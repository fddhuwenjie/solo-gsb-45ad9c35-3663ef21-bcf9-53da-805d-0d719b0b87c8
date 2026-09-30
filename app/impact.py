"""删除影响预演（dry-run，不修改任何状态）。

给定当前删除状态与用户勾选的「拟删除」存活条款（父条款按现有规则连同
后代纳入拟删除集），对比删除**前后**两套结果：

1. 引用绑定（复用 references 的扫描 / 展开）：删除前仍健康（ok）的引用，
   其目标在删除后消失 → 「引用失效」；删除前已异常（无法解析 / 目标已
   删除等）的引用不重复报告。
2. 定义术语绑定（复用 terms.extract_bindings）：删除前唯一绑定（ok）的
   使用，删除后绑定不到唯一定义 → 「术语失去唯一定义」（变为未定义或
   歧义）；改绑到另一个唯一定义 → 「改绑其他定义」。

再沿**反向引用边**（引用边 + 指向被删唯一定义的术语边）求受影响条款的
最短原因链：
- 多源 BFS，每个条款节点等权，路径长度即原因链层数；
- 等长路径按**文档顺序**决出唯一链（根与邻接均按组内最早文档位置排序）；
- 循环引用环（同一强连通分量 SCC）合并为一个影响项展示；
- 同一受影响条款（或循环组）只列一次，直连变化附在该条目上。
"""
from __future__ import annotations

from collections import deque

from .parser import Clause
from .references import cascade_deleted, expand_range, _scan
from .terms import extract_bindings, scope_label


# ---------------------------------------------------------------- 引用扫描

def _scan_refs(clauses: list[Clause], deleted_set: set[str]):
    """扫描存活条款中的引用并按当前删除状态绑定。

    返回 {cid: [(index, kind, raw, targets, missing), ...]}；
    无法解析的引用不进入结果。
    """
    path_to_id: dict[tuple[int, ...], str] = {}
    for c in clauses:
        path_to_id.setdefault(c.path, c.id)

    out: dict[str, list[tuple[int, str, object, list[str], list]]] = {}
    for c in clauses:
        if c.id in deleted_set:
            continue
        binds = []
        for i, r in enumerate(_scan(c.text)):
            if r.kind == "single":
                t = path_to_id.get(r.a)
                binds.append((i, r.kind, r, [t] if t else [],
                              [] if t else [r.a]))
            elif r.kind == "range":
                ids, missing = expand_range(r.a, r.b, path_to_id)
                binds.append((i, r.kind, r, ids, missing))
        out[c.id] = binds
    return out


# ---------------------------------------------------------------- 强连通分量

def _tarjan(nodes: list[str], edges: dict[str, set[str]]) -> list[list[str]]:
    """Tarjan 强连通分量（条款量级，递归足够）。"""
    import sys
    sys.setrecursionlimit(max(10000, sys.getrecursionlimit()))

    index: dict[str, int] = {}
    low: dict[str, int] = {}
    stack: list[str] = []
    on_stack: set[str] = set()
    counter = 0
    comps: list[list[str]] = []

    def strong(v: str) -> None:
        nonlocal counter
        index[v] = low[v] = counter
        counter += 1
        stack.append(v)
        on_stack.add(v)
        for w in edges.get(v, ()):
            if w not in index:
                strong(w)
                low[v] = min(low[v], low[w])
            elif w in on_stack:
                low[v] = min(low[v], index[w])
        if low[v] == index[v]:
            comp = []
            while True:
                w = stack.pop()
                on_stack.discard(w)
                comp.append(w)
                if w == v:
                    break
            comps.append(comp)

    for n in nodes:
        if n not in index:
            strong(n)
    return comps


# ---------------------------------------------------------------- 主入口

def preview_delete(clauses: list[Clause], preamble: str,
                   current_deleted: list[str], selected: list[str]) -> dict:
    """删除影响预演（纯计算，不修改调用方数据）。

    绑定是否失效只取决于条款身份与删除集合，与同父兄弟间的排序无关
    （重编号文本的变化在确认后由 /api/analyze 统一刷新），故不需要 order。
    """
    by_id = {c.id: c for c in clauses}
    known = set(by_id)
    doc_order = {c.id: i for i, c in enumerate(clauses)}

    cur_set = cascade_deleted(clauses, [c for c in current_deleted if c in known])
    picked_set = {c for c in selected if c in known and c not in cur_set}
    new_set = cascade_deleted(clauses, list(cur_set | picked_set))
    gone = new_set - cur_set                      # 本次拟删除（含级联后代）
    survivor_ids = known - new_set

    def info(cid: str) -> dict:
        c = by_id[cid]
        return {"id": c.id, "label": c.label, "heading": c.heading}

    changes: dict[str, list[dict]] = {}           # 存活条款 -> 直连变化

    def add_change(cid: str, ch: dict) -> None:
        changes.setdefault(cid, []).append(ch)

    # 反向边（跨组传播用）：被依赖条款 -> 依赖它的存活条款。
    # 元素 (src_id, dst_id, reason)，含义「src 因 reason 依赖 dst」。
    rev_edges: list[tuple[str, str, str]] = []

    # ------------------------------------------------------------ 引用对比
    scanned = _scan_refs(clauses, cur_set)
    for cid in sorted(survivor_ids, key=lambda x: doc_order[x]):
        for _i, kind, r, targets, missing in scanned.get(cid, []):
            lost = [t for t in targets if t in gone]
            if not lost:
                # 目标仍存活：传播边（区间的每个存活目标都建边）
                for t in targets:
                    if t in survivor_ids and t != cid:
                        rev_edges.append((cid, t, f"引用{by_id[t].label}"))
                continue
            # 删除前必须完全健康：无缺失路径、无当前已删除目标；否则不重复报告
            if missing or any(t in cur_set for t in targets):
                # 即便不报告，仍需保留其存活目标的传播边
                for t in targets:
                    if t in survivor_ids and t != cid:
                        rev_edges.append((cid, t, f"引用{by_id[t].label}"))
                continue
            if kind == "single":
                t = lost[0]
                add_change(cid, {
                    "kind": "ref_broken",
                    "ref_text": r.text,
                    "target_id": t,
                    "target_label": by_id[t].label,
                    "target_heading": by_id[t].heading,
                    "start": r.start, "end": r.end,
                    "message": f"引用{r.text}的目标{by_id[t].label}将被删除",
                })
                rev_edges.append((cid, t, f"引用{by_id[t].label}"))
            else:
                gone_labels = "、".join(by_id[t].label for t in lost)
                t0 = lost[0]
                add_change(cid, {
                    "kind": "ref_broken",
                    "ref_text": r.text,
                    "target_id": t0,
                    "target_label": by_id[t0].label,
                    "target_heading": by_id[t0].heading,
                    "start": r.start, "end": r.end,
                    "message": f"区间引用{r.text}中的{gone_labels}将被删除",
                })
                for t in lost:
                    rev_edges.append((cid, t, f"区间引用{by_id[t].label}"))
                for t in targets:
                    if t in survivor_ids and t != cid:
                        rev_edges.append((cid, t, f"引用{by_id[t].label}"))

    # 存活条款之间的正向引用边（SCC 用）
    fwd_edges: dict[str, set[str]] = {cid: set() for cid in survivor_ids}
    for src, dst, _r in rev_edges:
        if src in survivor_ids and dst in survivor_ids and src != dst:
            fwd_edges[src].add(dst)

    # ------------------------------------------------------------ 术语对比
    before_t = extract_bindings(preamble, clauses, cur_set)
    after_t = extract_bindings(preamble, clauses, new_set)
    after_use = {u.id: u for u in after_t["uses"]}

    for u in before_t["uses"]:
        if u.clause_id is None or u.clause_id not in survivor_ids:
            continue                                # 前置说明不列入条款影响
        if u.status != "ok" or len(u.def_ids) != 1:
            continue                                # 删除前已非唯一绑定，不报告
        d = before_t["def_by_id"][u.def_ids[0]]
        if d.clause_id is None or d.clause_id not in gone:
            continue
        name = u.name
        old_scope = scope_label(d.scope_path)
        shown = f"“{name}”" if u.quoted else f"术语“{name}”"
        reason = f"依赖{by_id[d.clause_id].label}对「{name}」的定义"
        u2 = after_use.get(u.id)

        if u2 is not None and u2.status == "ok" and len(u2.def_ids) == 1:
            d2 = after_t["def_by_id"][u2.def_ids[0]]
            new_scope = scope_label(d2.scope_path)
            add_change(u.clause_id, {
                "kind": "term_rebind",
                "name": name,
                "old_def_id": d.id,
                "old_clause_id": d.clause_id,
                "old_label": d.label,
                "old_scope_label": old_scope,
                "new_def_id": d2.id,
                "new_clause_id": d2.clause_id,
                "new_label": d2.label,
                "new_scope_label": new_scope,
                "start": u.start, "end": u.end,
                "message": (
                    f"{shown}将改绑到{new_scope}定义（{d2.label}）："
                    f"原绑定的{old_scope}定义（{d.label}）将被删除"
                ),
            })
        else:
            after_status = u2.status if u2 is not None else "undefined"
            detail = ("删除后同作用域存在多个同名定义，绑定存在歧义"
                      if after_status == "ambiguous"
                      else "删除后将无任何可见定义（未定义）")
            add_change(u.clause_id, {
                "kind": "term_lost",
                "name": name,
                "old_def_id": d.id,
                "old_clause_id": d.clause_id,
                "old_label": d.label,
                "old_scope_label": old_scope,
                "after_status": after_status,
                "start": u.start, "end": u.end,
                "message": (
                    f"{shown}将失去唯一定义：原绑定的{old_scope}定义"
                    f"（{d.label}）将被删除，{detail}"
                ),
            })
        rev_edges.append((u.clause_id, d.clause_id, reason))

    # ------------------------------------------------------------ SCC 合并
    survivor_list = [c.id for c in clauses if c.id in survivor_ids]
    comps = _tarjan(survivor_list, fwd_edges)

    groups: list[list[str]] = []
    group_of: dict[str, int] = {}
    cyclic_groups: set[int] = set()
    for comp in comps:
        gid = len(groups)
        members = sorted(comp, key=lambda x: doc_order[x])
        groups.append(members)
        for m in members:
            group_of[m] = gid
        if len(members) > 1:
            cyclic_groups.add(gid)
    root_groups: set[int] = set()
    for g in sorted(gone, key=lambda x: doc_order[x]):
        gid = len(groups)
        groups.append([g])
        group_of[g] = gid
        root_groups.add(gid)

    def grp_doc(gid: int) -> int:
        return min(doc_order[m] for m in groups[gid])

    # 组间反向邻接（去重；同一对组保留文档顺序最先出现的原因文案）
    rev_group: dict[int, dict[int, str]] = {}
    for src, dst, reason in rev_edges:
        gs, gd = group_of.get(src), group_of.get(dst)
        if gs is None or gd is None or gs == gd:
            continue
        rev_group.setdefault(gd, {}).setdefault(gs, reason)

    # ------------------------------------------------------------ 多源 BFS
    # 根（拟删除组）按文档顺序入队；父指针记录每个组沿最短链回溯到的父组。
    # 父指针同时覆盖根组与存活组，便于从循环组等节点完整还原「…→根」链条。
    parent_of: dict[int, tuple[int, str]] = {}
    queue: deque[int] = deque(sorted(root_groups, key=grp_doc))
    reached: set[int] = set(queue)
    while queue:
        cur = queue.popleft()
        neighbors = rev_group.get(cur, {})
        for ng in sorted(neighbors, key=grp_doc):
            if ng in reached:
                continue
            reached.add(ng)
            parent_of[ng] = (cur, neighbors[ng])
            queue.append(ng)

    # ------------------------------------------------------------ 组装结果
    def serialize_node(gid: int) -> dict:
        return {
            "group": [info(m) for m in groups[gid]],
            "cyclic": gid in cyclic_groups,
            "deleted": gid in root_groups,
        }

    entries: list[dict] = []
    for gid in sorted(
            (g for g in parent_of if g not in root_groups), key=grp_doc):
        members = groups[gid]
        cyclic = gid in cyclic_groups

        # 还原最短原因链：本条款/本组 → … → 拟删除条款（根）
        chain_nodes = [serialize_node(gid)]
        chain_edges: list[str] = []
        cur = gid
        guard = {gid}
        while cur in parent_of:
            pgr, label = parent_of[cur]
            chain_edges.append(label)
            chain_nodes.append(serialize_node(pgr))
            if pgr in guard:
                break
            guard.add(pgr)
            cur = pgr

        # 该组成员上的直连变化（循环组合并其全部成员）
        direct: list[dict] = []
        order_key = {"ref_broken": 0, "term_lost": 1, "term_rebind": 2}
        for m in members:
            for ch in changes.get(m, []):
                d = dict(ch)
                d["clause_id"] = m
                d["clause_label"] = by_id[m].label
                direct.append(d)
        direct.sort(key=lambda d: (doc_order[d["clause_id"]],
                                   order_key.get(d["kind"], 9),
                                   d.get("start", 0)))

        entries.append({
            "cyclic": cyclic,
            "members": [info(m) for m in members],
            "clause_id": None if cyclic else members[0],
            "label": None if cyclic else by_id[members[0]].label,
            "heading": None if cyclic else by_id[members[0]].heading,
            "transitive_only": not direct,
            "changes": direct,
            "chain_nodes": chain_nodes,
            "chain_edges": chain_edges,
        })

    new_deleted = [
        dict(info(c.id), picked=c.id in picked_set)
        for c in clauses if c.id in gone
    ]
    picked_out = [info(c.id) for c in clauses if c.id in picked_set]

    counts = {
        "new_deleted": len(gone),
        "cascaded": len(gone) - len(picked_set),
        "affected_clauses": sum(len(e["members"]) for e in entries),
        "affected_entries": len(entries),
        "ref_broken": sum(1 for e in entries for ch in e["changes"]
                          if ch["kind"] == "ref_broken"),
        "term_lost": sum(1 for e in entries for ch in e["changes"]
                         if ch["kind"] == "term_lost"),
        "term_rebind": sum(1 for e in entries for ch in e["changes"]
                           if ch["kind"] == "term_rebind"),
        "cyclic_groups": sum(1 for e in entries if e["cyclic"]),
    }

    return {
        "selected": picked_out,
        "new_deleted": new_deleted,
        "entries": entries,
        "counts": counts,
    }
