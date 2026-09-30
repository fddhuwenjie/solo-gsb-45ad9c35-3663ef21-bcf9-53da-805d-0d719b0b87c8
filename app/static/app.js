/* 条款引用重排台 —— 前端逻辑（原生 JS） */
"use strict";

const $ = (sel) => document.querySelector(sel);

const els = {
  input: $("#contract-input"),
  btnParse: $("#btn-parse"),
  btnExample: $("#btn-example"),
  btnSave: $("#btn-save"),
  draftSelect: $("#draft-select"),
  status: $("#parse-status"),
  workspace: $("#workspace"),
  sortable: $("#sortable"),
  tray: $("#tray"),
  trayList: $("#tray-list"),
  issuesBar: $("#issues-bar"),
  before: $("#before-view"),
  after: $("#after-view"),
  toast: $("#toast"),
  tabRefs: $("#tab-refs"),
  tabTerms: $("#tab-terms"),
  paneRefs: $("#pane-refs"),
  paneTerms: $("#pane-terms"),
  termIssues: $("#term-issues"),
  termDefs: $("#term-defs"),
  termIgnored: $("#term-ignored"),
  termIgnoredList: $("#term-ignored-list"),
  termsView: $("#terms-view"),
  // 删除影响预演
  btnDeletePreview: $("#btn-delete-preview"),
  dpPanel: $("#delete-preview-panel"),
  dpSelectedList: $("#dp-selected-list"),
  btnDpRun: $("#btn-dp-run"),
  btnDpCancel: $("#btn-dp-cancel"),
  dpResult: $("#dp-result"),
  dpStale: $("#dp-stale"),
  dpSummary: $("#dp-summary"),
  dpDeletedList: $("#dp-deleted-list"),
  dpEntries: $("#dp-entries"),
  btnDpConfirm: $("#btn-dp-confirm"),
  btnDpClose: $("#btn-dp-close"),
};

// 运行时状态
const state = {
  text: "",
  order: [],        // 存活条款 id 的先序（深度优先）扁平序列
  deleted: [],      // 已删除条款 id（含级联删除的后代）
  data: null,       // 最近一次 /api/analyze 响应
  clauseMap: new Map(),
  currentDraftId: null,
  lastParsedText: null,
  dragCid: null,    // 拖动中的条款 id（整棵子树随之移动）
  mode: "refs",     // refs | terms
  terms: null,      // 最近一次 /api/terms 响应
  termIgnores: [],  // 已忽略的术语问题 occ_id（随草稿保存）
  // 删除影响预演
  previewMode: false,   // 是否处于勾选/预览态（预览态禁用拖动与直接删除）
  previewPicked: [],    // 勾选的存活条款 id
  previewData: null,    // 最近一次 /api/delete-preview 响应
  previewSig: null,     // 生成预览结果时的草稿指纹
  previewBusy: false,
};

const LS_KEY = "clause-rebench-session";

// ---------------------------------------------------------------- 工具

function toast(msg) {
  els.toast.textContent = msg;
  els.toast.classList.remove("hidden");
  clearTimeout(toast._t);
  toast._t = setTimeout(() => els.toast.classList.add("hidden"), 2200);
}

function esc(s) {
  return s.replace(/[&<>"]/g, (c) =>
    ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;" }[c]));
}

function debounce(fn, ms) {
  let t;
  return (...args) => {
    clearTimeout(t);
    t = setTimeout(() => fn(...args), ms);
  };
}

async function api(path, options = {}) {
  const res = await fetch(path, {
    headers: { "Content-Type": "application/json" },
    ...options,
  });
  if (!res.ok) {
    let detail = res.statusText;
    try { detail = (await res.json()).detail || detail; } catch (_) {}
    throw new Error(detail);
  }
  return res.json();
}

// ---------------------------------------------------------------- 层级树

// state.order 是树的先序扁平序列；以下工具按后端返回的 path 还原父子树，
// 排序只允许发生在同一父级的兄弟之间，移动节点时整棵子树一起移动。

function buildTree() {
  const root = { path: [], key: "", children: new Map(), clauseIds: [] };
  const at = new Map([["", root]]);
  state.data.clauses.forEach((c) => {
    let node = root;
    (c.path || []).forEach((seg, depth) => {
      const pref = c.path.slice(0, depth + 1);
      const key = pref.join(".");
      let nxt = at.get(key);
      if (!nxt) {
        nxt = { path: pref, key, children: new Map(), clauseIds: [] };
        at.set(key, nxt);
        node.children.set(key, nxt);
      }
      node = nxt;
    });
    if (!node.clauseIds.includes(c.id)) node.clauseIds.push(c.id);
  });
  return { root, at };
}

function isDeletedId(cid) {
  return state.deleted.includes(cid);
}

function nodeAlive(node) {
  if (node.clauseIds.some((id) => !isDeletedId(id))) return true;
  for (const ch of node.children.values()) {
    if (nodeAlive(ch)) return true;
  }
  return false;
}

// state.order 始终是「合法树先序」（后端会规整，本地 moveSibling 只做同层
// 整子树移动）。布局完全由「原始路径深度 + 当前先序」推得，与原编号数值无关：
// 用深度栈跟踪父级，节点（含原文未单列的虚祖先）在其父级的兄弟序列中首次
// 出现时取下一个连续编号。
function computeLayout() {
  const { root, at } = buildTree();
  const newPathByKey = new Map([["", []]]);
  const seqByKey = new Map();   // 原 key -> 直接子节点原 key 的新次序
  const stack = [];             // { key, depth }

  const ensureNode = (op, depth) => {
    const key = op.slice(0, depth).join(".");
    if (newPathByKey.has(key)) return;
    const parentKey = depth === 1 ? "" : op.slice(0, depth - 1).join(".");
    if (depth > 1 && !newPathByKey.has(parentKey)) ensureNode(op, depth - 1);
    let seq = seqByKey.get(parentKey);
    if (!seq) { seq = []; seqByKey.set(parentKey, seq); }
    if (!seq.includes(key)) seq.push(key);
    const parentPath = newPathByKey.get(parentKey);
    newPathByKey.set(key, parentPath.concat(seq.indexOf(key) + 1));
  };

  for (const cid of state.order) {
    const c = state.clauseMap.get(cid);
    const op = c ? (c.path || []) : [];
    while (stack.length && stack[stack.length - 1].depth >= op.length) stack.pop();
    for (let d = 1; d <= op.length; d++) ensureNode(op, d);
    stack.push({ key: op.join("."), depth: op.length });
  }

  const kidsByKey = new Map();
  for (const [key, seq] of seqByKey) {
    kidsByKey.set(key, seq.map((k) => at.get(k)).filter(Boolean).filter(nodeAlive));
  }
  for (const key of newPathByKey.keys()) {
    if (!kidsByKey.has(key)) kidsByKey.set(key, []);
  }
  return { newPathByKey, kidsByKey, root };
}

// 条款当前的「新路径」。优先用本地布局（拖动后、后端响应回来前也准确），
// 布局尚不可用时回退到后端 new_label / 原始 path。
function newPathOf(cid) {
  try {
    const c = state.clauseMap.get(cid);
    if (!c) return [];
    const { newPathByKey } = computeLayout();
    // 找到该条款所属节点（其原始路径对应的 key）
    const op = c.path || [];
    for (let d = op.length; d >= 1; d--) {
      const key = op.slice(0, d).join(".");
      if (newPathByKey.has(key)) return newPathByKey.get(key);
    }
  } catch (_) { /* 布局未就绪 */ }
  const c = state.clauseMap.get(cid);
  return c && c.new_label
    ? c.new_label.slice(1, -1).split(".").map(Number)
    : (c ? (c.path || []) : []);
}

// 按「新路径」前缀求子树区段（用于本地换序，后端尚未返回前）
function subtreeSpanByNewPath(path) {
  let start = -1;
  let end = state.order.length;
  state.order.forEach((cid, i) => {
    const p = newPathOf(cid);
    const under = p.length >= path.length
      && path.every((s, k) => s === p[k]);
    if (under) {
      if (start === -1) start = i;
      end = i + 1;
    }
  });
  return [start, end];
}

// ---------------------------------------------------------------- 分析

async function runAnalyze(structureChanged = false) {
  state.text = els.input.value;
  if (!state.text.trim()) {
    els.workspace.classList.add("hidden");
    state.lastParsedText = null;
    if (state.previewMode) exitPreviewMode();
    return;
  }
  try {
    const data = await api("/api/analyze", {
      method: "POST",
      body: JSON.stringify({
        text: state.text,
        order: state.order,
        deleted: state.deleted,
      }),
    });
    state.data = data;
    // 以后端规整结果为准：顺序、删除集合（含级联后代）前后端保持一致
    state.order = data.order;
    state.deleted = data.deleted_clauses.map((d) => d.id);
    state.clauseMap = new Map(data.clauses.map((c) => [c.id, c]));
    if (structureChanged) renderSortable();
    renderAll();
    els.workspace.classList.remove("hidden");
    state.lastParsedText = state.text;
    saveSession();
    fetchTerms();
    // 预演态下任何分析返回都可能使勾选/旧结果失效：清理失效勾选并标记陈旧
    if (state.previewMode) {
      const alive = new Set(state.order);
      state.previewPicked = state.previewPicked.filter((id) => alive.has(id));
      renderSortable();
      renderDpSelection();
      if (state.previewData) markDpStale();
    }
  } catch (e) {
    els.status.textContent = "分析失败：" + e.message;
  }
}

const scheduleAnalyze = debounce(() => runAnalyze(false), 200);

// ---------------------------------------------------------------- 可排序（层级）列表

function renderSortable() {
  els.sortable.innerHTML = "";
  const { root, kidsByKey: kids, newPathByKey: newPaths } = computeLayout();

  const labelOf = (path) => path.length ? "第" + path.join(".") + "条" : "";

  const renderNode = (node, depth) => {
    // 节点自身的真实条款卡片（重复路径时只有首张可拖动）
    const own = node.clauseIds.filter((id) => !isDeletedId(id));
    if (own.length) {
      own.forEach((cid, dupIdx) => {
        els.sortable.appendChild(
          makeCard(cid, depth, dupIdx === 0, labelOf(newPaths.get(node.key))));
      });
    } else if (depth > 0) {
      // 原文未单列的虚父节点：展示占位，仅在顶层允许作为同层落点
      const newP = newPaths.get(node.key);
      els.sortable.appendChild(makeVirtualRow(node, depth, labelOf(newP), newP.join(".")));
    }
    // 子节点按新兄弟顺序递归渲染（整棵子树连续显示）
    (kids.get(node.key) || []).forEach((ch) => renderNode(ch, depth + 1));
  };
  renderNode(root, 0);

  // 删除托盘（预演态禁止直接恢复，避免改动删除状态）
  if (state.deleted.length) {
    els.tray.classList.remove("hidden");
    els.trayList.innerHTML = "";
    state.deleted.forEach((cid) => {
      const c = state.clauseMap.get(cid);
      if (!c) return;
      const chip = document.createElement("span");
      chip.className = "tray-item" + (state.previewMode ? " disabled" : "");
      chip.textContent = `${c.label} ＋`;
      chip.title = state.previewMode
        ? "删除影响预演进行中，不能恢复条款"
        : "点击恢复「" + c.label + "」（连同其后代）";
      if (!state.previewMode) {
        chip.addEventListener("click", () => restoreClause(cid));
      }
      els.trayList.appendChild(chip);
    });
  } else {
    els.tray.classList.add("hidden");
  }
}

function makeCard(cid, depth, draggable, liveLabel) {
  const c = state.clauseMap.get(cid);
  const li = document.createElement("li");
  li.className = "clause-card" + (state.previewMode ? " previewing" : "");
  li.draggable = draggable && !state.previewMode;
  li.dataset.cid = cid;
  li.style.paddingLeft = (12 + depth * 22) + "px";

  const checkHtml = state.previewMode
    ? `<input type="checkbox" class="dp-check" title="勾选后纳入拟删除集（父条款含全部后代）"${
        state.previewPicked.includes(cid) ? " checked" : ""} />`
    : "";

  li.innerHTML = `
    ${checkHtml}
    <span class="drag-handle" title="${draggable && !state.previewMode ? "拖动排序（仅同一父级内）" : state.previewMode ? "删除影响预演进行中，暂不可拖动" : "重复编号，不可拖动"}">⠿</span>
    <span class="new-badge">${esc(liveLabel || c.new_label || "—")}</span>
    <span class="old-label">${esc(c.label)}</span>
    <span class="card-heading">${esc(c.heading || "（无正文）")}</span>
    <span class="card-actions">
      <button type="button" class="btn-danger-mini" title="${state.previewMode ? "删除影响预演进行中，请使用下方勾选" : "删除该条款（含全部子条款）"}">✕</button>
    </span>`;

  const btnDel = li.querySelector(".btn-danger-mini");
  if (state.previewMode) {
    btnDel.disabled = true;
    btnDel.classList.add("disabled");
    const box = li.querySelector(".dp-check");
    box.addEventListener("click", (e) => e.stopPropagation());
    box.addEventListener("change", () => {
      if (box.checked) {
        if (!state.previewPicked.includes(cid)) state.previewPicked.push(cid);
      } else {
        state.previewPicked = state.previewPicked.filter((x) => x !== cid);
      }
      renderDpSelection();
      // 勾选集变化后，旧结果对应的拟删除集也已过时
      if (state.previewData) markDpStale();
    });
  } else {
    btnDel.addEventListener("click", (e) => {
      e.stopPropagation();
      deleteClause(cid);
    });
  }

  if (draggable && !state.previewMode) {
    li.addEventListener("dragstart", (e) => {
      state.dragCid = cid;
      li.classList.add("dragging");
      e.dataTransfer.effectAllowed = "move";
      try { e.dataTransfer.setData("text/plain", cid); } catch (_) {}
    });
    li.addEventListener("dragend", () => {
      state.dragCid = null;
      li.classList.remove("dragging");
      document.querySelectorAll(".drag-over,.drag-denied")
        .forEach((n) => n.classList.remove("drag-over", "drag-denied"));
    });
    attachDropZone(li, cid);
  }
  return li;
}

function makeVirtualRow(node, depth, newLabel, newKey) {
  const li = document.createElement("li");
  li.className = "clause-card virtual";
  li.dataset.vkey = newKey;
  li.style.paddingLeft = (12 + depth * 22) + "px";
  li.innerHTML = `
    <span class="drag-handle virtual-handle">•</span>
    <span class="new-badge virtual-badge">${esc(newLabel)}</span>
    <span class="virtual-hint">（原文未单列，仅含子条款）</span>`;
  // 虚节点只在顶层作为「同层兄弟」的落点（如 4.1/4.2 与第5条之间调整顺序）
  if (depth === 1 && !state.previewMode) attachDropZone(li, null, newKey);
  return li;
}

// 同层兄弟换序：把 srcCid 整棵子树移动到目标子树之前/之后（虚节点则插到
// 其整组子树之前）。返回 true 表示发生了移动；同父级校验不通过返回 false。
// 注意：state.order 是最近一次后端返回的规范先序，一切定位都基于「新路径」。
function moveSibling(srcCid, targetCid, { before = false, virtualKey = null } = {}) {
  const srcPath = newPathOf(srcCid);
  let dstPath;
  if (targetCid) {
    dstPath = newPathOf(targetCid);
  } else {
    dstPath = virtualKey == null || virtualKey === ""
      ? [] : virtualKey.split(".").map(Number);
  }
  const srcParent = srcPath.slice(0, -1);
  const dstParent = dstPath.slice(0, -1);
  if (srcParent.length !== dstParent.length
      || !srcParent.every((s, k) => s === dstParent[k])) {
    return false;
  }

  const [srcStart, srcEnd] = subtreeSpanByNewPath(srcPath);
  const [dstStart] = subtreeSpanByNewPath(dstPath);
  if (targetCid && srcStart === dstStart) return true;

  const block = state.order.slice(srcStart, srcEnd);
  const rest = state.order.slice(0, srcStart)
    .concat(state.order.slice(srcEnd));
  let anchor;
  if (targetCid) {
    anchor = rest.indexOf(targetCid);
    if (anchor === -1) return false; // 拖入自身子树内部
    if (!before) anchor += 1;
  } else {
    // 虚节点：始终插到其整组存活子条款之前。删除源区段后，虚组起点
    // 只可能因「源在其之前」而后移，减去源区段长度即可。
    anchor = srcStart < dstStart
      ? dstStart - (srcEnd - srcStart)
      : dstStart;
  }
  const nextOrder = rest.slice(0, anchor).concat(block, rest.slice(anchor));
  if (nextOrder.every((id, i) => id === state.order[i])
      && nextOrder.length === state.order.length) {
    return true; // 位置无变化
  }
  state.order = nextOrder;
  return true;
}

// 落点处理：只接受同一父级下的兄弟；before=true 插到目标子树之前
function attachDropZone(li, targetCid, virtualKey = null) {
  li.addEventListener("dragover", (e) => {
    const srcId = state.dragCid;
    if (!srcId) return;
    const srcParent = newPathOf(srcId).slice(0, -1);
    let dstParent;
    if (targetCid) {
      dstParent = newPathOf(targetCid).slice(0, -1);
    } else {
      dstParent = virtualKey === "" ? [] : virtualKey.split(".").map(Number);
    }
    const sameParent = srcParent.length === dstParent.length
      && srcParent.every((s, k) => s === dstParent[k]);
    e.preventDefault();
    e.dataTransfer.dropEffect = sameParent ? "move" : "none";
    li.classList.toggle("drag-denied", !sameParent);
    li.classList.toggle("drag-over", sameParent);
  });
  li.addEventListener("dragleave", () =>
    li.classList.remove("drag-over", "drag-denied"));
  li.addEventListener("drop", (e) => {
    e.preventDefault();
    li.classList.remove("drag-over", "drag-denied");
    const srcId = state.dragCid;
    state.dragCid = null;
    if (!srcId) return;
    if (targetCid && srcId === targetCid) return;

    const before = targetCid ? e.offsetY < li.offsetHeight / 2 : true;
    const ok = moveSibling(srcId, targetCid,
      { before, virtualKey: targetCid ? null : virtualKey });
    if (!ok) {
      toast("只能在同一父级下调整顺序（子条款会随父条款整棵移动）");
      return;
    }
    scheduleAnalyze();
  });
}

function deleteClause(cid) {
  // 连同整棵子树一起删除
  const c = state.clauseMap.get(cid);
  const pref = c.path || [];
  state.order = state.order.filter((x) => {
    const p = state.clauseMap.get(x).path || [];
    return !(p.length >= pref.length && pref.every((s, k) => s === p[k]));
  });
  state.data.clauses.forEach((x) => {
    const p = x.path || [];
    if (p.length >= pref.length && pref.every((s, k) => s === p[k])
        && !state.deleted.includes(x.id)) {
      state.deleted.push(x.id);
    }
  });
  runAnalyze();
}

function restoreClause(cid) {
  // 恢复父条款时一并恢复其全部后代；顺序按解析顺序回到同级原位
  const c = state.clauseMap.get(cid);
  const pref = c.path || [];
  state.data.clauses.forEach((x) => {
    const p = x.path || [];
    if (p.length >= pref.length && pref.every((s, k) => s === p[k])) {
      state.deleted = state.deleted.filter((d) => d !== x.id);
    }
  });
  // 交给后端按解析顺序把恢复的子树归位
  runAnalyze();
}

// ---------------------------------------------------------------- 删除影响预演

// 预演结果依赖的指纹：正文 / 排序 / 删除状态 / 勾选集任一变化即失效
function draftSignature() {
  return JSON.stringify({
    t: els.input.value,
    o: state.order,
    d: [...state.deleted].sort(),
    p: [...state.previewPicked].sort(),
  });
}

function enterPreviewMode() {
  if (!state.data || !state.order.length) {
    toast("请先粘贴并解析合同文本");
    return;
  }
  state.previewMode = true;
  state.previewPicked = [];
  state.previewData = null;
  state.previewSig = null;
  els.dpPanel.classList.remove("hidden");
  els.dpResult.classList.add("hidden");
  els.dpStale.classList.add("hidden");
  els.btnDeletePreview.disabled = true;
  renderSortable();
  renderDpSelection();
  els.dpPanel.scrollIntoView({ behavior: "smooth", block: "start" });
}

function exitPreviewMode() {
  state.previewMode = false;
  state.previewPicked = [];
  state.previewData = null;
  state.previewSig = null;
  state.previewBusy = false;
  els.dpPanel.classList.add("hidden");
  els.dpResult.classList.add("hidden");
  els.dpStale.classList.add("hidden");
  els.btnDeletePreview.disabled = false;
  renderSortable();
}

function renderDpSelection() {
  const picked = state.previewPicked
    .map((cid) => state.clauseMap.get(cid))
    .filter(Boolean);
  if (!picked.length) {
    els.dpSelectedList.textContent = "尚未勾选（在上方条款卡片左侧勾选）";
    els.dpSelectedList.classList.add("empty");
  } else {
    els.dpSelectedList.classList.remove("empty");
    els.dpSelectedList.textContent = picked
      .map((c) => `${c.label} ${c.heading || ""}`.trim()).join("　");
  }
  els.btnDpRun.disabled = state.previewBusy || !picked.length;
  els.btnDpRun.textContent = state.previewBusy ? "分析中…" : "预览影响";
}

async function runDeletePreview() {
  if (!state.previewPicked.length) {
    toast("请先勾选拟删除的条款");
    return;
  }
  state.previewBusy = true;
  renderDpSelection();
  try {
    const data = await api("/api/delete-preview", {
      method: "POST",
      body: JSON.stringify({
        text: els.input.value,
        order: state.order,
        deleted: state.deleted,
        selected: state.previewPicked,
      }),
    });
    state.previewData = data;
    state.previewSig = draftSignature();
    renderDpResult();
  } catch (e) {
    // 分析失败不得改变草稿：提示并退出预演态（恢复可拖动 / 可删除）
    toast("影响分析失败，草稿未改动：" + e.message);
    exitPreviewMode();
  } finally {
    state.previewBusy = false;
    renderDpSelection();
  }
}

const DP_CHANGE_META = {
  ref_broken: { tag: "引用失效", cls: "ref" },
  term_lost: { tag: "术语失去唯一定义", cls: "term-lost" },
  term_rebind: { tag: "术语改绑", cls: "term-rebind" },
};

function renderDpResult() {
  const d = state.previewData;
  if (!d) return;
  els.dpResult.classList.remove("hidden");
  markDpStale();

  const c = d.counts;
  els.dpSummary.innerHTML =
    `<span class="dp-stat stat-delete">拟删除 <b>${c.new_deleted}</b> 条` +
    (c.cascaded ? `（其中级联后代 ${c.cascaded} 条）` : "") + `</span>` +
    `<span class="dp-stat stat-affect">仍存活受影响条款 <b>${c.affected_clauses}</b> 条` +
    (c.cyclic_groups ? `（含 ${c.cyclic_groups} 个循环链合并项）` : "") + `</span>` +
    `<span class="dp-stat stat-ref">引用失效 <b>${c.ref_broken}</b></span>` +
    `<span class="dp-stat stat-term">术语失去唯一定义 <b>${c.term_lost}</b></span>` +
    `<span class="dp-stat stat-rebind">改绑其他定义 <b>${c.term_rebind}</b></span>`;

  // 拟删除清单
  els.dpDeletedList.innerHTML = "";
  if (d.new_deleted.length) {
    const wrap = document.createElement("div");
    wrap.className = "dp-deleted-wrap";
    wrap.innerHTML = `<span class="dp-deleted-label">拟删除集：</span>`;
    d.new_deleted.forEach((x) => {
      const chip = document.createElement("button");
      chip.type = "button";
      chip.className = "dp-del-chip" + (x.picked ? " picked" : " cascaded");
      chip.textContent = x.label + (x.picked ? "" : "（级联后代）");
      chip.title = (x.heading || "") + (x.picked ? "" : "：随父条款一并删除");
      chip.addEventListener("click", () => locate(x.id));
      wrap.appendChild(chip);
    });
    els.dpDeletedList.appendChild(wrap);
  }

  // 受影响条目
  els.dpEntries.innerHTML = "";
  if (!d.entries.length) {
    const ok = document.createElement("div");
    ok.className = "dp-ok";
    ok.textContent = "✓ 拟删除条款之外没有失效引用或术语绑定变化";
    els.dpEntries.appendChild(ok);
  } else {
    d.entries.forEach((e) => els.dpEntries.appendChild(makeDpEntry(e)));
  }
}

// 旧结果守卫：正文/排序/删除状态变化后不得直接确认
function markDpStale() {
  const stale = state.previewSig !== draftSignature();
  els.dpStale.classList.toggle("hidden", !stale);
  els.btnDpConfirm.disabled = stale || state.previewBusy;
  els.btnDpConfirm.title = stale ? "草稿已变化，请重新预览后再确认" : "";
}

function makeDpChain(e) {
  const chain = document.createElement("div");
  chain.className = "dp-chain";
  e.chain_nodes.forEach((node, i) => {
    if (i > 0) {
      const edge = document.createElement("span");
      edge.className = "dp-chain-edge";
      edge.textContent = "—" + (e.chain_edges[i - 1] || "依赖") + "→";
      chain.appendChild(edge);
    }
    if (node.cyclic) {
      const seg = document.createElement("span");
      seg.className = "dp-chain-node cyclic";
      seg.textContent = "循环链(" +
        node.group.map((m) => m.label).join(" ⇄ ") + ")";
      seg.title = "循环引用合并项，点击定位";
      seg.addEventListener("click", () =>
        locate(...node.group.map((m) => m.id)));
      chain.appendChild(seg);
    } else {
      const m = node.group[0];
      const seg = document.createElement("button");
      seg.type = "button";
      seg.className = "dp-chain-node" + (node.deleted ? " deleted" : "");
      seg.textContent = m.label;
      seg.title = (m.heading || "") + (node.deleted ? "（拟删除）" : "");
      if (!node.deleted) seg.addEventListener("click", () => locate(m.id));
      chain.appendChild(seg);
    }
  });
  return chain;
}

function makeDpEntry(e) {
  const row = document.createElement("div");
  row.className = "dp-entry" + (e.cyclic ? " cyclic" : "") +
    (e.transitive_only ? " transitive" : "");

  const head = document.createElement("div");
  head.className = "dp-entry-head";
  if (e.cyclic) {
    head.innerHTML =
      `<span class="dp-entry-tag tag-cycle">循环链合并</span>` +
      `<span class="dp-entry-title">${
        esc(e.members.map((m) => m.label).join(" ⇄ "))}</span>` +
      `<span class="dp-entry-sub">${
        esc(e.members.map((m) => m.heading).filter(Boolean).join(" / "))}</span>`;
    head.addEventListener("click", () => locate(...e.members.map((m) => m.id)));
  } else {
    const m = e.members[0];
    head.innerHTML =
      `<span class="dp-entry-tag ${e.transitive_only ? "tag-transitive" : "tag-direct"}">` +
      `${e.transitive_only ? "间接波及" : "直接受影响"}</span>` +
      `<span class="dp-entry-title">${esc(e.label)}</span>` +
      `<span class="dp-entry-sub">${esc(e.heading || "")}</span>`;
    head.addEventListener("click", () => locate(m.id));
  }
  row.appendChild(head);

  // 直连变化（去重：同一变化消息在循环组多成员上可能重复出现）
  const seenMsg = new Set();
  e.changes.forEach((ch) => {
    const meta = DP_CHANGE_META[ch.kind] || { tag: ch.kind, cls: "" };
    const key = ch.kind + "|" + ch.message;
    if (seenMsg.has(key)) return;
    seenMsg.add(key);
    const line = document.createElement("button");
    line.type = "button";
    line.className = `dp-change ${meta.cls}`;
    line.innerHTML =
      `<span class="dp-change-tag">${meta.tag}</span>` +
      `<span class="dp-change-msg">${esc(ch.message)}</span>` +
      (ch.clause_id ? `<span class="dp-change-where">@${esc(ch.clause_label)}</span>` : "");
    const target = ch.kind === "ref_broken"
      ? [ch.clause_id, ch.target_id]
      : [ch.clause_id, ch.old_clause_id].filter(Boolean);
    line.addEventListener("click", () => locate(...target));
    row.appendChild(line);
  });

  row.appendChild(makeDpChain(e));
  return row;
}

async function confirmDeletePreview() {
  if (!state.previewData) return;
  if (state.previewSig !== draftSignature()) {
    toast("草稿或勾选已变化，请重新预览后再确认");
    return;
  }
  // 一次性套用现有级联删除：拟删除集 = 后端预演算出的 new_deleted
  const gone = new Set(state.previewData.new_deleted.map((x) => x.id));
  const picked = state.previewData.new_deleted.map((x) => x.id);
  state.order = state.order.filter((cid) => !gone.has(cid));
  picked.forEach((cid) => {
    if (!state.deleted.includes(cid)) state.deleted.push(cid);
  });
  // 先退出预演态，再走与现有删除完全相同的分析/重排/术语刷新流程
  state.previewMode = false;
  state.previewPicked = [];
  state.previewData = null;
  state.previewSig = null;
  els.dpPanel.classList.add("hidden");
  els.dpResult.classList.add("hidden");
  els.btnDeletePreview.disabled = false;
  toast("已套用级联删除，正在重排与改写引用…");
  await runAnalyze(true);
}

// ---------------------------------------------------------------- 问题条

const ISSUE_META = {
  unparsable: { tag: "无法解析" },
  deleted: { tag: "目标已删除" },
  circular: { tag: "循环引用" },
};

function renderIssues() {
  const issues = state.data.issues;
  els.issuesBar.innerHTML = "";
  if (!issues.length) {
    const ok = document.createElement("div");
    ok.className = "issues-ok";
    ok.textContent = "✓ 所有引用均已成功绑定并重写";
    els.issuesBar.appendChild(ok);
    els.issuesBar.classList.remove("hidden");
    return;
  }
  issues.forEach((it) => {
    const chip = document.createElement("button");
    chip.type = "button";
    chip.className = `issue-chip ${it.type}`;
    const meta = ISSUE_META[it.type] || { tag: it.type };
    chip.innerHTML =
      `<span class="chip-tag">${meta.tag}</span>` +
      `<span class="chip-msg">${esc(it.message)}</span>`;
    chip.addEventListener("click", () => {
      locate(it.clause_id, it.target_id);
    });
    els.issuesBar.appendChild(chip);
  });
  els.issuesBar.classList.remove("hidden");
}

// ---------------------------------------------------------------- 对照视图

function makeMark(m, mode, ownerId) {
  const span = document.createElement("span");
  span.className = `mark ${m.status}`;
  span.textContent = mode === "before" ? m.text : m.new_text;
  const titles = {
    ok: "引用已按新层级顺序重写（点击定位目标条款）",
    unparsable: "无法解析或目标不存在（点击定位本条款）",
    deleted: "引用的目标条款已删除（点击查看目标）",
    circular: "循环引用：条款间相互指回（点击定位）",
  };
  span.title = titles[m.status] || "";
  span.addEventListener("click", (e) => {
    e.stopPropagation();
    locate(m.target_id || ownerId);
  });
  return span;
}

function appendBody(container, clause, mode) {
  const text = clause.before_text;
  const marks = clause.refs || [];
  let cursor = 0;
  marks.forEach((m) => {
    if (m.start > cursor) {
      container.appendChild(document.createTextNode(text.slice(cursor, m.start)));
    }
    container.appendChild(makeMark(m, mode, clause.id));
    cursor = m.end;
  });
  if (cursor < text.length) {
    container.appendChild(document.createTextNode(text.slice(cursor)));
  }
}

function makeBlock(clause, mode, isDeleted) {
  const block = document.createElement("div");
  block.className = "clause-block" + (isDeleted ? " deleted-clause" : "");
  block.dataset.cid = clause.id;
  // 用层级缩进体现父子树
  const depth = clause.depth != null ? clause.depth : (clause.path || []).length;
  block.style.paddingLeft = (12 + (depth - 1) * 18) + "px";

  const label = document.createElement("span");
  label.className = "block-label" + (mode === "after" ? " new" : "");
  label.textContent = mode === "after"
    ? (clause.new_label + " ")
    : (clause.label + " ");
  block.appendChild(label);

  if (isDeleted) {
    const ribbon = document.createElement("span");
    ribbon.className = "deleted-ribbon";
    ribbon.textContent = "已删除";
    block.appendChild(ribbon);
  }

  appendBody(block, clause, mode);
  return block;
}

function renderCompare() {
  const d = state.data;

  // 改动前：原解析顺序（含已删除条款，置灰）
  els.before.innerHTML = "";
  if (d.preamble) {
    const p = document.createElement("div");
    p.className = "preamble-block";
    p.textContent = d.preamble;
    els.before.appendChild(p);
  }
  d.clauses.forEach((c) => {
    els.before.appendChild(makeBlock(c, "before", d.deleted_clauses.some((x) => x.id === c.id)));
  });

  // 改动后：新顺序，只含存活条款
  els.after.innerHTML = "";
  if (d.preamble) {
    const p = document.createElement("div");
    p.className = "preamble-block";
    p.textContent = d.preamble;
    els.after.appendChild(p);
  }
  d.result.forEach((c) => els.after.appendChild(makeBlock(c, "after", false)));

  const c = d.counts;
  els.status.textContent =
    `共 ${d.clauses.length} 条，识别引用 ${d.total_refs} 处，已重写 ` +
    `${d.total_refs - c.unparsable - c.deleted - c.circular} 处` +
    (c.unparsable + c.deleted + c.circular
      ? `；异常 ${c.unparsable + c.deleted + c.circular} 处`
      : "，无异常");
}

function renderAll() {
  renderSortable();
  renderIssues();
  renderCompare();
}

// ---------------------------------------------------------------- 定位

function locate(...ids) {
  let scrolled = false;
  ids.filter(Boolean).forEach((cid) => {
    document.querySelectorAll(`.clause-block[data-cid="${CSS.escape(cid)}"]`)
      .forEach((node) => {
        if (!scrolled) {
          node.scrollIntoView({ behavior: "smooth", block: "center" });
          scrolled = true;
        }
        node.classList.remove("flash");
        void node.offsetWidth; // 重置动画
        node.classList.add("flash");
      });
    // 排序列表中的卡片也高亮
    const card = els.sortable.querySelector(`[data-cid="${CSS.escape(cid)}"]`);
    if (card) {
      card.classList.remove("flash");
      void card.offsetWidth;
      card.classList.add("flash");
    }
  });
}

// ---------------------------------------------------------------- 定义术语审校

async function fetchTerms() {
  if (!els.input.value.trim()) {
    state.terms = null;
    return;
  }
  try {
    state.terms = await api("/api/terms", {
      method: "POST",
      body: JSON.stringify({ text: els.input.value, deleted: state.deleted }),
    });
    // 清理已失效（正文中不再存在）的忽略项
    const live = new Set(state.terms.issues.map((it) => it.occ_id));
    state.termIgnores = state.termIgnores.filter((id) => live.has(id));
    if (state.mode === "terms") renderTerms();
  } catch (e) {
    state.terms = null;
  }
}

const TERM_ISSUE_META = {
  undefined: { tag: "未定义" },
  duplicate: { tag: "重复定义" },
  ambiguous: { tag: "歧义绑定" },
  unused: { tag: "未使用" },
};

function termBlockLabel(b) {
  return b.kind === "preamble" ? "前置说明" : (b.label || ("第" + b.path.join(".") + "条"));
}

function activeTermIssues() {
  const t = state.terms;
  if (!t) return [];
  return t.issues.filter((it) => !state.termIgnores.includes(it.occ_id));
}

function renderTermIssues() {
  const t = state.terms;
  els.termIssues.innerHTML = "";
  const issues = activeTermIssues();
  if (!issues.length) {
    const ok = document.createElement("div");
    ok.className = "term-ok";
    ok.textContent = "✓ 未发现术语问题" +
      (state.termIgnores.length ? `（已忽略 ${state.termIgnores.length} 项）` : "");
    els.termIssues.appendChild(ok);
  } else {
    issues.forEach((it) => {
      const b = t.blocks.find((x) => x.id === it.block_id);
      const where = b ? termBlockLabel(b) : "";
      const row = document.createElement("div");
      row.className = `term-issue-row ${it.type}`;
      row.innerHTML =
        `<span class="chip-tag">${TERM_ISSUE_META[it.type].tag}</span>` +
        `<span class="chip-body">` +
        `<span class="chip-msg">${esc(it.message)}</span>` +
        `<span class="chip-where">${esc(where)}</span></span>` +
        `<button type="button" class="chip-ignore" title="忽略该问题（随草稿保存）">忽略</button>`;
      row.addEventListener("click", () => locateTerm(it.occ_id));
      row.querySelector(".chip-ignore").addEventListener("click", (e) => {
        e.stopPropagation();
        ignoreTerm(it.occ_id);
      });
      els.termIssues.appendChild(row);
    });
  }

  // 已忽略区
  const ignored = t.issues.filter((it) => state.termIgnores.includes(it.occ_id));
  if (ignored.length) {
    els.termIgnored.classList.remove("hidden");
    els.termIgnoredList.innerHTML = "";
    ignored.forEach((it) => {
      const chip = document.createElement("span");
      chip.className = "tray-item";
      chip.textContent = `${TERM_ISSUE_META[it.type].tag}：${it.name} ↺`;
      chip.title = "点击恢复该问题";
      chip.addEventListener("click", () => unignoreTerm(it.occ_id));
      els.termIgnoredList.appendChild(chip);
    });
  } else {
    els.termIgnored.classList.add("hidden");
  }
}

function renderTermDefs() {
  const t = state.terms;
  els.termDefs.innerHTML = "";
  const defs = [...t.definitions].sort((a, b) =>
    a.name.localeCompare(b.name, "zh") || a.scope_label.localeCompare(b.scope_label));
  defs.forEach((d) => {
    const row = document.createElement("div");
    row.className = `term-def-row ${d.status}`;
    const statusText = d.status === "duplicate" ? "重复"
      : d.status === "unused" ? "未使用" : `使用 ${d.usage_count}`;
    row.innerHTML =
      `<span class="td-name">${esc(d.name)}</span>` +
      `<span class="td-scope">${esc(d.scope_label === "全文" ? "全文定义" : d.scope_label + " 局部")}</span>` +
      `<span class="td-meta">${statusText}</span>`;
    row.title = `点击定位定义处（${d.block_id === "preamble" ? "前置说明" : (d.label || "所在条款")}）`;
    row.addEventListener("click", () => locateTerm(d.id));
    els.termDefs.appendChild(row);
  });
}

function makeTermMark(block, m) {
  const span = document.createElement("span");
  span.className = `tmark ${m.kind} ${m.status}` + (state.termIgnores.includes(m.occ_id) ? " ignored" : "");
  span.textContent = block.text.slice(m.start, m.end);
  const titles = {
    def: `定义（${m.scope_label}）——点击定位其全部使用处`,
    "use-ok": `使用：绑定到${m.scope_label}定义 ——点击定位定义处`,
    "use-undefined": "未定义术语——点击定位本处",
    "use-ambiguous": "歧义绑定：同一作用域有多个同名定义",
  };
  span.title = titles[`${m.kind}-${m.status}`] || titles[m.kind] || "";
  span.dataset.occ = m.occ_id;
  span.addEventListener("click", (e) => {
    e.stopPropagation();
    locateTerm(m.occ_id);
  });
  return span;
}

function renderTermBlock(b) {
  const div = document.createElement("div");
  div.className = "term-block clause-block" +
    (b.kind === "preamble" ? " preamble-block" : "");
  div.dataset.bid = b.id;
  if (b.kind === "clause") {
    div.style.paddingLeft = (12 + Math.max(0, b.depth - 1) * 18) + "px";
    const label = document.createElement("span");
    label.className = "block-label";
    label.textContent = b.label + " ";
    div.appendChild(label);
  }
  let cursor = 0;
  (b.marks || []).forEach((m) => {
    if (m.start > cursor) div.appendChild(document.createTextNode(b.text.slice(cursor, m.start)));
    div.appendChild(makeTermMark(b, m));
    cursor = m.end;
  });
  if (cursor < b.text.length) div.appendChild(document.createTextNode(b.text.slice(cursor)));
  return div;
}

function renderTerms() {
  const t = state.terms;
  if (!t) return;
  renderTermIssues();
  renderTermDefs();
  els.termsView.innerHTML = "";
  t.blocks.forEach((b) => {
    if (!b.text.trim() && !(b.marks || []).length) return;
    els.termsView.appendChild(renderTermBlock(b));
  });
  const c = t.counts;
  const active = activeTermIssues().length;
  els.status.textContent =
    `术语审校：定义 ${t.total_definitions} 个，使用 ${t.total_usages} 处；` +
    (active ? `问题 ${active} 项（未定义 ${c.undefined} / 重复 ${c.duplicate} / 歧义 ${c.ambiguous} / 未使用 ${c.unused}）`
      : "未发现问题");
}

// 双向定位：定义 ↔ 其全部使用；歧义/未定义问题定位自身
function locateTerm(occId) {
  // 找到该 occ 的标记（定义或使用）
  const t = state.terms;
  let focus = null;
  const related = new Set([occId]);
  for (const b of t.blocks) {
    for (const m of b.marks || []) {
      if (m.occ_id === occId) {
        focus = m;
        (m.target_ids || []).forEach((id) => related.add(id));
      }
    }
  }
  // 若 occId 是使用，其 target_ids 已包含候选定义；再补上「指向该使用」的对端
  if (focus && focus.kind === "use") {
    for (const b of t.blocks) {
      for (const m of b.marks || []) {
        if (m.kind === "def" && (m.target_ids || []).includes(occId)) {
          related.add(m.occ_id);
        }
      }
    }
  }

  let scrolled = false;
  els.termsView.querySelectorAll(".tmark").forEach((node) => {
    const on = related.has(node.dataset.occ);
    node.classList.toggle("flash-pair", on);
    if (on && !scrolled) {
      node.scrollIntoView({ behavior: "smooth", block: "center" });
      scrolled = true;
    }
  });
  setTimeout(() => els.termsView.querySelectorAll(".tmark.flash-pair")
    .forEach((n) => n.classList.remove("flash-pair")), 2400);
}

function ignoreTerm(occId) {
  if (!state.termIgnores.includes(occId)) state.termIgnores.push(occId);
  saveSession();
  renderTerms();
  toast("已忽略该问题（保存草稿后随草稿保留）");
}

function unignoreTerm(occId) {
  state.termIgnores = state.termIgnores.filter((x) => x !== occId);
  saveSession();
  renderTerms();
}

async function switchMode(mode) {
  state.mode = mode;
  els.tabRefs.classList.toggle("active", mode === "refs");
  els.tabTerms.classList.toggle("active", mode === "terms");
  els.paneRefs.classList.toggle("hidden", mode !== "refs");
  els.paneTerms.classList.toggle("hidden", mode !== "terms");
  if (mode === "terms") {
    if (!state.terms) await fetchTerms();
    if (state.terms) renderTerms();
  }
}

// ---------------------------------------------------------------- 草稿（SQLite）
async function refreshDrafts(selectId) {
  try {
    const drafts = await api("/api/drafts");
    els.draftSelect.innerHTML =
      `<option value="">— 已保存草稿（${drafts.length}）—</option>` +
      drafts.map((d) =>
        `<option value="${d.id}">${esc(d.title)}</option>`).join("");
    if (selectId) els.draftSelect.value = String(selectId);
  } catch (_) { /* 后端不可用时静默 */ }
}

async function saveDraft() {
  const text = els.input.value;
  if (!text.trim()) {
    toast("请先粘贴并解析合同文本");
    return;
  }
  let title;
  if (state.currentDraftId) {
    const existing = [...els.draftSelect.options]
      .find((o) => o.value === String(state.currentDraftId));
    title = existing ? existing.textContent : prompt("草稿标题：");
    if (!title) return;
  } else {
    title = prompt("给草稿起个标题：", "合同草稿 " + new Date().toLocaleString());
    if (!title) return;
  }
  const payload = {
    title, content: text, order: state.order, deleted: state.deleted,
    term_ignores: state.termIgnores,
  };
  try {
    if (state.currentDraftId) {
      await api(`/api/drafts/${state.currentDraftId}`, {
        method: "PUT", body: JSON.stringify(payload),
      });
    } else {
      const r = await api("/api/drafts", {
        method: "POST", body: JSON.stringify(payload),
      });
      state.currentDraftId = r.id;
    }
    toast("草稿已保存");
    refreshDrafts(state.currentDraftId);
  } catch (e) {
    toast("保存失败：" + e.message);
  }
}

async function loadDraft(id) {
  if (state.previewMode) exitPreviewMode();
  const d = await api(`/api/drafts/${id}`);
  state.currentDraftId = d.id;
  els.input.value = d.content;
  state.order = d.order;
  state.deleted = d.deleted;
  state.termIgnores = d.term_ignores || [];
  await runAnalyze(true);
  toast(`已载入草稿：${d.title}`);
}

// ---------------------------------------------------------------- 本地会话（localStorage 自动暂存）

function saveSession() {
  try {
    localStorage.setItem(LS_KEY, JSON.stringify({
      text: els.input.value, order: state.order, deleted: state.deleted,
      term_ignores: state.termIgnores,
    }));
  } catch (_) {}
}

async function restoreSession() {
  let s;
  try { s = JSON.parse(localStorage.getItem(LS_KEY) || "null"); } catch (_) {}
  if (s && s.text) {
    els.input.value = s.text;
    state.order = s.order || [];
    state.deleted = s.deleted || [];
    state.termIgnores = s.term_ignores || [];
    await runAnalyze(true);
  }
}

// ---------------------------------------------------------------- 示例

const EXAMPLE = `鉴于甲方拟采购乙方的系统集成服务，双方经平等协商，就本合同项下条款达成如下约定：

第1条 定义
本合同下列用语具有如下含义：“服务”指乙方按照本合同约定向甲方提供的系统集成及运维支持。
“关联方”是指直接或间接控制甲方或乙方的主体。
本合同所称“工作日”为除法定节假日外的自然日。
第1.1条 术语来源
本合同术语以第1条解释为准，详见第1.1.1条的举例。
第1.1.1条 术语举例
本条所称“交付物”是指乙方按约提交的文档与系统；交付物应随验收移交。

第2条 服务内容
乙方应按照第1条的定义提供完整“服务”，并保证“最终用户”能够正常使用；
“最终用户”应配合乙方工作。服务范围详见第3条至第5条的约定，验收标准见第9条。
如第若干条所述之特殊情形发生，乙方有权顺延工期。

第3条 服务期限
本条所称“服务期”是指自合同生效之日起十二个月；服务期内乙方应持续履约，
每个“工作日”均须安排值班。违约责任适用第7条。
第3.1条 期限计算
服务期按自然日计算；起算日见第3条，续约见第3.2条。
第3.2条 续约安排
续约应提前三十日书面通知；计算方式同第3.1条。

第4条 费用与支付
本条所称“工作日”是指银行对公营业日；
合同总金额及支付安排由本条各款约定。

第4.1条 支付方式
甲方应在收到乙方付款申请后十五日内付款，付款币种为人民币。

第4.2条 发票
乙方应开具合规增值税发票；第4.1条至第4.2条共同构成支付条款。

第5条 验收
服务期届满前，甲方应在“工作日”内组织验收；逾期未提出异议的，视为验收合格。

第6条 保密
双方对在履约过程中知悉的商业秘密负有保密义务，违反保密义务的责任按第7条处理。

第7条 违约责任
任何一方违反本合同约定的，应承担违约责任；保密义务相关违约适用第6条，
且本条责任范围涵盖第5条至第7条项下的全部义务。
`;

function loadExample() {
  if (state.previewMode) exitPreviewMode();
  els.input.value = EXAMPLE;
  state.order = [];
  state.deleted = [];
  state.termIgnores = [];
  state.currentDraftId = null;
  els.draftSelect.value = "";
  runAnalyze(true).then(() => {
    toast("示例已载入：可点「🗑 删除影响预演」勾选第3条，预览引用失效、术语失效与循环链原因链");
  });
}

// ---------------------------------------------------------------- 事件绑定

els.btnParse.addEventListener("click", () => {
  // 重新解析：若文本变化则重置顺序；预演态随之退出（旧结果不得沿用）
  const structureChanged = state.lastParsedText !== els.input.value;
  if (structureChanged) {
    state.order = [];
    state.deleted = [];
    if (state.previewMode) exitPreviewMode();
  }
  runAnalyze(true);
});
els.btnExample.addEventListener("click", loadExample);
els.btnSave.addEventListener("click", saveDraft);
els.tabRefs.addEventListener("click", () => switchMode("refs"));
els.tabTerms.addEventListener("click", () => switchMode("terms"));
els.btnDeletePreview.addEventListener("click", enterPreviewMode);
els.btnDpRun.addEventListener("click", runDeletePreview);
els.btnDpCancel.addEventListener("click", exitPreviewMode);
els.btnDpClose.addEventListener("click", exitPreviewMode);
els.btnDpConfirm.addEventListener("click", () => {
  els.btnDpConfirm.disabled = true;
  confirmDeletePreview();
});
els.draftSelect.addEventListener("change", async (e) => {
  if (e.target.value) await loadDraft(Number(e.target.value));
});
els.input.addEventListener("input", debounce(saveSession, 500));
els.input.addEventListener("input", () => {
  if (state.previewMode && state.previewData) markDpStale();
});

// 启动
refreshDrafts();
restoreSession();
