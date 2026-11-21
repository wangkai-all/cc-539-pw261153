/*
 * app.js — 页面交互：样本录入、求解调度、结果渲染、候选比较、单步演示。
 * 所有推断结论都明确标注为“模型推断”，不冒充设备验证。
 */
(function () {
  'use strict';

  const $ = id => document.getElementById(id);
  const EPS = 'ε';

  /* ---------------- 预设 ---------------- */
  const a = n => 'a'.repeat(n).split('');
  const PRESETS = [
    {
      name: '重复前缀（偶数个 ab）',
      alphabet: 'a, b',
      pos: ['ab', 'ab ab', 'ab ab ab'],
      neg: [EPS, 'a', 'ab a', 'ab ab a'],
    },
    {
      name: '空序列是正例（偶数个 x）',
      alphabet: 'x, y',
      pos: [EPS, 'x x', 'x y x'],
      neg: ['x', 'y', 'x x y'],
    },
    {
      name: '矛盾标注（同序列正+反）',
      alphabet: 'a, b',
      pos: ['a b', EPS],
      neg: ['a b', 'b'],
    },
    {
      name: '样本不足（多种解释可分歧）',
      alphabet: 'a, b',
      pos: ['a'],
      neg: [EPS],
    },
    {
      name: '超出 6 状态上限（一元鸽链）',
      alphabet: 'a',
      pos: [0, 1, 2, 3, 4, 5].map(n => 'a'.repeat(n) || EPS),
      neg: [6, 7, 8, 9, 10, 11, 12].map(n => 'a'.repeat(n)),
    },
  ];

  /* ---------------- 解析 ---------------- */
  function parseAlphabet(raw) {
    return raw.split(/[\s,，、;；]+/).map(s => s.trim()).filter(Boolean);
  }

  // 每行一条；空行 / 仅 ε => 空序列。忽略文本末尾因换行产生的多余空行，
  // 连续空行合并为一条 ε，避免重复空样本。
  function parseSamples(raw) {
    const lines = raw.split('\n');
    const out = [];
    let pendingEmpty = false;
    for (const line of lines) {
      const t = line.trim();
      if (t === '' || t === EPS) {
        pendingEmpty = true;
        continue;
      }
      if (pendingEmpty) { out.push([]); pendingEmpty = false; }
      out.push(t.split(/\s+/).filter(Boolean));
    }
    if (pendingEmpty && raw.trim() !== '') out.push([]);
    return out;
  }

  function wordText(word) {
    return word.length === 0 ? EPS : word.join(' ');
  }

  /* ---------------- SVG 状态图 ---------------- */
  function renderGraph(dfa, currentState) {
    const reach = DFA.reachableStates(dfa);
    const n = dfa.n;
    const R = 26;
    const gapX = 150;
    const width = Math.max(320, n * gapX + 40);
    const cy = 120;
    const pos = q => ({ x: 30 + q * gapX + R, y: cy });
    const parts = [];

    // 起始箭头
    parts.push(`<line class="start-arrow" x1="0" y1="${cy}" x2="${pos(0).x - R - 4}" y2="${cy}" marker-end="url(#arrow)"/>`);

    // 边：按 (from,to) 聚合标签，自环单独画
    const edgeMap = new Map();
    for (const sym of dfa.alphabet) {
      for (let q = 0; q < n; q++) {
        const t = dfa.trans[sym][q];
        const key = q + '>' + t;
        if (!edgeMap.has(key)) edgeMap.set(key, []);
        edgeMap.get(key).push(sym);
      }
    }
    const curEdges = new Set();
    for (const sym of dfa.alphabet) {
      for (let q = 0; q < n; q++) {
        if (q === currentState) curEdges.add(q + '>' + dfa.trans[sym][q]);
      }
    }

    for (const [key, syms] of edgeMap) {
      const [from, to] = key.split('>').map(Number);
      const cls = curEdges.has(key) ? 'edge edge-current' : 'edge';
      if (from === to) {
        const p = pos(from);
        const lx = p.x, ly = p.y - R - 26;
        parts.push(`<path class="${cls}" d="M ${p.x - 12} ${p.y - R + 4}
          C ${p.x - 34} ${p.y - R - 30}, ${p.x + 34} ${p.y - R - 30}, ${p.x + 12} ${p.y - R + 4}"
          marker-end="url(#arrow)"/>`);
        parts.push(`<text class="edge-label" x="${lx}" y="${ly}" text-anchor="middle">${syms.join(',')}</text>`);
      } else {
        const p1 = pos(from), p2 = pos(to);
        const dir = p2.x > p1.x ? 1 : -1;
        const x1 = p1.x + dir * R, x2 = p2.x - dir * R;
        const bend = syms.length ? 0 : 0;
        const my = cy - 14 - bend;
        parts.push(`<path class="${cls}" d="M ${x1} ${cy} Q ${(x1 + x2) / 2} ${my}, ${x2} ${cy}" marker-end="url(#arrow)"/>`);
        parts.push(`<text class="edge-label" x="${(x1 + x2) / 2}" y="${my - 6}" text-anchor="middle">${syms.join(',')}</text>`);
      }
    }

    // 节点
    for (let q = 0; q < n; q++) {
      const p = pos(q);
      const isAccept = dfa.accept[q];
      const isSink = q === dfa.sink;
      const isCurrent = q === currentState;
      const cls = 'node-circle' +
        (isAccept ? ' node-accept' : '') +
        (isSink ? ' node-sink' : '') +
        (isCurrent ? ' node-current' : '');
      parts.push(`<circle class="${cls}" cx="${p.x}" cy="${p.y}" r="${R}"/>`);
      if (isAccept) parts.push(`<circle class="${cls}" cx="${p.x}" cy="${p.y}" r="${R - 5}"/>`);
      const label = isSink ? `q${q}·汇点` : `q${q}`;
      parts.push(`<text x="${p.x}" y="${p.y + 4}" text-anchor="middle">${label}</text>`);
      if (!reach.has(q)) {
        parts.push(`<text x="${p.x}" y="${p.y + R + 16}" text-anchor="middle" style="fill:var(--warn);font-size:10px">不可达</text>`);
      }
    }

    return `<div class="graph-wrap"><svg class="graph" width="${width}" height="220" viewBox="0 0 ${width} 220">
      <defs><marker id="arrow" markerWidth="9" markerHeight="9" refX="8" refY="3" orient="auto" markerUnits="strokeWidth">
        <path d="M0,0 L8,3 L0,6 z" fill="#6b7ea3"/></marker></defs>
      ${parts.join('\n')}
    </svg></div>`;
  }

  function renderTransTable(dfa) {
    let html = '<table><thead><tr><th>状态</th>';
    for (const sym of dfa.alphabet) html += `<th>--${sym}--&gt;</th>`;
    html += '<th>接受?</th></tr></thead><tbody>';
    for (let q = 0; q < dfa.n; q++) {
      const rowCls = q === 0 ? 'start-row' : '';
      html += `<tr class="${rowCls}"><td>${q === dfa.sink ? `q${q}（汇点）` : 'q' + q}${q === 0 ? ' 起点' : ''}</td>`;
      for (const sym of dfa.alphabet) html += `<td>q${dfa.trans[sym][q]}</td>`;
      html += `<td class="${dfa.accept[q] ? 'accept-cell-yes' : 'accept-cell-no'}">${dfa.accept[q] ? '接受' : '拒绝'}</td></tr>`;
    }
    return html + '</tbody></table>';
  }

  function renderSizeLog(statuses) {
    const label = { sat: '可满足', unsat: '无解', timeout: '超时' };
    return '<div class="size-log">' + statuses.map(s =>
      `<span class="size-chip ${s.status}">${s.n} 状态 · ${label[s.status]}</span>`).join('') + '</div>';
  }

  /* ---------------- 状态 ---------------- */
  let lastResult = null;
  let stepState = null;

  /* ---------------- 求解 ---------------- */
  function onSolve() {
    hideAllPanels();
    const alphabet = parseAlphabet($('alphabet').value);
    const positives = parseSamples($('positives').value);
    const negatives = parseSamples($('negatives').value);
    const maxStates = Math.max(1, parseInt($('maxStates').value, 10) || 6);
    const timeLimit = Math.max(1, parseInt($('timeLimit').value, 10) || 8000);

    const r = Synth.synthesize(alphabet, positives, negatives, { maxStates, timeLimitMs: timeLimit });
    lastResult = r;
    $('inputError').classList.add('hidden');

    if (r.kind === 'invalid') {
      showError(r.reason);
      return;
    }
    if (r.kind === 'conflict') return renderConflict(r);
    if (r.kind === 'unsat') return renderUnsat(r);
    if (r.kind === 'noModelTimeout') return renderNoModelTimeout(r);
    renderModel(r);
  }

  function hideAllPanels() {
    ['modelPanel', 'comparePanel', 'unsatPanel', 'conflictPanel', 'stepperPanel', 'statusBanner']
      .forEach(id => $(id).classList.add('hidden'));
  }

  function showError(msg) {
    const el = $('inputError');
    el.textContent = '输入错误：' + msg;
    el.classList.remove('hidden');
  }

  function banner(cls, big, detailHtml) {
    const el = $('statusBanner');
    el.className = 'card banner ' + cls;
    el.innerHTML = `<div class="big">${big}</div>${detailHtml ? `<p>${detailHtml}</p>` : ''}`;
    el.classList.remove('hidden');
  }

  function renderConflict(r) {
    banner('err', '发现标注冲突', '同一序列同时被标成正例和反例，请先消除冲突再求解。');
    $('conflictBody').innerHTML = '<p>冲突样本：</p><div class="core-list">' +
      r.conflicts.map(w => `<div class="core-item"><span class="conflict-item">${wordText(w)}</span>
        <span><span class="pill pos">正例</span> <span class="pill neg">反例</span></span></div>`).join('') +
      '</div>';
    $('conflictPanel').classList.remove('hidden');
  }

  function renderUnsat(r) {
    banner('err', `在 ${r.maxStates} 状态上限内找不到一致模型`,
      '以下样本在<b>当前状态上限与拒绝汇点约定</b>下无法同时满足。这<b>不</b>意味着任意规模都无解——放宽上限可能出现模型。');
    const items = r.core.map(s =>
      `<div class="core-item"><span>${wordText(s.word)}</span>
       <span class="pill ${s.label === '+' ? 'pos' : 'neg'}">${s.label === '+' ? '正例' : '反例'}</span></div>`).join('');
    $('unsatBody').innerHTML =
      `<p class="hint">最小冲突核心（删除其中任一条后，剩余样本在该上限内可满足）。核心提取状态：${r.coreComplete ? '已完成，结论确定' : '中途超时，当前为部分核心'}</p>
       <div class="core-list">${items}</div>`;
    $('unsatPanel').classList.remove('hidden');
  }

  function renderNoModelTimeout(r) {
    banner('warn', '搜索超时：尚未找到模型，也未证明无解',
      '已保留各规模的搜索记录。<b>超时不能当成不存在模型</b>，可增大时间预算或状态上限后重试。');
    $('modelPanel').classList.remove('hidden');
    $('modelMeta').innerHTML = '';
    $('sizeLog').innerHTML = renderSizeLog(r.sizeStatuses);
    $('graph').innerHTML = '';
    $('transTable').innerHTML = '';
    $('sinkNote').textContent = '';
  }

  function renderModel(r) {
    const dfa = r.dfa;
    const minimality = r.minimal
      ? '<span class="pill pos">最小性已证明</span>'
      : '<span class="pill info">最小性未证明</span>';
    const detail = r.minimal
      ? `状态数 ${r.nStates}（含拒绝汇点）；从 1 到 ${r.nStates - 1} 的所有更小规模都已被证明无解。`
      : `状态数 ${r.nStates}（含拒绝汇点）；部分更小规模在预算内超时，因此<b>不能</b>断言这是最小模型。`;
    banner('ok', '找到与全部样本一致的确定性状态机', detail + ' 最小性仅针对本模型约定。');
    $('modelMeta').innerHTML =
      `<div class="row" style="margin:4px 0">${minimality}
        <span class="pill info">起始 q0</span>
        <span class="pill neg">拒绝汇点 q${dfa.sink}</span>
       </div>`;
    $('sizeLog').innerHTML = renderSizeLog(r.sizeStatuses);
    $('graph').innerHTML = renderGraph(dfa, null);
    $('transTable').innerHTML = renderTransTable(dfa);
    $('sinkNote').textContent =
      '注：任何未定义的转移都进入拒绝汇点 q' + dfa.sink + '；汇点非接受且所有操作自环。不可达 / 等价状态造成的编号差异不构成新解释。';
    $('modelPanel').classList.remove('hidden');

    renderComparison(r);
    initStepper(dfa);
    $('stepperPanel').classList.remove('hidden');
  }

  function renderComparison(r) {
    const c = r.comparison;
    const panel = $('comparePanel');
    if (!c) { panel.classList.add('hidden'); return; }
    panel.classList.remove('hidden');

    if (c.status === 'distinct') {
      const w = c.word;
      const wt = wordText(w);
      $('compareBody').innerHTML =
        `<p>找到两份在至少一条序列上接受结论<b>不同</b>的候选（已排除仅状态编号、不可达或等价状态造成的结构差异）。
          乘积状态图 BFS 得到最短分歧序列：</p>
         <div class="diverge-box">
           <div class="word mono">${wt}</div>
           <div class="row" style="margin-top:8px">
             <span class="pill ${c.verdicts[0] === '+' ? 'pos' : 'neg'}">候选 A：${c.verdicts[0] === '+' ? '接受' : '拒绝'}</span>
             <span class="pill ${c.verdicts[1] === '+' ? 'pos' : 'neg'}">候选 B：${c.verdicts[1] === '+' ? '接受' : '拒绝'}</span>
           </div>
           <div class="diverge-actions">
             <button class="mini" data-add="pos">把该序列标为正例并补入</button>
             <button class="mini" data-add="neg">把该序列标为反例并补入</button>
             <button class="mini" data-step="1">载入单步演示</button>
           </div>
         </div>
         <div class="compare-grid" style="margin-top:14px">
           <div class="compare-col"><h4>候选 A（当前模型）</h4>${renderGraph(c.dfa1, null)}</div>
           <div class="compare-col"><h4>候选 B（语言不同）</h4>${renderGraph(c.dfa2, null)}</div>
         </div>
         <p class="hint">补标后重新求解，两份解释中将有一份被样本排除。</p>`;
      panel.querySelectorAll('button[data-add]').forEach(btn => {
        btn.addEventListener('click', () => {
          const target = btn.dataset.add === 'pos' ? $('positives') : $('negatives');
          const line = w.length === 0 ? EPS : w.join(' ');
          target.value = target.value.replace(/\s+$/, '') + '\n' + line;
          onSolve();
        });
      });
      const stepBtn = panel.querySelector('button[data-step]');
      stepBtn.addEventListener('click', () => {
        $('stepInput').value = wt === EPS ? '' : wt;
        initStepper(lastResult.dfa);
      });
    } else if (c.status === 'exhausted') {
      $('compareBody').innerHTML =
        `<p><span class="pill pos">区分搜索已证明结束</span></p>
         <p class="hint">在本状态规模下枚举了全部满足样本的赋值（共 ${c.enumerated} 份其它候选），
         它们规范化后语言完全相同，因此<b>不存在</b>可产生分歧的序列。要获得更强的模型，需要补充新样本。</p>`;
    } else {
      $('compareBody').innerHTML =
        `<p><span class="pill info">区分搜索超时</span></p>
         <p class="hint">已检查 ${c.enumerated} 份候选，时间预算耗尽；尚不能证明是否存在语言不同的解释，也不能断言没有分歧串。</p>`;
    }
  }

  /* ---------------- 单步演示 ---------------- */
  function initStepper(dfa) {
    stepState = { dfa, word: [], index: 0 };
    const raw = $('stepInput').value.trim();
    stepState.word = (raw === '' || raw === EPS) ? [] : raw.split(/\s+/).filter(Boolean);
    // 校验符号
    const bad = stepState.word.find(sym => !dfa.alphabet.includes(sym));
    if (bad) {
      $('stepVerdict').innerHTML = `<div class="verdict reject"><span class="label">符号 “${bad}” 不在字母表中</span></div>`;
      $('stepTrace').innerHTML = '';
      $('stepGraph').innerHTML = renderGraph(dfa, dfa.start);
      $('stepPos').textContent = '';
      return;
    }
    stepState.index = 0;
    renderStep();
  }

  function renderStep() {
    const { dfa, word, index } = stepState;
    // 当前所在状态：按前缀求值
    let q = dfa.start;
    for (let i = 0; i < index; i++) q = dfa.trans[word[i]][q];
    $('stepGraph').innerHTML = renderGraph(dfa, q);
    $('stepPos').textContent = `第 ${index} / ${word.length} 步 · 当前 q${q}`;

    // 轨迹表
    let html = '<table class="trace-table"><thead><tr><th>#</th><th>操作</th><th>迁移前</th><th>迁移后</th></tr></thead><tbody>';
    html += `<tr><td>0</td><td class="sym">（起点）</td><td>—</td><td>q0</td></tr>`;
    let cur = dfa.start;
    for (let i = 0; i < word.length; i++) {
      const nxt = dfa.trans[word[i]][cur];
      const done = i < index;
      html += `<tr style="${done ? '' : 'opacity:.45'}"><td>${i + 1}</td><td class="sym">${word[i]}</td><td>q${cur}</td><td>q${nxt}</td></tr>`;
      cur = nxt;
    }
    $('stepTrace').innerHTML = html + '</tbody></table>';

    const finished = index === word.length;
    if (finished) {
      const accepted = dfa.accept[q];
      const inSink = q === dfa.sink;
      $('stepVerdict').innerHTML =
        `<div class="verdict ${accepted ? 'accept' : 'reject'}">
           <span class="label">模型推断：该序列被${accepted ? '接受 ✓' : '拒绝 ✗'}</span>
           <small>终点 q${q}${inSink ? '（拒绝汇点：曾触发缺失转移）' : ''}；此结论仅来自推断模型，未在真实设备上验证。序列：${wordText(word)}</small>
         </div>`;
    } else {
      const nxt = dfa.trans[word[index]][q];
      $('stepVerdict').innerHTML =
        `<div class="verdict reject" style="background:var(--panel-2);border-color:var(--border)">
           <span class="label" style="color:var(--text)">下一步：--${word[index]}--&gt; q${nxt}</span>
           <small>走到序列末尾后才给出接受 / 拒绝的模型推断。</small></div>`;
    }
  }

  /* ---------------- 事件绑定 ---------------- */
  function fillPreset(p) {
    $('alphabet').value = p.alphabet;
    $('positives').value = p.pos.join('\n');
    $('negatives').value = p.neg.join('\n');
  }

  function init() {
    const row = $('presetRow');
    PRESETS.forEach((p, i) => {
      const b = document.createElement('button');
      b.textContent = (i + 1) + '. ' + p.name;
      b.addEventListener('click', () => { fillPreset(p); onSolve(); });
      row.appendChild(b);
    });

    $('solveBtn').addEventListener('click', onSolve);
    $('addEmptyPos').addEventListener('click', () => {
      $('positives').value = $('positives').value.replace(/\s+$/, '') + '\n' + EPS;
    });
    $('addEmptyNeg').addEventListener('click', () => {
      $('negatives').value = $('negatives').value.replace(/\s+$/, '') + '\n' + EPS;
    });

    $('stepLoad').addEventListener('click', () => {
      if (lastResult && lastResult.kind === 'ok') initStepper(lastResult.dfa);
    });
    $('stepNext').addEventListener('click', () => {
      if (!stepState || stepState.index >= stepState.word.length) return;
      stepState.index++; renderStep();
    });
    $('stepBack').addEventListener('click', () => {
      if (!stepState || stepState.index === 0) return;
      stepState.index--; renderStep();
    });
    $('stepReset').addEventListener('click', () => {
      if (!stepState) return;
      stepState.index = 0; renderStep();
    });

    // 默认载入第一个示例并求解
    fillPreset(PRESETS[0]);
    onSolve();
  }

  document.addEventListener('DOMContentLoaded', init);
})();
