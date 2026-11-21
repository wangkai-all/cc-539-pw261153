/*
 * dfa.js — 确定性有限状态机的表示与算法
 *
 * 模型约定（与题目一致）：
 *  - 状态 0 为起始状态；
 *  - 每个操作符号在每个状态下有且仅有一个后继（完整转移表）；
 *  - 显式拒绝汇点 sink：非接受状态，且每个符号都自环；
 *  - 合成时“转移缺失”统一落入该汇点。
 */
(function (root, factory) {
  const mod = factory();
  if (typeof module !== 'undefined' && module.exports) module.exports = mod;
  else root.DFA = mod;
})(typeof self !== 'undefined' ? self : this, function () {
  'use strict';

  /**
   * 沿 word 逐步求值。
   * 返回完整轨迹，供页面单步演示使用。
   */
  function evaluate(dfa, word) {
    const path = [];
    let state = dfa.start;
    for (const sym of word) {
      if (!dfa.alphabet.includes(sym)) {
        throw new Error('符号不在操作字母表中: ' + sym);
      }
      const next = dfa.trans[sym][state];
      path.push({ state, symbol: sym, next });
      state = next;
    }
    return {
      finalState: state,
      accepted: dfa.accept[state],
      path,
      inSink: state === dfa.sink,
    };
  }

  function reachableStates(dfa) {
    const seen = new Set([dfa.start]);
    const queue = [dfa.start];
    while (queue.length) {
      const q = queue.shift();
      for (const a of dfa.alphabet) {
        const t = dfa.trans[a][q];
        if (!seen.has(t)) { seen.add(t); queue.push(t); }
      }
    }
    return seen;
  }

  /**
   * 划分求精最小化（仅保留可达状态），再以 BFS 发现顺序重编号，
   * 得到与具体状态编号无关的规范形式。语言相同的 DFA 规范形式一致。
   */
  function minimize(dfa) {
    const reach = reachableStates(dfa);
    const states = [...reach].sort((x, y) => x - y);
    let cls = new Map();
    for (const q of states) cls.set(q, dfa.accept[q] ? 1 : 0);
    const alpha = dfa.alphabet;
    let changed = true;
    while (changed) {
      changed = false;
      const sig = new Map();
      const nextCls = new Map();
      let nextId = 0;
      for (const q of states) {
        const key = [cls.get(q)]
          .concat(alpha.map(a => cls.get(dfa.trans[a][q])))
          .join(',');
        let id = sig.get(key);
        if (id === undefined) { id = nextId++; sig.set(key, id); }
        nextCls.set(q, id);
      }
      for (const q of states) {
        if (nextCls.get(q) !== cls.get(q)) { changed = true; break; }
      }
      cls = nextCls;
    }
    // BFS 从起始块开始规范编号
    const startCls = cls.get(dfa.start);
    const remap = new Map([[startCls, 0]]);
    const order = [startCls];
    let head = 0;
    while (head < order.length) {
      const c = order[head++];
      const member = states.find(q => cls.get(q) === c);
      for (const a of alpha) {
        const tc = cls.get(dfa.trans[a][member]);
        if (!remap.has(tc)) { remap.set(tc, remap.size); order.push(tc); }
      }
    }
    const k = remap.size;
    const accept = new Array(k).fill(false);
    const trans = {};
    for (const a of alpha) trans[a] = new Array(k).fill(0);
    for (const q of states) {
      const nq = remap.get(cls.get(q));
      accept[nq] = dfa.accept[q];
      for (const a of alpha) trans[a][nq] = remap.get(cls.get(dfa.trans[a][q]));
    }
    return { alphabet: alpha.slice(), start: 0, n: k, accept, trans };
  }

  /** 规范签名：最小 DFA 的结构字符串，语言相同则签名相同。 */
  function signature(dfa) {
    const m = minimize(dfa);
    const parts = [];
    parts.push('acc=' + m.accept.map(Number).join(''));
    for (const a of m.alphabet) parts.push(a + ':' + m.trans[a].join(','));
    return parts.join('|');
  }

  function sameLanguage(d1, d2) {
    return signature(d1) === signature(d2);
  }

  /**
   * 乘积状态图 BFS：从 (start1, start2) 出发，
   * 找最短的、两台 DFA 接受结论不同的序列；语言相同时返回 null。
   */
  function distinguishingWord(d1, d2) {
    const alpha = d1.alphabet;
    const start = d1.start + ',' + d2.start;
    const parent = new Map([[start, null]]); // node -> {prev, symbol}
    const queue = [start];
    while (queue.length) {
      const node = queue.shift();
      const [q1s, q2s] = node.split(',');
      const q1 = Number(q1s), q2 = Number(q2s);
      if (d1.accept[q1] !== d2.accept[q2]) {
        const word = [];
        let cur = node;
        while (parent.get(cur)) {
          word.push(parent.get(cur).symbol);
          cur = parent.get(cur).prev;
        }
        word.reverse();
        return word;
      }
      for (const a of alpha) {
        const n1 = d1.trans[a][q1];
        const n2 = d2.trans[a][q2];
        const nxt = n1 + ',' + n2;
        if (!parent.has(nxt)) {
          parent.set(nxt, { prev: node, symbol: a });
          queue.push(nxt);
        }
      }
    }
    return null;
  }

  /** 找显式拒绝汇点（非接受且所有符号自环）；找不到返回 -1。 */
  function findSink(dfa) {
    for (let q = 0; q < dfa.n; q++) {
      if (dfa.accept[q]) continue;
      let selfLoop = true;
      for (const a of dfa.alphabet) {
        if (dfa.trans[a][q] !== q) { selfLoop = false; break; }
      }
      if (selfLoop) return q;
    }
    return -1;
  }

  return {
    evaluate,
    reachableStates,
    minimize,
    signature,
    sameLanguage,
    distinguishingWord,
    findSink,
  };
});
