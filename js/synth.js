/*
 * synth.js — 由正/反例样本合成 DFA
 *
 * 搜索策略（严格按题目约定）：
 *  1. 先检查同一序列同时被标成正例和反例的直接冲突；
 *  2. 状态数 n 从 1 递增到上限（演示默认 6，拒绝汇点占最后一个状态）；
 *  3. 每个 n 用 SAT 求解；UNSAT 才继续 n+1，超时不算 UNSAT；
 *  4. 找到模型后枚举同规模其他赋值，寻找语言不同的第二份候选，
 *     并在乘积图上求最短分歧序列；
 *  5. 全部规模都被证明 UNSAT 时，用删除法提取无法同时满足的样本核心。
 */
(function (root, factory) {
  const mod = factory(
    typeof require === 'function' ? require('./sat.js') : root.SAT,
    typeof require === 'function' ? require('./dfa.js') : root.DFA
  );
  if (typeof module !== 'undefined' && module.exports) module.exports = mod;
  else root.Synth = mod;
})(typeof self !== 'undefined' ? self : this, function (SAT, DFA) {
  'use strict';

  const { Solver } = SAT;
  function wordKey(word) { return word.join(''); }

  /** 同一序列被同时标成正例和反例 → 直接定位冲突样本。 */
  function findDirectConflicts(pos, neg) {
    const posMap = new Map();
    for (const w of pos) posMap.set(wordKey(w), w);
    const conflicts = [];
    for (const w of neg) {
      if (posMap.has(wordKey(w))) conflicts.push(w);
    }
    return conflicts;
  }

  /**
   * 规模为 n 的单热编码。
   * 变量：
   *   T[a][q][q']  q 为非汇点状态时符号 a 的唯一后继
   *   Acc[q]       非汇点状态是否接受（汇点恒为拒绝）
   *   P[s][i][q]   样本 s 走到第 i 个符号后处于状态 q
   */
  function buildCnf(alphabet, samples, n) {
    const sink = n - 1;

    const solver = new Solver();
    const newV = () => solver.newVar();
    // 字面量助手：变量 v 的正字面量为 2v，负字面量为 2v+1
    const pos = v => v * 2;
    const neg = v => v * 2 + 1;

    const T = {};
    for (const a of alphabet) {
      T[a] = [];
      for (let q = 0; q < n; q++) {
        if (q === sink) { T[a][q] = null; continue; }
        const row = [];
        for (let q2 = 0; q2 < n; q2++) row.push(newV());
        T[a][q] = row;
      }
    }
    const Acc = [];
    for (let q = 0; q < n; q++) Acc.push(q === sink ? null : newV());

    const P = samples.map(() => []);

    const add = c => { if (!solver.addClause(c)) throw new Error('root conflict'); };

    // 1) 每个非汇点状态、每个符号恰好一个后继
    for (const a of alphabet) {
      for (let q = 0; q < sink; q++) {
        const row = T[a][q];
        add(row.map(pos)); // 至少一个
        for (let i = 0; i < n; i++) {
          for (let j = i + 1; j < n; j++) {
            add([neg(row[i]), neg(row[j])]); // 至多一个
          }
        }
      }
    }

    // 2) 样本路径变量与约束
    samples.forEach((sample, s) => {
      const word = sample.word;
      const positions = [];
      for (let i = 0; i <= word.length; i++) {
        const row = [];
        for (let q = 0; q < n; q++) row.push(newV());
        positions.push(row);
      }
      P[s] = positions;

      // 起点固定为状态 0
      add([pos(positions[0][0])]);
      for (let q = 1; q < n; q++) add([neg(positions[0][q])]);

      for (let i = 0; i <= word.length; i++) {
        // 每个位置恰好处于一个状态
        add(positions[i].map(pos));
        for (let x = 0; x < n; x++) {
          for (let y = x + 1; y < n; y++) {
            add([neg(positions[i][x]), neg(positions[i][y])]);
          }
        }
      }

      for (let i = 0; i < word.length; i++) {
        const a = word[i];
        for (let q = 0; q < n; q++) {
          if (q === sink) {
            // 汇点所有符号自环
            add([neg(positions[i][sink]), pos(positions[i + 1][sink])]);
          } else {
            for (let q2 = 0; q2 < n; q2++) {
              // P(i,q) ∧ T[a][q][q2] ⇒ P(i+1,q2)
              add([
                neg(positions[i][q]),
                neg(T[a][q][q2]),
                pos(positions[i + 1][q2]),
              ]);
            }
          }
        }
      }

      const last = positions[word.length];
      if (sample.label === '+') {
        // 正例：终点不能在汇点；在哪个非汇点状态，哪个状态必须接受
        add([neg(last[sink])]);
        for (let q = 0; q < sink; q++) add([neg(last[q]), pos(Acc[q])]);
      } else {
        // 反例：终点在汇点天然拒绝；在非汇点状态则该状态必须不接受
        for (let q = 0; q < sink; q++) add([neg(last[q]), neg(Acc[q])]);
      }
    });

    return { solver, T, Acc, n, sink };
  }

  function modelToDfa(alphabet, cnf, model) {
    const { n, sink, T, Acc } = cnf;
    const accept = [];
    for (let q = 0; q < n; q++) accept.push(q === sink ? false : model[Acc[q]]);
    const trans = {};
    for (const a of alphabet) {
      trans[a] = [];
      for (let q = 0; q < n; q++) {
        if (q === sink) { trans[a][q] = sink; continue; }
        const row = T[a][q];
        let target = -1;
        for (let q2 = 0; q2 < n; q2++) if (model[row[q2]]) { target = q2; break; }
        if (target < 0) target = sink;
        trans[a][q] = target;
      }
    }
    return { alphabet: alphabet.slice(), start: 0, n, accept, trans, sink };
  }

  /** 阻塞子句：要求主变量（转移+接受）至少翻转一个，排除同一台具体 DFA。 */
  function blockingClause(cnf, model) {
    const { n, sink, T, Acc } = cnf;
    const lits = [];
    const flip = v => model[v] ? v * 2 + 1 : v * 2; // 翻转当前取值
    for (const a of Object.keys(T)) {
      for (let q = 0; q < n; q++) {
        if (q === sink) continue;
        for (let q2 = 0; q2 < n; q2++) {
          lits.push(flip(T[a][q][q2]));
        }
      }
    }
    for (let q = 0; q < n; q++) {
      if (q === sink) continue;
      lits.push(flip(Acc[q]));
    }
    return lits;
  }

  /**
   * 在已满足的规模上枚举第二份“语言不同”的候选。
   * 返回 { status, dfa1, dfa2?, word?, verdicts? }
   * status: 'distinct' | 'exhausted' | 'enumTimeout'
   */
  function enumerateAlternative(alphabet, samples, n, firstModel, firstDfa, deadline) {
    const cnf = buildCnf(alphabet, samples, n);
    const sig1 = DFA.signature(firstDfa);
    let model = firstModel;
    let enumerated = 0;
    while (true) {
      cnf.solver.addClause(blockingClause(cnf, model));
      const remain = deadline - Date.now();
      if (remain <= 0) return { status: 'enumTimeout', dfa1: firstDfa, enumerated };
      cnf.solver.timeLimitMs = remain;
      const r = cnf.solver.solve();
      if (r.timedOut) return { status: 'enumTimeout', dfa1: firstDfa, enumerated };
      if (!r.sat) return { status: 'exhausted', dfa1: firstDfa, enumerated };
      enumerated++;
      model = r.model;
      const dfa2 = modelToDfa(alphabet, cnf, model);
      if (DFA.signature(dfa2) !== sig1) {
        const word = DFA.distinguishingWord(firstDfa, dfa2);
        const v1 = DFA.evaluate(firstDfa, word).accepted ? '+' : '-';
        const v2 = DFA.evaluate(dfa2, word).accepted ? '+' : '-';
        return {
          status: 'distinct', dfa1: firstDfa, dfa2, word,
          verdicts: [v1, v2], enumerated,
        };
      }
    }
  }

  /** 删除式 UNSAT 核心：逐个尝试移除样本，移除后可满足则样本必要。 */
  function unsatCore(alphabet, samples, n, deadline) {
    let core = samples.slice();
    let i = 0;
    let timedOut = false;
    while (i < core.length) {
      const trial = core.slice(0, i).concat(core.slice(i + 1));
      let satResult;
      try {
        const cnf = buildCnf(alphabet, trial, n);
        cnf.solver.timeLimitMs = Math.max(1, deadline - Date.now());
        satResult = cnf.solver.solve();
      } catch (e) {
        satResult = { sat: false, timedOut: false };
      }
      if (satResult.timedOut) { timedOut = true; break; }
      if (satResult.sat) i++;          // 该样本是核心的必要成员
      else core = trial;               // 移除后仍 UNSAT，永久删除
    }
    return { core, complete: !timedOut };
  }

  /**
   * 主入口。
   * opts: { maxStates=6, timeLimitMs=8000, enumerate=true }
   */
  function synthesize(alphabet, positives, negatives, opts) {
    opts = opts || {};
    const maxStates = opts.maxStates || 6;
    const timeLimitMs = opts.timeLimitMs || 8000;
    const deadline = Date.now() + timeLimitMs;

    // 输入校验
    if (alphabet.length === 0) return { kind: 'invalid', reason: '操作字母表为空' };
    if (new Set(alphabet).size !== alphabet.length) {
      return { kind: 'invalid', reason: '操作字母表存在重复符号' };
    }
    const allWords = positives.concat(negatives);
    for (const w of allWords) {
      for (const a of w) {
        if (!alphabet.includes(a)) return { kind: 'invalid', reason: '序列含字母表外符号: ' + a };
      }
    }

    const conflicts = findDirectConflicts(positives, negatives);
    if (conflicts.length) return { kind: 'conflict', conflicts };

    const samples = positives.map(word => ({ word, label: '+' }))
      .concat(negatives.map(word => ({ word, label: '-' })));

    const sizeStatuses = [];
    for (let n = 1; n <= maxStates; n++) {
      const remain = deadline - Date.now();
      if (remain <= 0) {
        sizeStatuses.push({ n, status: 'timeout' });
        continue;
      }
      let cnf, result;
      try {
        cnf = buildCnf(alphabet, samples, n);
        cnf.solver.timeLimitMs = remain;
        result = cnf.solver.solve();
      } catch (e) {
        result = { sat: false, timedOut: false };
      }
      if (result.timedOut) {
        sizeStatuses.push({ n, status: 'timeout' });
        continue;
      }
      if (!result.sat) {
        sizeStatuses.push({ n, status: 'unsat' });
        continue;
      }
      // 找到当前最小可满足规模
      const dfa = modelToDfa(alphabet, cnf, result.model);
      const minimal = sizeStatuses.every(s => s.status === 'unsat');
      let comparison = null;
      if (opts.enumerate !== false && Date.now() < deadline) {
        comparison = enumerateAlternative(
          alphabet, samples, n, result.model, dfa, deadline
        );
      }
      sizeStatuses.push({ n, status: 'sat' });
      return {
        kind: 'ok',
        dfa,
        nStates: n,
        minimal,
        sizeStatuses,
        comparison,
        maxStates,
      };
    }

    // 上限内没有任何候选
    const anyTimeout = sizeStatuses.some(s => s.status === 'timeout');
    if (anyTimeout) {
      return { kind: 'noModelTimeout', sizeStatuses, maxStates };
    }
    // 所有规模都被证明 UNSAT：提取样本冲突核心（在最大规模上）
    const { core, complete } = unsatCore(
      alphabet, samples, maxStates, deadline
    );
    return { kind: 'unsat', core, coreComplete: complete, sizeStatuses, maxStates };
  }

  return {
    synthesize,
    findDirectConflicts,
    buildCnf,
    modelToDfa,
    unsatCore,
    wordKey,
  };
});
