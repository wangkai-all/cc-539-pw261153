/*
 * tests/test.js — 纯 Node 测试（node tests/test.js），不依赖任何第三方包。
 * 覆盖：SAT 基础、DFA 求值/规范化/分歧串、合成的各类结果与诚实性约定。
 */
'use strict';
const assert = require('assert');
const SAT = require('../js/sat.js');
const DFA = require('../js/dfa.js');
const Synth = require('../js/synth.js');

let passed = 0;
function test(name, fn) {
  try { fn(); passed++; console.log('  ok - ' + name); }
  catch (e) { console.error('FAIL - ' + name); console.error(e && e.stack || e); process.exitCode = 1; }
}
const s = w => w.split('').filter(c => c !== 'ε'); // 书写方便，ε 表示空串
const eps = [];

/* ---------- SAT ---------- */
test('SAT: 可满足 (x∨y)∧¬x 推出 y', () => {
  const slv = new SAT.Solver();
  slv.newVar(); slv.newVar();
  assert(slv.addClause([2, 4]));
  assert(slv.addClause([3])); // ¬x
  const r = slv.solve();
  assert(r.sat && !r.timedOut);
  assert(r.model[1] === false && r.model[2] === true);
});

test('SAT: 直接 UNSAT', () => {
  const slv = new SAT.Solver();
  slv.newVar();
  assert(slv.addClause([2]));
  assert(slv.addClause([3]) === false);
});

test('SAT: 鸽子洞 3 鸽 2 洞 UNSAT', () => {
  const slv = new SAT.Solver();
  const V = {};
  for (let i = 0; i < 3; i++) for (let j = 0; j < 2; j++) { V[i + ',' + j] = slv.newVar(); }
  for (let i = 0; i < 3; i++) {
    slv.addClause([V[i + ',0'] << 1, V[i + ',1'] << 1]);
    slv.addClause([(V[i + ',0'] << 1) ^ 1, (V[i + ',1'] << 1) ^ 1]);
  }
  for (let j = 0; j < 2; j++) {
    for (let i1 = 0; i1 < 3; i1++) for (let i2 = i1 + 1; i2 < 3; i2++) {
      slv.addClause([(V[i1 + ',' + j] << 1) ^ 1, (V[i2 + ',' + j] << 1) ^ 1]);
    }
  }
  const r = slv.solve();
  assert(!r.sat && !r.timedOut);
});

test('SAT: 超时不等于 UNSAT（长传播链中途耗尽预算）', () => {
  // 可满足的长蕴含链：x1 ∧ (¬xi ∨ x(i+1))，预算 1ms，传播未完成必须报超时
  const N = 200000;
  const slv = new SAT.Solver({ timeLimitMs: 1 });
  for (let i = 0; i < N; i++) slv.newVar();
  slv.addClause([2]);
  for (let i = 1; i < N; i++) slv.addClause([i * 2 + 1, (i + 1) * 2]);
  const r = slv.solve();
  assert(r.sat === false);
  assert(r.timedOut === true, '时间预算耗尽必须标记超时，不能谎报 UNSAT');
  // 同一公式放开预算后可满足，证明超时确实不代表无解
  const slv2 = new SAT.Solver({ timeLimitMs: 0 });
  for (let i = 0; i < N; i++) slv2.newVar();
  slv2.addClause([2]);
  for (let i = 1; i < N; i++) slv2.addClause([i * 2 + 1, (i + 1) * 2]);
  const r2 = slv2.solve();
  assert(r2.sat === true && r2.timedOut === false);
});

/* ---------- DFA ---------- */
function handDfa() {
  // 偶数个 a 接受；b 自环；状态 2 为显式汇点（此处不可达）
  return {
    alphabet: ['a', 'b'], start: 0, n: 3,
    accept: [true, false, false],
    trans: { a: [1, 0, 2], b: [0, 1, 2] }, sink: 2,
  };
}
test('DFA: 求值与空串', () => {
  const d = handDfa();
  assert(DFA.evaluate(d, eps).accepted === true);
  assert(DFA.evaluate(d, s('a')).accepted === false);
  assert(DFA.evaluate(d, s('aa')).accepted === true);
  assert(DFA.evaluate(d, s('abbab')).accepted === true);  // 2 个 a
  assert(DFA.evaluate(d, s('abba')).accepted === true);
});

test('DFA: 编号不同但语言相同 → 规范签名一致', () => {
  const d1 = handDfa();
  const d2 = {
    alphabet: ['a', 'b'], start: 5, n: 3,
    accept: [false, true, false],
    trans: { a: [5, 7, 6], b: [6, 5, 7] }, sink: 6, // 6=原0,5=原1,7=原0? 重新构造
  };
  // 显式构造同语言重编号：原 0->新2(accept), 原1->新0, sink->新1
  const d3 = {
    alphabet: ['a', 'b'], start: 2, n: 3,
    accept: [false, false, true],
    trans: { a: [2, 1, 0], b: [0, 1, 2] }, sink: 1,
  };
  assert(DFA.sameLanguage(d1, d3));
  assert(DFA.signature(d1) === DFA.signature(d3));
  assert(DFA.minimize(d1).n === 2); // 汇点不可达，最小化后消失
  void d2;
});

test('DFA: 乘积图最短分歧串', () => {
  // d1 接受 b；d2 拒绝一切
  const d1 = {
    alphabet: ['a', 'b'], start: 0, n: 3,
    accept: [false, true, false],
    trans: { a: [2, 2, 2], b: [1, 1, 2] }, sink: 2,
  };
  const d2 = {
    alphabet: ['a', 'b'], start: 0, n: 1,
    accept: [false],
    trans: { a: [0], b: [0] }, sink: 0,
  };
  const w = DFA.distinguishingWord(d1, d2);
  assert.deepStrictEqual(w, ['b']);
  assert(DFA.evaluate(d1, w).accepted !== DFA.evaluate(d2, w).accepted);
});

/* ---------- 合成 ---------- */
function checkSamples(dfa, pos, neg) {
  for (const w of pos) assert(DFA.evaluate(dfa, w).accepted === true, '应接受 ' + JSON.stringify(w));
  for (const w of neg) assert(DFA.evaluate(dfa, w).accepted === false, '应拒绝 ' + JSON.stringify(w));
}

test('合成: 偶数 a 语言，最小性已证明，含汇点', () => {
  const pos = [eps, s('aa'), s('abba'), s('babbab')];
  const neg = [s('a'), s('abb'), s('ba')];
  const r = Synth.synthesize(['a', 'b'], pos, neg, { timeLimitMs: 5000 });
  assert.strictEqual(r.kind, 'ok');
  assert(r.minimal === true);
  assert.strictEqual(r.nStates, 3); // 2 个可达状态 + 汇点
  assert(DFA.findSink(r.dfa) === r.dfa.sink);
  checkSamples(r.dfa, pos, neg);
});

test('合成: 空序列作为正例', () => {
  const pos = [eps, s('xx'), s('xyx')];
  const neg = [s('x'), s('y'), s('xxy')];
  const r = Synth.synthesize(['x', 'y'], pos, neg, { timeLimitMs: 5000 });
  assert.strictEqual(r.kind, 'ok');
  assert(r.dfa.accept[0] === true);
  checkSamples(r.dfa, pos, neg);
});

test('合成: 直接冲突样本定位', () => {
  const r = Synth.synthesize(['a', 'b'], [s('ab'), eps], [s('ab')], {});
  assert.strictEqual(r.kind, 'conflict');
  assert.deepStrictEqual(r.conflicts, [s('ab')]);
});

test('合成: 一元语言强制 7 状态 → 上限 6 内 UNSAT 并给核心', () => {
  // 鸽链原理：a^0..a^5 接受、a^6..a^12 拒绝 → 必须 7 个总状态
  const a = n => 'a'.repeat(n).split('');
  const pos = [0, 1, 2, 3, 4, 5].map(a);
  const neg = [6, 7, 8, 9, 10, 11, 12].map(a);
  const r = Synth.synthesize(['a'], pos, neg, { maxStates: 6, timeLimitMs: 8000 });
  assert.strictEqual(r.kind, 'unsat');
  assert(r.sizeStatuses.every(x => x.status === 'unsat'));
  assert(r.core.length >= 2 && r.core.length <= pos.length + neg.length);
  assert(r.coreComplete === true);
  // 核心本身确实无法在 6 状态内满足
  const cpos = r.core.filter(x => x.label === '+').map(x => x.word);
  const cneg = r.core.filter(x => x.label === '-').map(x => x.word);
  const rc = Synth.synthesize(['a'], cpos, cneg, { maxStates: 6, timeLimitMs: 8000, enumerate: false });
  assert(rc.kind === 'unsat' || rc.kind === 'noModelTimeout');
});

test('合成: 样本不足时给出可区分候选与最短分歧串', () => {
  const r = Synth.synthesize(['a', 'b'], [s('a')], [eps], { timeLimitMs: 5000 });
  assert.strictEqual(r.kind, 'ok');
  assert(r.comparison);
  if (r.comparison.status === 'distinct') {
    assert(r.comparison.verdicts[0] !== r.comparison.verdicts[1]);
    const w = r.comparison.word;
    const v1 = DFA.evaluate(r.comparison.dfa1, w).accepted;
    const v2 = DFA.evaluate(r.comparison.dfa2, w).accepted;
    assert(v1 !== v2);
  } else {
    assert(['exhausted', 'enumTimeout'].includes(r.comparison.status));
  }
});

test('合成: 预算过小时只能报告超时，不得谎报 UNSAT', () => {
  const a = n => 'a'.repeat(n).split('');
  const pos = [0, 1, 2, 3, 4, 5].map(a);
  const neg = [6, 7, 8, 9, 10, 11, 12].map(a);
  const r = Synth.synthesize(['a'], pos, neg, { maxStates: 6, timeLimitMs: 1 });
  assert(['noModelTimeout', 'ok'].includes(r.kind));
  if (r.kind === 'noModelTimeout') {
    assert(r.sizeStatuses.some(x => x.status === 'timeout'));
    assert(!r.sizeStatuses.some(x => x.status === 'sat'));
  }
});

test('合成: 所有候选都与样本一致（重复前缀场景）', () => {
  const pos = [s('ab'), s('abab'), s('ababab')];
  const neg = [eps, s('a'), s('aba'), s('ababa')];
  const r = Synth.synthesize(['a', 'b'], pos, neg, { timeLimitMs: 5000 });
  assert.strictEqual(r.kind, 'ok');
  checkSamples(r.dfa, pos, neg);
  if (r.comparison && r.comparison.status === 'distinct') {
    checkSamples(r.comparison.dfa2, pos, neg);
  }
});

test('合成: 字母表外符号被拒绝', () => {
  const r = Synth.synthesize(['a'], [s('c')], [], {});
  assert.strictEqual(r.kind, 'invalid');
});

console.log('\n' + passed + ' 个测试通过' + (process.exitCode ? '，存在失败' : ''));
