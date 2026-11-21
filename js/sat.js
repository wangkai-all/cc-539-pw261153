/*
 * sat.js — 极简 DPLL SAT 求解器（无第三方依赖）
 *
 * 特性：
 *  - 双监视字面量（表头/表尾槽位，watch list 不随监视交换而失效）
 *  - 首 UIP 冲突分析 + 子句学习 + 非时序回跳
 *  - VSIDS 活动度 + 相位保存
 *  - 时间预算：超时返回 { sat:false, timedOut:true }，不把超时当成 UNSAT
 *
 * 字面量约定：变量 v >= 1，正字面量 = 2*v（偶数），负字面量 = 2*v+1（奇数），取反 l^1。
 */
(function (root, factory) {
  const mod = factory();
  if (typeof module !== 'undefined' && module.exports) module.exports = mod;
  else root.SAT = mod;
})(typeof self !== 'undefined' ? self : this, function () {
  'use strict';

  function neg(l) { return l ^ 1; }

  class Solver {
    constructor(opts) {
      opts = opts || {};
      this.timeLimitMs = opts.timeLimitMs || 0;
      this.nVars = 0;
      this.clauses = [];          // 每条子句 { lits: [], w: [slot, slot] }
      this.watches = new Map();   // 字面量 -> 槽位对象数组
      this.value = [0];
      this.reason = [null];       // 蕴含变量的子句下标，决策为 null
      this.level = [0];
      this.activity = [0];
      this.phase = [0];
      this.seen = [false];
      this.trail = [];
      this.trailLim = [];
      this.qhead = 0;
      this.decisions = 0;
      this.conflicts = 0;
      this.varInc = 1;
      this.varDecay = 1 / 0.95;
      this.startTime = 0;
      this.timedOut = false;
    }

    newVar() {
      this.nVars++;
      this.value.push(0);
      this.reason.push(null);
      this.level.push(0);
      this.activity.push(0);
      this.phase.push(0);
      this.seen.push(false);
      return this.nVars;
    }

    decisionLevel() { return this.trailLim.length; }

    litValue(l) {
      const a = this.value[l >> 1];
      return (l & 1) ? -a : a;
    }

    _watchList(l) {
      let arr = this.watches.get(l);
      if (!arr) { arr = []; this.watches.set(l, arr); }
      return arr;
    }

    /** 仅在根层级调用：常量化简，单子句立即入队。false 表示根冲突。 */
    addClause(lits) {
      const c = [];
      for (const l of lits) {
        const val = this.litValue(l);
        if (val === 1) return true;
        if (val === -1) continue;
        if (c.includes(neg(l))) return true;
        if (!c.includes(l)) c.push(l);
      }
      if (c.length === 0) return false;
      const ci = this.clauses.length;
      const clause = { lits: c, w: [null, null] };
      this.clauses.push(clause);
      if (c.length === 1) {
        const slot = { ci, pos: 0 };
        clause.w[0] = slot;
        clause.w[1] = slot; // 单元：两个监视位指向同一槽位
        this._watchList(c[0]).push(slot);
        return this._enqueue(c[0], ci);
      }
      clause.w[0] = { ci, pos: 0 };
      clause.w[1] = { ci, pos: 1 };
      this._watchList(c[0]).push(clause.w[0]);
      this._watchList(c[1]).push(clause.w[1]);
      return true;
    }

    _enqueue(l, reason) {
      const v = l >> 1;
      const want = (l & 1) ? -1 : 1;
      if (this.value[v] !== 0) return this.value[v] === want;
      this.value[v] = want;
      this.reason[v] = reason;
      this.level[v] = this.decisionLevel();
      this.trail.push(l);
      return true;
    }

    _cancelUntil(lvl) {
      if (this.decisionLevel() <= lvl) return;
      const lim = this.trailLim[lvl];
      for (let i = this.trail.length - 1; i >= lim; i--) {
        const v = this.trail[i] >> 1;
        this.phase[v] = this.value[v];
        this.value[v] = 0;
        this.reason[v] = null;
        this.level[v] = 0;
      }
      this.trail.length = lim;
      this.trailLim.length = lvl;
      this.qhead = this.trail.length;
    }

    _propagate() {
      let processed = 0;
      while (this.qhead < this.trail.length) {
        // 长传播链中也要尊重时间预算（每 4096 个字面量检查一次）
        if ((processed++ & 4095) === 0 && this.timeLimitMs > 0 &&
            Date.now() - this.startTime > this.timeLimitMs) {
          return 'TIMEOUT';
        }
        const p = this.trail[this.qhead++];
        const falseLit = neg(p);
        const ws = this.watches.get(falseLit);
        if (!ws) continue;
        let i = 0, j = 0;
        let confl = -1;
        while (i < ws.length) {
          const slot = ws[i++];
          const clause = this.clauses[slot.ci];
          const c = clause.lits;
          // 槽位可能因监视交换而指向别的位置；确保 falseLit 位于 pos=1
          if (c[clause.w[0].pos] === falseLit) {
            const t = clause.w[0]; clause.w[0] = clause.w[1]; clause.w[1] = t;
          }
          const firstPos = clause.w[0].pos;
          const first = c[firstPos];
          if (this.litValue(first) === 1) { ws[j++] = slot; continue; }
          // 单元子句（两槽位相同）：没有其他字面量可换
          if (clause.w[0] === clause.w[1]) {
            ws[j++] = slot;
            if (this.litValue(first) === -1) {
              confl = slot.ci;
              while (i < ws.length) ws[j++] = ws[i++];
              ws.length = j;
              return confl;
            }
            this._enqueue(first, slot.ci);
            continue;
          }
          // 在非监视字面量中寻找新监视
          let found = false;
          for (let k = 0; k < c.length; k++) {
            if (k === clause.w[0].pos || k === clause.w[1].pos) continue;
            if (this.litValue(c[k]) !== -1) {
              // 把新字面量换到 pos=1，旧 falseLit 占据它原来的位置
              const oldPos = clause.w[1].pos;
              c[oldPos] = c[k];
              c[k] = falseLit;
              clause.w[1] = { ci: slot.ci, pos: oldPos };
              this._watchList(c[oldPos]).push(clause.w[1]);
              found = true;
              break;
            }
          }
          if (found) continue; // 旧槽位随本次压缩被丢弃，新槽位已挂上
          // 没有新监视：first 成为断言/冲突字面量，旧槽位保留
          ws[j++] = slot;
          if (this.litValue(first) === -1) {
            confl = slot.ci;
            while (i < ws.length) ws[j++] = ws[i++];
            ws.length = j;
            return confl;
          }
          this._enqueue(first, slot.ci);
        }
        ws.length = j;
      }
      return null;
    }

    /* 首 UIP 冲突分析，返回学习子句与回跳层级。 */
    _analyze(conflCi) {
      const learned = [];
      let pathC = 0;
      let p = -1;
      let reason = conflCi;
      let index = this.trail.length - 1;
      let btlevel = 0;
      const curLevel = this.decisionLevel();
      do {
        const c = this.clauses[reason].lits;
        for (const q of c) {
          if (q === p) continue;
          const v = q >> 1;
          if (this.level[v] === 0 || this.seen[v]) continue;
          this.seen[v] = true;
          this._bumpActivity(v);
          if (this.level[v] >= curLevel) {
            pathC++;
          } else {
            learned.push(q);
            if (this.level[v] > btlevel) btlevel = this.level[v];
          }
        }
        while (index >= 0 && !this.seen[this.trail[index] >> 1]) index--;
        p = this.trail[index];
        const pv = p >> 1;
        this.seen[pv] = false;
        reason = this.reason[pv];
        index--;
        pathC--;
      } while (pathC > 0);
      learned.push(neg(p));
      return { learned, btlevel };
    }

    _bumpActivity(v) {
      this.activity[v] += this.varInc;
      if (this.activity[v] > 1e100) {
        for (let i = 1; i <= this.nVars; i++) this.activity[i] *= 1e-100;
        this.varInc *= 1e-100;
      }
    }

    _decayActivity() { this.varInc *= this.varDecay; }

    _pickBranchVar() {
      let best = 0;
      let bestAct = -1;
      for (let v = 1; v <= this.nVars; v++) {
        if (this.value[v] !== 0) continue;
        if (this.activity[v] > bestAct) { bestAct = this.activity[v]; best = v; }
      }
      return best;
    }

    _timeout() {
      if (this.timeLimitMs <= 0) return false;
      return (Date.now() - this.startTime) > this.timeLimitMs;
    }

    _buildModel() {
      const m = new Array(this.nVars + 1).fill(false);
      for (let v = 1; v <= this.nVars; v++) m[v] = this.value[v] === 1;
      return m;
    }

    solve() {
      this.startTime = Date.now();
      this.timedOut = false;
      let confl = this._propagate();
      if (confl === 'TIMEOUT') {
        this.timedOut = true;
        this._cancelUntil(0);
        return { sat: false, timedOut: true, model: null };
      }
      if (confl !== null) return { sat: false, timedOut: false, model: null };
      while (true) {
        if (this._timeout()) {
          this.timedOut = true;
          this._cancelUntil(0);
          return { sat: false, timedOut: true, model: null };
        }
        confl = this._propagate();
        if (confl === 'TIMEOUT') {
          this.timedOut = true;
          this._cancelUntil(0);
          return { sat: false, timedOut: true, model: null };
        }
        if (confl !== null) {
          this.conflicts++;
          this._decayActivity();
          if (this.decisionLevel() === 0) {
            return { sat: false, timedOut: false, model: null };
          }
          const { learned, btlevel } = this._analyze(confl);
          this._cancelUntil(btlevel);
          if (!this.addClause(learned)) {
            return { sat: false, timedOut: false, model: null };
          }
        } else {
          const v = this._pickBranchVar();
          if (v === 0) {
            return { sat: true, timedOut: false, model: this._buildModel() };
          }
          this.trailLim.push(this.trail.length);
          this.decisions++;
          const positive = this.phase[v] === 1;
          this._enqueue(positive ? v * 2 : v * 2 + 1, null);
        }
      }
    }
  }

  return { Solver, neg };
});
