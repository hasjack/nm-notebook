import { useMemo, useState } from "react";
import Plot from "../components/Plot";
import { baseFromSlider, fmt, fmtBase, sliderFromBase } from "../lib/format";
import {
  layout2d,
  layout3d,
  plotConfig,
  traces2d,
  traces3d,
} from "../lib/plotTheme";
import { piFactorForMinusOne, resultAt } from "../lib/walk";

/** Lock i: α = 1. Expression base^(i · βπ). */
const ALPHA = 1;

export function LockIPage() {
  const [t, setT] = useState(() => sliderFromBase(Math.E));
  const [odd, setOdd] = useState(1);
  const [lock, setLock] = useState(true);
  const [freeBeta, setFreeBeta] = useState(1);

  const base = baseFromSlider(t);
  const lockedBeta = piFactorForMinusOne(base, odd);
  const beta = lock ? lockedBeta : freeBeta;
  const product = beta != null && Number.isFinite(beta) ? ALPHA * beta : null;

  const data3d = useMemo(
    () =>
      product != null && Number.isFinite(product) ? traces3d(product, base) : [],
    [product, base]
  );
  const data2d = useMemo(
    () =>
      traces2d(
        odd,
        Math.abs(Math.log(base)) < 1e-12 ? 0 : Math.log(base),
        beta != null && Number.isFinite(beta) ? beta : null,
        "pi-factor"
      ),
    [odd, base, beta]
  );

  return (
    <main className="page">
      <h1>Lock i — watch π move</h1>
      <p className="lede">
        Hold the <strong>i-factor α = 1</strong>. The expression is{" "}
        base<sup>i · βπ</sup>. With lock −1 on, the π-factor retunes as{" "}
        <strong>β = odd / ln(base)</strong>. Unlock to free-β and watch π move.
      </p>

      {product == null || !Number.isFinite(product) ? (
        <>
          <div className="value">—</div>
          <div className="expr">base → 1: ln(base) = 0, no finite π-factor</div>
          <div className="rule">singularity: cannot keep −1 at base 1</div>
        </>
      ) : (
        <>
          <div className="value">{resultAt(product, base)}</div>
          <div className="expr">
            {fmtBase(base)} ^ (i · {fmt(beta!, 4)} π) · α = 1
            {lock ? `, β = ${odd} / ln(base)` : ", free β"}
          </div>
          <div className="rule">
            {lock
              ? `β · ln(${fmtBase(base)}) = ${fmt(beta!, 4)} · ${fmt(Math.log(base), 4)} = ${odd} (odd) → −1`
              : `α · β · ln(${fmtBase(base)}) = ${fmt(product, 4)} · ${fmt(Math.log(base), 4)} = ${fmt(product * Math.log(base), 3)}`}
          </div>
        </>
      )}

      <div className="split-readout">
        <div>
          <div className="kv-label">i-factor α</div>
          <div className="kv-value">1 (locked)</div>
        </div>
        <div>
          <div className="kv-label">π-factor β</div>
          <div className="kv-value">
            {beta != null && Number.isFinite(beta) ? fmt(beta, 5) : "—"}
          </div>
        </div>
        <div>
          <div className="kv-label">base</div>
          <div className="kv-value">{fmtBase(base)}</div>
        </div>
      </div>

      <div className="graph3d">
        <Plot
          data={data3d}
          layout={layout3d}
          config={plotConfig}
          style={{ width: "100%", height: "100%" }}
          useResizeHandler
        />
      </div>
      <div className="graph2d">
        <Plot
          data={data2d}
          layout={layout2d("pi-factor")}
          config={plotConfig}
          style={{ width: "100%", height: "100%" }}
          useResizeHandler
        />
      </div>

      <div className="panel">
        <label className="row">
          <span>lock result = −1</span>
          <input
            type="checkbox"
            checked={lock}
            onChange={(e) => setLock(e.target.checked)}
          />
        </label>

        <label className="row">
          <span>base</span>
          <span>{fmtBase(base)}</span>
        </label>
        <input
          type="range"
          min={0}
          max={1}
          step={0.001}
          value={t}
          onChange={(e) => setT(parseFloat(e.target.value))}
        />

        <label className="row" style={{ marginTop: "0.8rem" }}>
          <span>odd branch</span>
          <select
            value={odd}
            onChange={(e) => setOdd(parseInt(e.target.value, 10))}
          >
            {[-5, -3, -1, 1, 3, 5].map((o) => (
              <option key={o} value={o}>
                {o}
              </option>
            ))}
          </select>
        </label>

        {!lock && (
          <>
            <label className="row" style={{ marginTop: "0.8rem" }}>
              <span>π-factor β (free)</span>
              <span>{fmt(freeBeta, 3)}</span>
            </label>
            <input
              type="range"
              min={-2}
              max={4}
              step={0.01}
              value={freeBeta}
              onChange={(e) => setFreeBeta(parseFloat(e.target.value))}
            />
          </>
        )}

        <p className="hint">
          Lock on: grow the base and β shrinks so β · ln(base) stays on the
          chosen odd branch. Lock off: slide β yourself and watch the complex
          value leave −1 — that is π moving under a fixed i.
        </p>
        <div className="actions">
          <button
            type="button"
            onClick={() => {
              setLock(true);
              setOdd(1);
              setT(sliderFromBase(Math.E));
              setFreeBeta(1);
            }}
          >
            snap base → e (β = 1)
          </button>
          <button
            type="button"
            onClick={() => {
              setLock(true);
              setOdd(1);
              setT(sliderFromBase(Math.E ** 3));
            }}
          >
            snap base → e³ (β = ⅓)
          </button>
        </div>
      </div>
    </main>
  );
}
