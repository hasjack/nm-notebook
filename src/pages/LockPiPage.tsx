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
import { iFactorForMinusOne, resultAt } from "../lib/walk";

/** Lock π: β = 1. Expression base^(α · i · π). */
const BETA = 1;

export function LockPiPage() {
  const [t, setT] = useState(() => sliderFromBase(Math.E));
  const [odd, setOdd] = useState(1);
  const [lock, setLock] = useState(true);
  const [freeAlpha, setFreeAlpha] = useState(1);

  const base = baseFromSlider(t);
  const lockedAlpha = iFactorForMinusOne(base, odd);
  const alpha = lock ? lockedAlpha : freeAlpha;
  const product = alpha != null && Number.isFinite(alpha) ? alpha * BETA : null;

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
        alpha != null && Number.isFinite(alpha) ? alpha : null,
        "i-factor"
      ),
    [odd, base, alpha]
  );

  return (
    <main className="page">
      <h1>Lock π — watch i move</h1>
      <p className="lede">
        Hold the <strong>π-factor β = 1</strong>. The expression is{" "}
        base<sup>α · i · π</sup>. With lock −1 on, the i-factor retunes as{" "}
        <strong>α = odd / ln(base)</strong>. Unlock to free-α and watch i move.
      </p>

      {product == null || !Number.isFinite(product) ? (
        <>
          <div className="value">—</div>
          <div className="expr">base → 1: ln(base) = 0, no finite i-factor</div>
          <div className="rule">singularity: cannot keep −1 at base 1</div>
        </>
      ) : (
        <>
          <div className="value">{resultAt(product, base)}</div>
          <div className="expr">
            {fmtBase(base)} ^ ({fmt(alpha!, 4)} · i · π) · β = 1
            {lock ? `, α = ${odd} / ln(base)` : ", free α"}
          </div>
          <div className="rule">
            {lock
              ? `α · ln(${fmtBase(base)}) = ${fmt(alpha!, 4)} · ${fmt(Math.log(base), 4)} = ${odd} (odd) → −1`
              : `α · β · ln(${fmtBase(base)}) = ${fmt(product, 4)} · ${fmt(Math.log(base), 4)} = ${fmt(product * Math.log(base), 3)}`}
          </div>
        </>
      )}

      <div className="split-readout">
        <div>
          <div className="kv-label">π-factor β</div>
          <div className="kv-value">1 (locked)</div>
        </div>
        <div>
          <div className="kv-label">i-factor α</div>
          <div className="kv-value">
            {alpha != null && Number.isFinite(alpha) ? fmt(alpha, 5) : "—"}
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
          layout={layout2d("i-factor")}
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
              <span>i-factor α (free)</span>
              <span>{fmt(freeAlpha, 3)}</span>
            </label>
            <input
              type="range"
              min={-2}
              max={4}
              step={0.01}
              value={freeAlpha}
              onChange={(e) => setFreeAlpha(parseFloat(e.target.value))}
            />
          </>
        )}

        <p className="hint">
          Lock on: grow the base and α shrinks so α · ln(base) stays on the
          chosen odd branch. Lock off: slide α yourself — that is i moving under
          a fixed π.
        </p>
        <div className="actions">
          <button
            type="button"
            onClick={() => {
              setLock(true);
              setOdd(1);
              setT(sliderFromBase(Math.E));
              setFreeAlpha(1);
            }}
          >
            snap base → e (α = 1)
          </button>
          <button
            type="button"
            onClick={() => {
              setLock(true);
              setOdd(1);
              setT(sliderFromBase(Math.E ** 3));
            }}
          >
            snap base → e³ (α = ⅓)
          </button>
        </div>
      </div>
    </main>
  );
}
