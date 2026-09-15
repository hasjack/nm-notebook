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
import { kForMinusOne, resultAt } from "../lib/walk";

export function LockPage() {
  const [t, setT] = useState(() => sliderFromBase(Math.E));
  const [odd, setOdd] = useState(1);

  const base = baseFromSlider(t);
  const k = kForMinusOne(base, odd);

  const data3d = useMemo(
    () => (k != null && Number.isFinite(k) ? traces3d(k, base) : []),
    [k, base]
  );
  const data2d = useMemo(
    () =>
      traces2d(
        odd,
        Math.abs(Math.log(base)) < 1e-12 ? 0 : Math.log(base),
        k != null && Number.isFinite(k) ? k : null
      ),
    [odd, base, k]
  );

  return (
    <main className="page">
      <h1>Lock −1</h1>
      <p className="lede">
        Grow the base in ln-space and retune <strong>k = odd / ln(base)</strong>{" "}
        so the result stays −1 on the chosen odd branch. Near base = 1 the needed
        k blows up.
      </p>

      {k == null || !Number.isFinite(k) ? (
        <>
          <div className="value">—</div>
          <div className="expr">base → 1: ln(base) = 0, no finite k</div>
          <div className="rule">singularity: cannot keep −1 at base 1</div>
        </>
      ) : (
        <>
          <div className="value">{resultAt(k, base)}</div>
          <div className="expr">
            {fmtBase(base)} ^ ({fmt(k, 4)} × i × π) · k = {odd} / ln(base)
          </div>
          <div className="rule">
            k · ln({fmtBase(base)}) = {fmt(k, 4)} · {fmt(Math.log(base), 4)} ={" "}
            {odd} (odd) → −1
          </div>
        </>
      )}

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
          layout={layout2d}
          config={plotConfig}
          style={{ width: "100%", height: "100%" }}
          useResizeHandler
        />
      </div>

      <div className="panel">
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

        <p className="hint">
          Base is spaced in ln-space (powers of e). Near base = 1 the needed k
          blows up — ln(1) = 0, so no finite k keeps −1. With branch 1 and base e,
          you get k = 1 again.
        </p>
        <div className="actions">
          <button
            type="button"
            onClick={() => {
              setOdd(1);
              setT(sliderFromBase(Math.E));
            }}
          >
            snap base → e (k = 1)
          </button>
          <button
            type="button"
            onClick={() => {
              setOdd(1);
              setT(sliderFromBase(Math.E ** 3));
            }}
          >
            snap base → e³ (k = ⅓)
          </button>
        </div>
      </div>
    </main>
  );
}
