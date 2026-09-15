import { useMemo, useState } from "react";
import Plot from "../components/Plot";
import { baseFromSlider, fmt, fmtBase, sliderFromBase } from "../lib/format";
import { layout3d, plotConfig, traces3d } from "../lib/plotTheme";
import { resultAt } from "../lib/walk";

/** Classical exponent: i-factor = 1, π-factor = 1 ⇒ product = 1. */
const PRODUCT = 1;

export function WalkPage() {
  const [t, setT] = useState(() => sliderFromBase(Math.E));
  const base = baseFromSlider(t);

  const data = useMemo(() => traces3d(PRODUCT, base), [base]);
  const value = resultAt(PRODUCT, base);
  const angFactor = Math.log(base); // product · ln(base) with product = 1
  const oddEnough =
    Math.abs(Math.abs(angFactor) % 2 - 1) < 0.02 && Math.abs(angFactor) >= 0.98;

  return (
    <main className="page">
      <h1>Walk — variable base, classical iπ</h1>
      <p className="lede">
        Hold the classical exponent <strong>iπ</strong> fixed (i-factor = 1,
        π-factor = 1) and walk the <strong>base</strong> in ln-space. Orange
        diamond marks the current base; navy marks sit at powers of e. Exploring,
        not claiming.
      </p>

      <div className="value">{value}</div>
      <div className="expr">
        {fmtBase(base)} ^ (i × π)
      </div>
      <div className="rule">
        ln({fmtBase(base)}) = {fmt(angFactor, 3)}
        {oddEnough
          ? "  → odd enough for −1"
          : "  (need an odd integer for −1)"}
      </div>

      <div className="graph3d">
        <Plot
          data={data}
          layout={layout3d}
          config={plotConfig}
          style={{ width: "100%", height: "100%" }}
          useResizeHandler
        />
      </div>

      <div className="panel">
        <label className="row">
          <span>base (ln-space)</span>
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
        <p className="hint">
          At base e you recover e<sup>iπ</sup> = −1. At base e³ the angle is
          3π and you land on −1 again on the odd branch 3. Near base = 1 the
          walk sits at +1 with no winding.
        </p>
        <div className="actions">
          <button type="button" onClick={() => setT(sliderFromBase(Math.E))}>
            snap base → e (−1)
          </button>
          <button
            type="button"
            onClick={() => setT(sliderFromBase(Math.E ** 3))}
          >
            snap base → e³
          </button>
        </div>
      </div>
    </main>
  );
}
