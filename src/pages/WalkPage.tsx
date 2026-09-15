import { useMemo, useState } from "react";
import Plot from "../components/Plot";
import { fmt } from "../lib/format";
import { layout3d, plotConfig, traces3d } from "../lib/plotTheme";
import { resultAtE } from "../lib/walk";

export function WalkPage() {
  const [k, setK] = useState(1);

  const data = useMemo(() => traces3d(k, Math.E), [k]);
  const value = resultAtE(k);
  const prod = k * 1;
  const oddEnough =
    Math.abs(Math.abs(prod) % 2 - 1) < 0.02 && Math.abs(prod) >= 0.98;

  return (
    <main className="page">
      <h1>Walk — favourite 3D ribbon</h1>
      <p className="lede">
        Free <strong>k</strong> at base <strong>e</strong>. The walk is sampled
        densely in ln-space so windings stay smooth. Marks sit at 1/e³, 1/e, 1,
        e, e², e³.
      </p>

      <div className="value">{value}</div>
      <div className="expr">
        at base e, e ^ ({fmt(k, 2)} × i × π)
      </div>
      <div className="rule">
        k · ln(e) = {fmt(prod, 3)}
        {oddEnough
          ? "  → odd enough for −1"
          : "  (need an odd integer for −1)"}
      </div>

      <div className="graph3d">
        <Plot data={data} layout={layout3d} config={plotConfig} style={{ width: "100%", height: "100%" }} useResizeHandler />
      </div>

      <div className="panel">
        <label className="row">
          <span>k (the “i” slider)</span>
          <span>{fmt(k, 2)}</span>
        </label>
        <input
          type="range"
          min={-2}
          max={4}
          step={0.01}
          value={k}
          onChange={(e) => setK(parseFloat(e.target.value))}
        />
        <p className="hint">
          At base e, k = 1 recovers e<sup>iπ</sup> = −1. k = ½ lands on i. Even
          integers land on +1.
        </p>
        <div className="actions">
          <button type="button" onClick={() => setK(1)}>
            reset to Euler (−1)
          </button>
        </div>
      </div>
    </main>
  );
}
