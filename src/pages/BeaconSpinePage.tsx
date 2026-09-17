import { useMemo, useState } from "react";
import Plot from "../components/Plot";
import { fmt } from "../lib/format";
import { layout3d, plotConfig, traces3d } from "../lib/plotTheme";
import { resultAt } from "../lib/walk";

const SPINE = [1, 3, 5, 7, 9] as const;

/**
 * Integer choreography: e^{odd} with factor 1/odd — pleasant beacons.
 */
export function BeaconSpinePage() {
  const [idx, setIdx] = useState(0);
  const [which, setWhich] = useState<"beta" | "alpha">("beta");

  const odd = SPINE[idx];
  const base = Math.exp(odd);
  const alpha = which === "alpha" ? 1 / odd : 1;
  const beta = which === "beta" ? 1 / odd : 1;
  const product = alpha * beta;

  const data3d = useMemo(() => traces3d(product, base), [product, base]);

  return (
    <main className="page">
      <h1>Beacon spine — count the odds</h1>
      <p className="lede">
        Pleasant lattice: base = e^{odd}, and either the π-factor or the i-factor
        is 1/odd. Same −1 landing every time. e³ with ⅓ is the poster child —
        integer choreography, not a new theorem.
      </p>

      <div className="value">−1</div>
      <div className="expr">
        e^{odd} ^ ({fmt(alpha, 4)} · i · {fmt(beta, 4)} π) · value{" "}
        {resultAt(product, base)}
      </div>
      <div className="rule">
        α·β·ln(base) = {fmt(product * Math.log(base), 4)} = {odd} × {fmt(1 / odd, 4)}{" "}
        = 1 (odd) → beacon
      </div>

      <div className="split-readout">
        <div>
          <div className="kv-label">odd</div>
          <div className="kv-value">{odd}</div>
        </div>
        <div>
          <div className="kv-label">base</div>
          <div className="kv-value">e^{odd}</div>
        </div>
        <div>
          <div className="kv-label">α</div>
          <div className="kv-value">{fmt(alpha, 5)}</div>
        </div>
        <div>
          <div className="kv-label">β</div>
          <div className="kv-value">{fmt(beta, 5)}</div>
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

      <div className="panel">
        <div className="modes" style={{ display: "flex", gap: "0.4rem", flexWrap: "wrap" }}>
          {SPINE.map((o, i) => (
            <button
              key={o}
              type="button"
              onClick={() => setIdx(i)}
              style={{
                background: idx === i ? "#1f4e79" : "#fffaf3",
                color: idx === i ? "#fff" : "#1a1a1a",
                border: "1px solid #e2d8c8",
                borderRadius: 8,
                padding: "0.35rem 0.75rem",
                font: "inherit",
                cursor: "pointer",
              }}
            >
              e^{o} · 1/{o}
            </button>
          ))}
        </div>
        <label className="row" style={{ marginTop: "0.9rem" }}>
          <span>who takes the 1/odd?</span>
          <select
            value={which}
            onChange={(e) => setWhich(e.target.value as "beta" | "alpha")}
          >
            <option value="beta">π-factor β</option>
            <option value="alpha">i-factor α</option>
          </select>
        </label>
        <p className="hint">
          Video beat: tap up the odds — e, e³, e⁵ — twin factor shrinks 1, ⅓,
          ⅕ — the orange diamond climbs the base axis and the value never leaves
          −1.
        </p>
      </div>
    </main>
  );
}
