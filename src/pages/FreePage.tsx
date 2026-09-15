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
import { resultAt } from "../lib/walk";

/**
 * Free play — neither i nor π locked.
 * Expression: base^(α · i · β · π)
 * product = α·β drives the walk ribbon (structured three-way).
 */
export function FreePage() {
  const [t, setT] = useState(() => sliderFromBase(Math.E));
  const [alpha, setAlpha] = useState(1);
  const [beta, setBeta] = useState(1);
  const [odd, setOdd] = useState(1);

  const base = baseFromSlider(t);
  const product = alpha * beta;
  const prodLn = product * Math.log(base);
  const nest = (prodLn * Math.PI) ** 2 / 6;
  const PI2_6 = (Math.PI * Math.PI) / 6;

  const r = Math.round(prodLn);
  const onPeg =
    Math.abs(prodLn - r) < 1e-4 && Math.abs(r) % 2 === 1;
  const onNest = Math.abs(Math.abs(prodLn) - 1) < 1e-4;
  const onBeacon = onPeg && onNest;

  const data3d = useMemo(
    () => traces3d(product, base),
    [product, base]
  );
  const data2d = useMemo(
    () =>
      traces2d(
        odd,
        Math.abs(Math.log(base)) < 1e-12 ? 0 : Math.log(base),
        Number.isFinite(product) ? product : null,
        "product"
      ),
    [odd, base, product]
  );

  return (
    <main className="page">
      <h1>Free — move i and π</h1>
      <p className="lede">
        Nothing locked. Play all three levers of{" "}
        <strong>base^(α · i · β · π)</strong>. The ribbon uses the product α·β;
        the structured nest is (α·β·π·ln(base))² / 6. Beacon lamps light when
        you land on α·β·ln(base)=±1 by accident — they don’t steer you.
      </p>

      <div className="value">{resultAt(product, base)}</div>
      <div className="expr">
        {fmtBase(base)} ^ ({fmt(alpha, 3)} · i · {fmt(beta, 3)} π)
      </div>
      <div className="rule">
        α·β·ln(base) = {fmt(prodLn, 4)}
        {onBeacon
          ? " · beacon (peg −1 and nest π²/6)"
          : onPeg
            ? " · on −1 peg"
            : onNest
              ? " · |prod|=1 (nest height)"
              : ""}
      </div>

      <div className="split-readout">
        <div>
          <div className="kv-label">α (i-factor)</div>
          <div className="kv-value">{fmt(alpha, 5)}</div>
        </div>
        <div>
          <div className="kv-label">β (π-factor)</div>
          <div className="kv-value">{fmt(beta, 5)}</div>
        </div>
        <div>
          <div className="kv-label">α · β</div>
          <div className="kv-value">{fmt(product, 5)}</div>
        </div>
        <div>
          <div className="kv-label">structured nest</div>
          <div className="kv-value">{fmt(nest, 5)}</div>
          <div className="hint">π²/6 = {fmt(PI2_6, 5)}</div>
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
          layout={layout2d("product")}
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
          <span>α (i-factor)</span>
          <span>{fmt(alpha, 3)}</span>
        </label>
        <input
          type="range"
          min={-2}
          max={4}
          step={0.01}
          value={alpha}
          onChange={(e) => setAlpha(parseFloat(e.target.value))}
        />

        <label className="row" style={{ marginTop: "0.8rem" }}>
          <span>β (π-factor)</span>
          <span>{fmt(beta, 3)}</span>
        </label>
        <input
          type="range"
          min={-2}
          max={4}
          step={0.01}
          value={beta}
          onChange={(e) => setBeta(parseFloat(e.target.value))}
        />

        <label className="row" style={{ marginTop: "0.8rem" }}>
          <span>locus odd branch (guide only)</span>
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
          Unlike Lock i / Lock π, neither factor is frozen and nothing auto-solves
          for −1. Use snaps if you want a known beacon; otherwise just explore.
        </p>
        <div className="actions">
          <button
            type="button"
            onClick={() => {
              setT(sliderFromBase(Math.E));
              setAlpha(1);
              setBeta(1);
            }}
          >
            beacon e · α=1 · β=1
          </button>
          <button
            type="button"
            onClick={() => {
              setT(sliderFromBase(Math.E ** 3));
              setAlpha(1);
              setBeta(1 / 3);
            }}
          >
            beacon e³ · β=⅓
          </button>
          <button
            type="button"
            onClick={() => {
              setT(sliderFromBase(Math.E));
              setAlpha(2);
              setBeta(0.5);
            }}
          >
            beacon e · α=2 · β=½
          </button>
          <button
            type="button"
            onClick={() => {
              setT(sliderFromBase(Math.E));
              setAlpha(1);
              setBeta(0.5);
            }}
          >
            off-peg · z ≈ i
          </button>
        </div>
      </div>
    </main>
  );
}
