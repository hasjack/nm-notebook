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
import {
  alphaBetaForMinusOne,
  productToAlphaBeta,
  resultAtSplit,
} from "../lib/walk";

export function SplitPage() {
  const [t, setT] = useState(() => sliderFromBase(Math.E));
  const [odd, setOdd] = useState(1);
  const [share, setShare] = useState(0.5);
  const [lock, setLock] = useState(true);

  const base = baseFromSlider(t);

  const ab = useMemo(() => {
    if (lock) {
      return alphaBetaForMinusOne(base, odd, share);
    }
    // free product demo around Euler strength when unlocked: product = 1
    return productToAlphaBeta(1, share);
  }, [lock, base, odd, share]);

  const alpha = ab?.alpha ?? 0;
  const beta = ab?.beta ?? 0;
  const product = ab?.product ?? 0;
  const k = product;

  const data3d = useMemo(
    () => (Number.isFinite(k) ? traces3d(k, base) : []),
    [k, base]
  );
  const data2d = useMemo(
    () =>
      traces2d(
        odd,
        Math.abs(Math.log(base)) < 1e-12 ? 0 : Math.log(base),
        Number.isFinite(k) ? k : null
      ),
    [odd, base, k]
  );

  const value =
    ab == null
      ? "—"
      : resultAtSplit(alpha, beta, lock ? base : Math.E);

  return (
    <main className="page">
      <h1>Split i &amp; π</h1>
      <p className="lede">
        Write the same strength as <strong>k = α·β</strong>, so the expression is{" "}
        base<sup>α · i · βπ</sup>. Under lock −1, αβ · ln(base) = odd. The share
        dial trades magnitude between α (i-factor) and β (π-factor) without
        changing the product.
      </p>

      <div className="value">{value}</div>
      <div className="expr">
        {lock ? fmtBase(base) : "e"} ^ (α · i · βπ) with α = {fmt(alpha, 4)}, β ={" "}
        {fmt(beta, 4)}, αβ = {fmt(product, 4)}
      </div>
      <div className="rule">
        {lock
          ? ab == null
            ? "singularity near base 1 — no finite αβ"
            : `αβ · ln(${fmtBase(base)}) = ${fmt(product, 4)} · ${fmt(Math.log(base), 4)} = ${odd} (odd) → −1`
          : `free demo product αβ = ${fmt(product, 4)} at base e (unlock to explore share alone)`}
      </div>

      <div className="split-readout">
        <div>
          <div className="kv-label">α (i factor)</div>
          <div className="kv-value">{fmt(alpha, 5)}</div>
        </div>
        <div>
          <div className="kv-label">β (π factor)</div>
          <div className="kv-value">{fmt(beta, 5)}</div>
        </div>
        <div>
          <div className="kv-label">α · β = k</div>
          <div className="kv-value">{fmt(product, 5)}</div>
        </div>
        <div>
          <div className="kv-label">share</div>
          <div className="kv-value">{fmt(share, 2)}</div>
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
      {lock && (
        <div className="graph2d">
          <Plot
            data={data2d}
            layout={layout2d}
            config={plotConfig}
            style={{ width: "100%", height: "100%" }}
            useResizeHandler
          />
        </div>
      )}

      <div className="panel">
        <label className="row">
          <span>lock result = −1</span>
          <input
            type="checkbox"
            checked={lock}
            onChange={(e) => setLock(e.target.checked)}
          />
        </label>

        {lock && (
          <>
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
          </>
        )}

        <label className="row" style={{ marginTop: "0.8rem" }}>
          <span>share (α ↔ β)</span>
          <span>{fmt(share, 2)}</span>
        </label>
        <input
          type="range"
          min={0}
          max={1}
          step={0.01}
          value={share}
          onChange={(e) => setShare(parseFloat(e.target.value))}
        />
        <p className="hint">
          share = 0 → |α|≈1, β≈|product|; share = ½ → |α|=|β|=√|P|; share = 1 →
          α=product, β=1. Under lock −1 the complex value is unchanged — only the
          naming of the factors moves.
        </p>
        <div className="actions">
          <button
            type="button"
            onClick={() => {
              setLock(true);
              setOdd(1);
              setT(sliderFromBase(Math.E));
              setShare(0.5);
            }}
          >
            snap e / share ½
          </button>
          <button
            type="button"
            onClick={() => {
              setLock(true);
              setOdd(1);
              setT(sliderFromBase(Math.E ** 3));
              setShare(0.5);
            }}
          >
            snap e³ / share ½
          </button>
        </div>
      </div>
    </main>
  );
}
