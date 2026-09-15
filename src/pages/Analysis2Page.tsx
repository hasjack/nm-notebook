import { useMemo, useState } from "react";
import { fmt, fmtBase, baseFromSlider, sliderFromBase } from "../lib/format";

const PI2_6 = (Math.PI * Math.PI) / 6;
/** 1+1/8+1/27+… — cube reciprocal sum (no special-function name in UI) */
const CUBE_SUM = 1.202056903159594;
const ODD_SHARE = 7 / 8; // sum_{n odd} 1/n³ = (7/8) · full cube sum
const ODD_CUBE_TARGET = ODD_SHARE * CUBE_SUM;

function nestFromProd(prod: number): number {
  return (prod * Math.PI) ** 2 / 6;
}

function pegProduct(base: number, alpha: number, beta: number): number {
  return alpha * beta * Math.log(base);
}

function near(a: number, b: number, eps = 1e-8) {
  return Math.abs(a - b) < eps;
}

function oddEnough(x: number) {
  const r = Math.round(x);
  return Math.abs(x - r) < 1e-6 && Math.abs(r) % 2 === 1;
}

/** Partial sums */
function partialSquare(n: number) {
  let s = 0;
  for (let k = 1; k <= n; k++) s += 1 / (k * k);
  return s;
}
function partialCube(n: number) {
  let s = 0;
  for (let k = 1; k <= n; k++) s += 1 / (k * k * k);
  return s;
}
function partialCubeOdd(n: number) {
  let s = 0;
  for (let k = 1; k <= n; k += 2) s += 1 / (k * k * k);
  return s;
}
function partialCubeEven(n: number) {
  let s = 0;
  for (let k = 2; k <= n; k += 2) s += 1 / (k * k * k);
  return s;
}

const SPINE_ODDS = [1, 3, 5, 7, 9, 11] as const;

export function Analysis2Page() {
  const [spineIdx, setSpineIdx] = useState(0); // which beacon on the spine
  const [nTerms, setNTerms] = useState(5000);
  const [alpha, setAlpha] = useState(1);

  const odd = SPINE_ODDS[spineIdx];
  // Spine: base = e^odd, β = 1/odd / α  so α·β·ln(base)=1 when ln=odd
  // With free α: β = 1 / (α * odd), base = e^odd
  const base = Math.exp(odd);
  const beta = 1 / (alpha * odd);
  const prod = pegProduct(base, alpha, beta);
  const nest = nestFromProd(prod);

  const squarePartial = useMemo(() => partialSquare(nTerms), [nTerms]);
  const cubePartial = useMemo(() => partialCube(nTerms), [nTerms]);
  const cubeOddPartial = useMemo(() => partialCubeOdd(nTerms), [nTerms]);
  const cubeEvenPartial = useMemo(() => partialCubeEven(nTerms), [nTerms]);

  const nestGreen = near(nest, PI2_6, 1e-9);
  const pegGreen = oddEnough(prod);
  const splitRatio =
    cubePartial > 0 ? cubeOddPartial / cubePartial : 0;
  const splitGreen = Math.abs(splitRatio - ODD_SHARE) < 0.002;
  const oddTargetGreen =
    Math.abs(cubeOddPartial - ODD_CUBE_TARGET) < 0.01;

  const twoLock = nestGreen && pegGreen && splitGreen;

  // Spine probe: sequence of β or 1/odd³ along odds
  const spineProbe = useMemo(
    () =>
      SPINE_ODDS.map((o) => ({
        odd: o,
        beta: 1 / o,
        invOdd3: 1 / (o * o * o),
        base: Math.exp(o),
      })),
    []
  );

  return (
    <main className="page">
      <h1>Analysis 2 — two-observable lock</h1>
      <p className="lede">
        Observable A (nest): product-only even calibrator — green when{" "}
        <strong>(α·β·π·ln(base))² / 6 = π²/6</strong> on the beacon spine.
        Observable B (spine probe): the same odd integers that label e, e³, e⁵…
        also split the cube reciprocal sum —{" "}
        <strong>sum over odd n of 1/n³ = (7/8) · (1+1/8+1/27+…)</strong>.
        Two greens = hinge locked; still not a closed form.
      </p>

      <div
        className="value"
        style={{ color: twoLock ? "#1f4e79" : "#9a2f38" }}
      >
        {twoLock ? "TWO-LOCK GREEN" : "OPEN"}
      </div>
      <div className="expr">
        spine odd={odd} · base=e^{odd} · α={fmt(alpha, 3)} · β={fmt(beta, 4)} ·
        αβln={fmt(prod, 4)}
      </div>
      <div className="rule">
        A nest {nestGreen ? "green" : "red"} · A peg {pegGreen ? "green" : "red"}{" "}
        · B odd-share {splitGreen ? "green (~7/8)" : "climbing"}
      </div>

      <h2>Observable A — nest (flat on the spine)</h2>
      <div className="split-readout">
        <div>
          <div className="kv-label">structured nest</div>
          <div className="kv-value" style={{ fontSize: "1.05rem" }}>
            {fmt(nest, 6)}
          </div>
          <div className="hint">{nestGreen ? "= π²/6" : `want ${fmt(PI2_6, 6)}`}</div>
        </div>
        <div>
          <div className="kv-label">square sum to N</div>
          <div className="kv-value" style={{ fontSize: "1.05rem" }}>
            {fmt(squarePartial, 6)}
          </div>
        </div>
        <div>
          <div className="kv-label">π²/6</div>
          <div className="kv-value" style={{ fontSize: "1.05rem" }}>
            {fmt(PI2_6, 6)}
          </div>
        </div>
        <div>
          <div className="kv-label">base</div>
          <div className="kv-value" style={{ fontSize: "1.05rem" }}>
            e^{odd}
          </div>
          <div className="hint">≈ {fmt(base, 4)}</div>
        </div>
      </div>
      <p className="hint">
        Move along e → e³ → e⁵: nest stays put. That was the dig constraint —
        spine position is invisible to A.
      </p>

      <h2>Observable B — spine / odd split</h2>
      <div className="split-readout">
        <div>
          <div className="kv-label">cube sum to N</div>
          <div className="kv-value" style={{ fontSize: "1.05rem" }}>
            {fmt(cubePartial, 6)}
          </div>
          <div className="hint">target ≈ {fmt(CUBE_SUM, 6)}</div>
        </div>
        <div>
          <div className="kv-label">odd n only</div>
          <div className="kv-value" style={{ fontSize: "1.05rem" }}>
            {fmt(cubeOddPartial, 6)}
          </div>
          <div className="hint">(7/8) target ≈ {fmt(ODD_CUBE_TARGET, 6)}</div>
        </div>
        <div>
          <div className="kv-label">even n only</div>
          <div className="kv-value" style={{ fontSize: "1.05rem" }}>
            {fmt(cubeEvenPartial, 6)}
          </div>
          <div className="hint">(1/8) of full</div>
        </div>
        <div>
          <div className="kv-label">odd / full</div>
          <div className="kv-value" style={{ fontSize: "1.05rem" }}>
            {fmt(splitRatio, 6)}
          </div>
          <div className="hint">{splitGreen ? "≈ 7/8" : "want 0.875"}</div>
        </div>
      </div>

      <div className="panel">
        <div className="kv-label" style={{ marginBottom: "0.35rem" }}>
          spine beacon (odd = ln(base))
        </div>
        <div className="modes" style={{ display: "flex", gap: "0.4rem", flexWrap: "wrap" }}>
          {SPINE_ODDS.map((o, i) => (
            <button
              key={o}
              type="button"
              onClick={() => setSpineIdx(i)}
              style={{
                background: spineIdx === i ? "#1f4e79" : "#fffaf3",
                color: spineIdx === i ? "#fff" : "#1a1a1a",
                border: "1px solid #e2d8c8",
                borderRadius: 8,
                padding: "0.35rem 0.7rem",
                font: "inherit",
                cursor: "pointer",
              }}
            >
              e^{o}
            </button>
          ))}
        </div>

        <label className="row" style={{ marginTop: "0.9rem" }}>
          <span>α (trade against β; nest stays if product held)</span>
          <span>{fmt(alpha, 3)}</span>
        </label>
        <input
          type="range"
          min={0.25}
          max={4}
          step={0.01}
          value={alpha}
          onChange={(e) => setAlpha(parseFloat(e.target.value))}
        />

        <label className="row" style={{ marginTop: "0.8rem" }}>
          <span>sum terms N</span>
          <span>{nTerms}</span>
        </label>
        <input
          type="range"
          min={100}
          max={20000}
          step={100}
          value={nTerms}
          onChange={(e) => setNTerms(parseInt(e.target.value, 10))}
        />

        <h2 style={{ marginTop: "1.2rem" }}>Spine probe table</h2>
        <div style={{ overflowX: "auto" }}>
          <table
            style={{
              width: "100%",
              borderCollapse: "collapse",
              fontSize: "0.95rem",
            }}
          >
            <thead>
              <tr style={{ textAlign: "left", color: "#1f4e79" }}>
                <th style={{ padding: "0.3rem" }}>odd</th>
                <th style={{ padding: "0.3rem" }}>base</th>
                <th style={{ padding: "0.3rem" }}>β (α=1)</th>
                <th style={{ padding: "0.3rem" }}>1/odd³</th>
                <th style={{ padding: "0.3rem" }}>nest</th>
              </tr>
            </thead>
            <tbody>
              {spineProbe.map((row) => (
                <tr
                  key={row.odd}
                  style={{
                    background:
                      row.odd === odd ? "rgba(31,78,121,0.08)" : "transparent",
                  }}
                >
                  <td style={{ padding: "0.3rem" }}>{row.odd}</td>
                  <td style={{ padding: "0.3rem" }}>e^{row.odd}</td>
                  <td style={{ padding: "0.3rem" }}>{fmt(row.beta, 4)}</td>
                  <td style={{ padding: "0.3rem" }}>{fmt(row.invOdd3, 6)}</td>
                  <td style={{ padding: "0.3rem" }}>{fmt(PI2_6, 4)}</td>
                </tr>
              ))}
            </tbody>
          </table>
        </div>

        <p className="hint" style={{ marginTop: "1rem" }}>
          Read: A is blind to which spine beacon you’re on; B cares about odd vs
          even denominators in the cube sum — the same odd lattice. Two-lock
          green means both stories are on the table together. It does{" "}
          <em>not</em> mean we have (−i Ln(e^(iπ)))³ / something for the cube
          sum — only that the hinge is real enough to dig further.
        </p>
        <div className="actions">
          <button
            type="button"
            onClick={() => {
              setSpineIdx(0);
              setAlpha(1);
            }}
          >
            classical e¹
          </button>
          <button type="button" onClick={() => setSpineIdx(1)}>
            e³ hint
          </button>
          <button type="button" onClick={() => setSpineIdx(2)}>
            e⁵ hint
          </button>
        </div>
      </div>
    </main>
  );
}
