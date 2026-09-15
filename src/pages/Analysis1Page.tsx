import { useMemo, useState } from "react";
import { fmt } from "../lib/format";

const PI2_6 = (Math.PI * Math.PI) / 6;

/** Principal complex log via Math — for a+ib on the principal branch. */
function clogs(re: number, im: number): { re: number; im: number } {
  const mod = Math.hypot(re, im);
  return { re: Math.log(mod), im: Math.atan2(im, re) };
}

function cexp(re: number, im: number): { re: number; im: number } {
  const e = Math.exp(re);
  return { re: e * Math.cos(im), im: e * Math.sin(im) };
}

function cmul(
  a: { re: number; im: number },
  b: { re: number; im: number }
): { re: number; im: number } {
  return {
    re: a.re * b.re - a.im * b.im,
    im: a.re * b.im + a.im * b.re,
  };
}

function csquare(z: { re: number; im: number }) {
  return cmul(z, z);
}

/** Angle A: e^(i · β · π) */
function peg(beta: number) {
  return cexp(0, beta * Math.PI);
}

/** Angle B: (−i Ln(e^(i β π)))² / 6 */
function nest(beta: number) {
  const w = peg(beta);
  const ln = clogs(w.re, w.im);
  const minusI = { re: 0, im: -1 };
  const inner = cmul(minusI, ln);
  const sq = csquare(inner);
  return { re: sq.re / 6, im: sq.im / 6 };
}

function partialSquareSum(n: number): number {
  let s = 0;
  for (let k = 1; k <= n; k++) s += 1 / (k * k);
  return s;
}

function near(a: number, b: number, eps = 1e-9) {
  return Math.abs(a - b) < eps;
}

export function Analysis1Page() {
  const [beta, setBeta] = useState(1);
  const [nTerms, setNTerms] = useState(1000);

  const A = useMemo(() => peg(beta), [beta]);
  const B = useMemo(() => nest(beta), [beta]);
  const C = useMemo(() => partialSquareSum(nTerms), [nTerms]);

  const aGreen = near(A.re, -1, 1e-8) && near(A.im, 0, 1e-8);
  const bGreen =
    near(B.re, PI2_6, 1e-8) && near(B.im, 0, 1e-8);
  const cGreen = Math.abs(C - PI2_6) < 0.002;
  // full calibration green only at classical β=1 (or odd integers with care)
  const allGreen = aGreen && bGreen && cGreen;

  return (
    <main className="page">
      <h1>Analysis 1 — calibrate on the even</h1>
      <p className="lede">
        Three angles must agree before we touch odd reciprocal-power sums. Peg{" "}
        <strong>e^(iπ) = −1</strong>, nest{" "}
        <strong>(−i Ln(e^(iπ)))² / 6</strong>, and the plain sum{" "}
        <strong>1+1/4+1/9+…</strong>. Green only when they line up. Twist the
        π-factor dial to see where principal Ln breaks the nest.
      </p>

      <div
        className="value"
        style={{ color: allGreen ? "#1f4e79" : "#9a2f38" }}
      >
        {allGreen ? "GREEN" : "RED"}
      </div>
      <div className="expr">
        analysis 1 · β = {fmt(beta, 3)} · N = {nTerms}
      </div>
      <div className="rule">
        {allGreen
          ? "peg, nest, and sum agree — safe to deform later"
          : "disagreement — dial left the classical calibration point (or sum still climbing)"}
      </div>

      <div className="split-readout">
        <div>
          <div className="kv-label">A · peg e^(iβπ)</div>
          <div className="kv-value" style={{ fontSize: "1rem" }}>
            {fmt(A.re, 4)}
            {A.im >= 0 ? " + " : " − "}
            {fmt(Math.abs(A.im), 4)} i
          </div>
          <div className="hint">{aGreen ? "green (−1)" : "not −1"}</div>
        </div>
        <div>
          <div className="kv-label">B · nest / 6</div>
          <div className="kv-value" style={{ fontSize: "1rem" }}>
            {fmt(B.re, 6)}
          </div>
          <div className="hint">
            {bGreen ? "green (π²/6)" : `target ${fmt(PI2_6, 6)}`}
          </div>
        </div>
        <div>
          <div className="kv-label">C · sum to N</div>
          <div className="kv-value" style={{ fontSize: "1rem" }}>
            {fmt(C, 6)}
          </div>
          <div className="hint">
            {cGreen ? "near π²/6" : `err ${fmt(PI2_6 - C, 6)}`}
          </div>
        </div>
        <div>
          <div className="kv-label">π²/6</div>
          <div className="kv-value" style={{ fontSize: "1rem" }}>
            {fmt(PI2_6, 6)}
          </div>
        </div>
      </div>

      <div className="panel">
        <label className="row">
          <span>π-factor β in e^(i β π)</span>
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
          <span>sum terms N</span>
          <span>{nTerms}</span>
        </label>
        <input
          type="range"
          min={10}
          max={5000}
          step={10}
          value={nTerms}
          onChange={(e) => setNTerms(parseInt(e.target.value, 10))}
        />
        <p className="hint">
          Finding: at β = 1, A = −1 and B = π²/6 (green). At β = 2, e^(i2π) = 1
          and principal Ln(1) = 0, so the nest collapses to 0 — not 4·π²/6. The
          dial is branch-aware; calibration is at the half-turn, not every
          full turn.
        </p>
        <div className="actions">
          <button type="button" onClick={() => setBeta(1)}>
            β = 1 (calibrate)
          </button>
          <button type="button" onClick={() => setBeta(2)}>
            β = 2 (branch trap)
          </button>
          <button type="button" onClick={() => setBeta(0.5)}>
            β = ½
          </button>
        </div>
      </div>
    </main>
  );
}
