import { useMemo, useState } from "react";
import { fmt, fmtBase, baseFromSlider, sliderFromBase } from "../lib/format";

const PI2_6 = (Math.PI * Math.PI) / 6;

/**
 * Three-way lock inside the exponential:
 *   value = base^(α · i · β · π) = exp(α · i · β · π · ln(base))
 *
 * Do NOT casually collapse to a complex number then principal-Log.
 * Structured reading keeps the levers:
 *   Ln_struct(base^(α i β π)) := α · i · β · π · ln(base)
 *   nest = (−i · Ln_struct)² / 6 = (α · β · π · ln(base))² / 6
 *
 * Peg −1 ⇔ α·β·ln(base) is an odd integer (same as Lock pages).
 */

function nestStructured(base: number, alpha: number, beta: number): number {
  const u = Math.log(base);
  return (alpha * beta * Math.PI * u) ** 2 / 6;
}

/** Casual collapse: evaluate then principal atan2-log (loses full turns). */
function nestCollapsed(base: number, alpha: number, beta: number): {
  re: number;
  im: number;
} {
  const ang = alpha * beta * Math.PI * Math.log(base);
  const wRe = Math.cos(ang);
  const wIm = Math.sin(ang);
  const mod = Math.hypot(wRe, wIm);
  const lnRe = Math.log(mod);
  const lnIm = Math.atan2(wIm, wRe);
  // (−i)(lnRe + i lnIm) = lnIm - i lnRe
  const innerRe = lnIm;
  const innerIm = -lnRe;
  const sqRe = innerRe * innerRe - innerIm * innerIm;
  const sqIm = 2 * innerRe * innerIm;
  return { re: sqRe / 6, im: sqIm / 6 };
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

export function Analysis1Page() {
  const [t, setT] = useState(() => sliderFromBase(Math.E));
  const [alpha, setAlpha] = useState(1);
  const [beta, setBeta] = useState(1);
  const [nTerms, setNTerms] = useState(1000);

  const base = baseFromSlider(t);
  const prod = pegProduct(base, alpha, beta);
  const structured = nestStructured(base, alpha, beta);
  const collapsed = nestCollapsed(base, alpha, beta);

  const pegGreen = oddEnough(prod);
  const nestGreen = near(structured, PI2_6);
  const sum = useMemo(() => {
    let s = 0;
    for (let k = 1; k <= nTerms; k++) s += 1 / (k * k);
    return s;
  }, [nTerms]);
  const sumGreen = Math.abs(sum - PI2_6) < 0.002;

  // Three-way calibration: classical e, α=1, β=1
  const classical =
    near(base, Math.E, 1e-6) && near(alpha, 1) && near(beta, 1);
  const allGreen = pegGreen && nestGreen && sumGreen && classical;

  return (
    <main className="page">
      <h1>Analysis 1 — three-way lock</h1>
      <p className="lede">
        The exponential is <strong>base^(α · i · β · π)</strong> — three levers,
        not a casual collapse to −1. Structured nest keeps them:{" "}
        <strong>(−i Ln_struct(·))² / 6 = (α·β·π·ln(base))² / 6</strong>. Peg −1
        when α·β·ln(base) is odd. Compare the collapsed principal-Log reading
        (loses full turns) so we don’t treat the exponential too lightly.
      </p>

      <div
        className="value"
        style={{ color: allGreen ? "#1f4e79" : "#9a2f38" }}
      >
        {allGreen ? "GREEN" : pegGreen && nestGreen ? "OPEN" : "RED"}
      </div>
      <div className="expr">
        base={fmtBase(base)} · α={fmt(alpha, 3)} · β={fmt(beta, 3)} · αβln=
        {fmt(prod, 4)}
      </div>
      <div className="rule">
        {allGreen
          ? "three-way classical lock: peg −1, structured nest = π²/6, sum agrees"
          : pegGreen && nestGreen
            ? "peg and structured nest agree — not classical e/α/β=1 (deformation)"
            : "levers disagree or sum still climbing"}
      </div>

      <div className="split-readout">
        <div>
          <div className="kv-label">base</div>
          <div className="kv-value">{fmtBase(base)}</div>
        </div>
        <div>
          <div className="kv-label">α (i)</div>
          <div className="kv-value">{fmt(alpha, 4)}</div>
        </div>
        <div>
          <div className="kv-label">β (π)</div>
          <div className="kv-value">{fmt(beta, 4)}</div>
        </div>
        <div>
          <div className="kv-label">α·β·ln(base)</div>
          <div className="kv-value">{fmt(prod, 4)}</div>
          <div className="hint">{pegGreen ? "odd → −1" : "not odd"}</div>
        </div>
      </div>

      <div className="split-readout">
        <div>
          <div className="kv-label">structured nest</div>
          <div className="kv-value" style={{ fontSize: "1.05rem" }}>
            {fmt(structured, 6)}
          </div>
          <div className="hint">
            {nestGreen ? "π²/6" : `target ${fmt(PI2_6, 6)}`}
          </div>
        </div>
        <div>
          <div className="kv-label">collapsed Ln</div>
          <div className="kv-value" style={{ fontSize: "1.05rem" }}>
            {fmt(collapsed.re, 6)}
          </div>
          <div className="hint">principal value — can drop turns</div>
        </div>
        <div>
          <div className="kv-label">sum to N</div>
          <div className="kv-value" style={{ fontSize: "1.05rem" }}>
            {fmt(sum, 6)}
          </div>
        </div>
        <div>
          <div className="kv-label">π²/6</div>
          <div className="kv-value" style={{ fontSize: "1.05rem" }}>
            {fmt(PI2_6, 6)}
          </div>
        </div>
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
          Structured nest depends on the product α·β·ln(base). Same product ⇒
          same nest (three-way trade). Collapsed Ln(e^(i2π))=Ln(1)=0 is the
          casual mistake — it throws away the β lever after evaluating the
          exponential.
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
            classical e · α=1 · β=1
          </button>
          <button
            type="button"
            onClick={() => {
              setT(sliderFromBase(Math.E));
              setAlpha(1);
              setBeta(2);
            }}
          >
            β=2 (compare structured vs collapsed)
          </button>
          <button
            type="button"
            onClick={() => {
              setT(sliderFromBase(Math.E ** 3));
              setAlpha(1);
              setBeta(1 / 3);
            }}
          >
            base e³ · β=⅓ (same αβln=1)
          </button>
        </div>
      </div>
    </main>
  );
}
