import { useMemo, useState } from "react";
import { baseFromSlider, fmt, fmtBase, sliderFromBase } from "../lib/format";
import { fmtC, polilog, polilogContinued } from "../lib/polilog";

const PI2_6 = (Math.PI * Math.PI) / 6;
const CUBE = 1.202056903159594;

function near(a: number, b: number, eps = 1e-4) {
  return Math.abs(a - b) < eps;
}

/**
 * Analysis 5 — deform Li₂ / Li₃ with σ off the unit cylinder.
 * Star labels: −2 Li₂(e^(iπ)) and −(4/3) Li₃(e^(iπ)).
 */
export function Analysis5Page() {
  const [t, setT] = useState(() => sliderFromBase(Math.E));
  const [alpha, setAlpha] = useState(1);
  const [beta, setBeta] = useState(1);
  const [sigma, setSigma] = useState(0);
  const [nTerms, setNTerms] = useState(5000);
  const [continueMode, setContinueMode] = useState(true);

  const base = baseFromSlider(t);
  const ln = Math.log(base);
  const prod = alpha * beta * ln;
  // z = base^(σ + α i β π) = base^σ · exp(i π prod)
  const mag = base > 0 ? base ** sigma : 0;
  const ang = Math.PI * prod;
  const zRe = mag * Math.cos(ang);
  const zIm = mag * Math.sin(ang);

  const outsideDisk = mag > 1 + 1e-9;

  const li2 = useMemo(() => {
    if (continueMode) return polilogContinued(2, zRe, zIm, nTerms);
    if (outsideDisk) return { re: NaN, im: NaN, mode: "series" as const };
    return { ...polilog(2, zRe, zIm, nTerms), mode: "series" as const };
  }, [zRe, zIm, nTerms, continueMode, outsideDisk]);

  const li3 = useMemo(() => {
    if (continueMode) return polilogContinued(3, zRe, zIm, nTerms);
    if (outsideDisk) return { re: NaN, im: NaN, mode: "series" as const };
    return { ...polilog(3, zRe, zIm, nTerms), mode: "series" as const };
  }, [zRe, zIm, nTerms, continueMode, outsideDisk]);

  const height2 = -2 * li2.re;
  const height3 = -(4 / 3) * li3.re;
  const seriesBlocked = outsideDisk && !continueMode;

  const onPeg =
    near(sigma, 0) && near(zRe, -1, 1e-3) && near(zIm, 0, 1e-3);
  const h2Green = onPeg && near(height2, PI2_6, 0.015);
  const h3Green = onPeg && near(height3, CUBE, 0.025);

  return (
    <main className="page">
      <h1>Analysis 5 — σ off the peg</h1>
      <p className="lede">
        Same three levers as Analysis 3, plus Magnitude’s{" "}
        <strong>σ</strong>: z = base^(σ + α · i · β · π) so |z| = base^σ.
        Star costumes at the classical peg (σ = 0, z = −1):{" "}
        <strong>π²/6 = −2 Li₂(e^(iπ))</strong> and{" "}
        <strong>cube sum = −(4/3) Li₃(e^(iπ))</strong> — prefer that over the
        Apéry costume. Ask: does order 2 still lean toward π under σ? Does
        order 3 join {"{e, i, π}"}?
      </p>

      <div
        className="value"
        style={{
          color: seriesBlocked
            ? "#9a2f38"
            : onPeg
              ? "#1f4e79"
              : outsideDisk
                ? "#c45c26"
                : "#9a2f38",
          fontSize: "1.35rem",
        }}
      >
        {seriesBlocked
          ? "OUTSIDE DISK · series undefined"
          : outsideDisk && continueMode
            ? "CONTINUED · |z|>1"
            : onPeg
              ? "−(4/3) Li₃(e^(iπ)) · ON PEG"
              : "−(4/3) Re Li₃(z) · deformed"}
      </div>
      <div className="expr">
        twin −2 Li₂ · z ≈ {fmt(zRe, 4)}
        {zIm >= 0 ? " + " : " − "}
        {fmt(Math.abs(zIm), 4)} i · |z| = {fmt(mag, 4)}
      </div>
      <div className="rule">
        prod αβln = {fmt(prod, 4)} · σ = {fmt(sigma, 3)} · |z| = {fmt(mag, 4)}
        {seriesBlocked
          ? " · series blocked"
          : li3.mode === "continued"
            ? " · inversion continuation"
            : near(sigma, 0)
              ? " · cylinder · series"
              : " · inside disk · series"}
      </div>

      <div className="split-readout">
        <div>
          <div className="kv-label">base</div>
          <div className="kv-value">{fmtBase(base)}</div>
        </div>
        <div>
          <div className="kv-label">α</div>
          <div className="kv-value">{fmt(alpha, 3)}</div>
        </div>
        <div>
          <div className="kv-label">β</div>
          <div className="kv-value">{fmt(beta, 3)}</div>
        </div>
        <div>
          <div className="kv-label">σ</div>
          <div className="kv-value">{fmt(sigma, 3)}</div>
        </div>
      </div>

      <div className="split-readout">
        <div>
          <div className="kv-label">Li₂(z)</div>
          <div className="kv-value" style={{ fontSize: "0.95rem" }}>
            {fmtC(li2, 4)}
          </div>
        </div>
        <div>
          <div className="kv-label">−2 Re Li₂</div>
          <div
            className="kv-value"
            style={{ fontSize: "0.95rem", color: h2Green ? "#1f4e79" : undefined }}
          >
            {seriesBlocked || !Number.isFinite(height2) ? "—" : fmt(height2, 5)}
          </div>
          <div className="hint">
            {seriesBlocked
              ? "need |z|≤1 or continuation"
              : h2Green
                ? "π²/6 ✓"
                : `π²/6 = ${fmt(PI2_6, 5)}`}
          </div>
        </div>
        <div>
          <div className="kv-label">Li₃(z)</div>
          <div className="kv-value" style={{ fontSize: "0.95rem" }}>
            {fmtC(li3, 4)}
          </div>
        </div>
        <div>
          <div className="kv-label">−(4/3) Re Li₃</div>
          <div
            className="kv-value"
            style={{
              fontSize: "1.05rem",
              color: h3Green ? "#1f4e79" : "#9a2f38",
              fontWeight: 600,
            }}
          >
            {seriesBlocked || !Number.isFinite(height3) ? "—" : fmt(height3, 5)}
          </div>
          <div className="hint">
            {seriesBlocked
              ? "need |z|≤1 or continuation"
              : h3Green
                ? "cube sum ✓"
                : `cube ≈ ${fmt(CUBE, 5)}`}
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
        <label className="row">
          <span>α (i-factor)</span>
          <span>{fmt(alpha, 3)}</span>
        </label>
        <input
          type="range"
          min={0.05}
          max={3}
          step={0.01}
          value={alpha}
          onChange={(e) => setAlpha(parseFloat(e.target.value))}
        />
        <label className="row">
          <span>β (π-factor)</span>
          <span>{fmt(beta, 3)}</span>
        </label>
        <input
          type="range"
          min={0.05}
          max={3}
          step={0.01}
          value={beta}
          onChange={(e) => setBeta(parseFloat(e.target.value))}
        />
        <label className="row">
          <span>σ (magnitude)</span>
          <span>{fmt(sigma, 3)}</span>
        </label>
        <input
          type="range"
          min={-1.5}
          max={1.5}
          step={0.02}
          value={sigma}
          onChange={(e) => setSigma(parseFloat(e.target.value))}
        />
        <label className="row">
          <span>polilog terms</span>
          <span>{nTerms}</span>
        </label>
        <input
          type="range"
          min={500}
          max={12000}
          step={500}
          value={nTerms}
          onChange={(e) => setNTerms(parseInt(e.target.value, 10))}
        />

        
        <label className="row" style={{ marginTop: "0.6rem" }}>
          <span>Analytic continuation (|z|&gt;1)</span>
          <select
            value={continueMode ? "on" : "off"}
            onChange={(e) => setContinueMode(e.target.value === "on")}
          >
            <option value="on">on — inversion formulas</option>
            <option value="off">off — series only (fence)</option>
          </select>
        </label>

        <div className="actions">
          <button
            type="button"
            onClick={() => {
              setT(sliderFromBase(Math.E));
              setAlpha(1);
              setBeta(1);
              setSigma(0);
            }}
          >
            peg · Euler
          </button>
          <button
            type="button"
            onClick={() => {
              setT(sliderFromBase(Math.exp(3)));
              setAlpha(1);
              setBeta(1 / 3);
              setSigma(0);
            }}
          >
            peg · e³
          </button>
          <button
            type="button"
            onClick={() => {
              setT(sliderFromBase(Math.E));
              setAlpha(1);
              setBeta(1);
              setSigma(0.25);
            }}
          >
            σ = 0.25 (continue)
          </button>
          <button
            type="button"
            onClick={() => {
              setT(sliderFromBase(Math.E));
              setAlpha(1);
              setBeta(1);
              setSigma(-0.25);
            }}
          >
            σ = −0.25
          </button>

          <button
            type="button"
            onClick={() => {
              setT(sliderFromBase(Math.exp(3)));
              setAlpha(1.5);
              setBeta(2);
              setSigma(0);
            }}
          >
            peg · e³ · 1½ · 2
          </button>
          <button
            type="button"
            onClick={() => {
              setT(sliderFromBase(Math.exp(3)));
              setAlpha(2);
              setBeta(1.5);
              setSigma(0);
            }}
          >
            peg · e³ · 2 · 1½
          </button>
          <button
            type="button"
            onClick={() => {
              setT(sliderFromBase(Math.E));
              setAlpha(1);
              setBeta(1.15);
              setSigma(0);
            }}
          >
            angle nudge
          </button>
        </div>
        <p className="hint">
          Series for |z| ≤ 1; past the knife, inversion continuation (toggle above).
          Same peg z = −1 whenever α·β·ln(base) is an odd integer — Euler, e³ with
          β = ⅓, or your e³ · α = 1.5 · β = 2 (prod = 9). Twin costumes light together.
          Return check: even prod → +1; odd → −1.
        </p>
      </div>

      <div className="catalogue-list" style={{ marginTop: "1rem" }}>
        <article className="catalogue-card grade-clean">
          <header className="catalogue-card-head">
            <h2>−(4/3) Li₃(e^(iπ))</h2>
            <span className="grade-pill grade-clean">star</span>
          </header>
          <p>
            Cube height on the peg in the same alphabet costume as the Basel
            nest. Cute, tight, and nicer than the Apéry mess — keep it as the
            public face of this height.
          </p>
        </article>
        <article className="catalogue-card grade-calligraphy">
          <header className="catalogue-card-head">
            <h2>What to watch</h2>
            <span className="grade-pill grade-calligraphy">honest</span>
          </header>
          <p>
            Continuation lets σ &gt; 0 speak; it does not invent an alphabet exit
            for order 3. Order 2 can still lean toward π; −(4/3) Li₃ stays the
            cute costume. Crossing |z| = 1 is another twofold cut — series vs
            continued — nature’s knife again.
          </p>
        </article>
      </div>
    </main>
  );
}
