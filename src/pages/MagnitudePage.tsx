import { useMemo, useState } from "react";
import Plot from "../components/Plot";
import { baseFromSlider, fmt, fmtBase, sliderFromBase } from "../lib/format";
import { layout3dMag, plotConfig, traces3dMag } from "../lib/plotTheme";
import { magnitudeAt, resultAtMag } from "../lib/walk";

/**
 * Magnitude / singularities — Natural Mathematics characters.
 * base^(σ + α·i·βπ): σ grows/shrinks off the unit cylinder.
 */
export function MagnitudePage() {
  const [t, setT] = useState(() => sliderFromBase(Math.E));
  const [alpha, setAlpha] = useState(1);
  const [beta, setBeta] = useState(1);
  const [sigma, setSigma] = useState(0);

  const base = baseFromSlider(t);
  const product = alpha * beta;
  const mag = magnitudeAt(base, sigma);
  const value = resultAtMag(product, base, sigma);
  const nearOne = Math.abs(Math.log(base)) < 0.08;
  const nearZero = base < 0.08;

  const data3d = useMemo(
    () => traces3dMag(product, base, sigma),
    [product, base, sigma]
  );
  const layout = useMemo(() => {
    // scale view by mag at focus and at e^3-ish
    const r = Math.max(1.2, mag * 1.2, Math.pow(22, Math.abs(sigma)) * 0.15);
    return layout3dMag(Math.min(r, 8));
  }, [mag, sigma]);

  return (
    <main className="page">
      <h1>Magnitude — leave the unit cylinder</h1>
      <p className="lede">
        Full expression{" "}
        <strong>base^(σ + α · i · β · π)</strong>. The new dial σ is ordinary
        growth or decay: magnitude = base^σ. When σ = 0 you stay on the familiar
        unit cylinder. When σ ≠ 0 the ribbon swells or pinches — Natural
        Mathematics with amplitude, not only phase.
      </p>

      <div className="value">{value}</div>
      <div className="expr">
        {fmtBase(base)} ^ ({fmt(sigma, 2)} + {fmt(alpha, 2)} · i · {fmt(beta, 2)}{" "}
        π) · |value| = {fmt(mag, 4)}
      </div>
      <div className="rule">
        {sigma === 0
          ? "σ = 0 · unit cylinder (phase only)"
          : sigma > 0
            ? "σ > 0 · grows with base (outward spiral)"
            : "σ < 0 · shrinks as base grows (inward)"}
      </div>

      <div className="split-readout">
        <div>
          <div className="kv-label">σ (magnitude)</div>
          <div className="kv-value">{fmt(sigma, 3)}</div>
        </div>
        <div>
          <div className="kv-label">α (i)</div>
          <div className="kv-value">{fmt(alpha, 3)}</div>
        </div>
        <div>
          <div className="kv-label">β (π)</div>
          <div className="kv-value">{fmt(beta, 3)}</div>
        </div>
        <div>
          <div className="kv-label">base^σ</div>
          <div className="kv-value">{fmt(mag, 4)}</div>
        </div>
      </div>

      <div className="graph3d">
        <Plot
          data={data3d}
          layout={layout}
          config={plotConfig}
          style={{ width: "100%", height: "100%" }}
          useResizeHandler
        />
      </div>

      <div className="panel">
        <label className="row">
          <span>σ (real exponent / magnitude)</span>
          <span>{fmt(sigma, 3)}</span>
        </label>
        <input
          type="range"
          min={-1.5}
          max={1.5}
          step={0.01}
          value={sigma}
          onChange={(e) => setSigma(parseFloat(e.target.value))}
        />

        <label className="row" style={{ marginTop: "0.8rem" }}>
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

        <h2>Singularities as characters</h2>
        <div className="catalogue-list">
          <article
            className={`catalogue-card ${nearOne ? "grade-refuses" : "grade-clean"}`}
          >
            <header className="catalogue-card-head">
              <h2>The mute — base → 1</h2>
              <span className="grade-pill grade-refuses">dead lock</span>
            </header>
            <p>
              ln(1)=0. Phase freezes; no finite α,β can peg −1. Amplitude is
              1^σ = 1, so you sit still at 1 on the complex plane — a polite
              silence. The slider’s hole is this character’s stage direction.
            </p>
            {nearOne && (
              <p className="catalogue-beat">You are near the mute now.</p>
            )}
          </article>
          <article
            className={`catalogue-card ${nearZero ? "grade-calligraphy" : "grade-clean"}`}
          >
            <header className="catalogue-card-head">
              <h2>The wind — base → 0+</h2>
              <span className="grade-pill grade-calligraphy">0^i mood</span>
            </header>
            <p>
              Phase angle ∼ ln(base) → −∞: endless spin on (or off) the circle.
              With σ&gt;0, base^σ → 0 so the wind collapses into the origin; with
              σ&lt;0 it blows up; with σ=0 it is the pure 0^i unit wind — no
              landing.
            </p>
            {nearZero && (
              <p className="catalogue-beat">You are in the wind now.</p>
            )}
          </article>
          <article
            className={`catalogue-card ${Math.abs(sigma) < 1e-6 ? "grade-clean" : ""}`}
          >
            <header className="catalogue-card-head">
              <h2>The cylinder — σ = 0</h2>
              <span className="grade-pill grade-clean">phase only</span>
            </header>
            <p>
              Familiar e-walk ribbon: every value has length 1. Beacons and pegs
              live here. Switch σ off zero and the cylinder becomes a horn or a
              funnel — same angle story, new amplitude.
            </p>
            {Math.abs(sigma) < 1e-6 && (
              <p className="catalogue-beat">On the cylinder.</p>
            )}
          </article>
        </div>

        <div className="actions" style={{ marginTop: "1rem" }}>
          <button
            type="button"
            onClick={() => {
              setSigma(0);
              setT(sliderFromBase(Math.E));
              setAlpha(1);
              setBeta(1);
            }}
          >
            cylinder · Euler
          </button>
          <button type="button" onClick={() => setSigma(0.5)}>
            swell σ = ½
          </button>
          <button type="button" onClick={() => setSigma(-0.5)}>
            pinch σ = −½
          </button>
          <button
            type="button"
            onClick={() => {
              setSigma(0);
              setT(0.02);
            }}
          >
            toward the wind
          </button>
        </div>
      </div>
    </main>
  );
}
