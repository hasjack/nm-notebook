import { useMemo, useState } from "react";
import Plot from "../components/Plot";
import { fmt } from "../lib/format";
import {
  CREAM,
  MAROON,
  MUTED,
  NAVY,
  ORANGE,
  PAPER,
  plotConfig,
} from "../lib/plotTheme";
import type { Data, Layout } from "plotly.js";

/**
 * Rotation as a number line — turns of e^(i θ) with θ = t·π.
 * 0 and 1 as "back to where it started" (full turn / identity).
 */
const STOPS = [
  { t: 0, label: "0 · start", value: "1", note: "back to where it started" },
  { t: 0.5, label: "½ · quarter", value: "i", note: "up the i-axis" },
  { t: 1, label: "1 · half", value: "−1", note: "Euler landing" },
  { t: 1.5, label: "1½", value: "−i", note: "down the i-axis" },
  { t: 2, label: "2 · full", value: "1", note: "same as 0 — returned" },
] as const;

export function RotationPage() {
  const [t, setT] = useState(1);

  const ang = t * Math.PI;
  const re = Math.cos(ang);
  const im = Math.sin(ang);

  const nearest = STOPS.reduce((best, s) =>
    Math.abs(s.t - t) < Math.abs(best.t - t) ? s : best
  );

  const circle: Data[] = useMemo(() => {
    const th = Array.from({ length: 361 }, (_, i) => (i * Math.PI) / 180);
    return [
      {
        type: "scatter",
        mode: "lines",
        x: th.map((a) => Math.cos(a)),
        y: th.map((a) => Math.sin(a)),
        line: { color: MAROON, width: 2 },
        name: "unit circle",
      },
      {
        type: "scatter",
        mode: "markers+text",
        x: STOPS.map((s) => Math.cos(s.t * Math.PI)),
        y: STOPS.map((s) => Math.sin(s.t * Math.PI)),
        text: STOPS.map((s) => s.value),
        textposition: "top center",
        marker: { size: 9, color: NAVY },
        name: "landings",
      },
      {
        type: "scatter",
        mode: "markers",
        x: [re],
        y: [im],
        marker: { size: 12, color: ORANGE, symbol: "diamond" },
        name: "now",
      },
    ];
  }, [re, im]);

  const layout: Partial<Layout> = {
    paper_bgcolor: CREAM,
    plot_bgcolor: PAPER,
    margin: { l: 50, r: 30, t: 36, b: 45 },
    title: {
      text: "Rotation number line — e^(i · t · π)",
      font: { size: 13, family: "Georgia, serif" },
    },
    xaxis: {
      title: { text: "real" },
      range: [-1.4, 1.4],
      zeroline: true,
      scaleanchor: "y",
    },
    yaxis: { title: { text: "i piece" }, range: [-1.4, 1.4], zeroline: true },
    showlegend: false,
    font: { family: "Georgia, Palatino, serif" },
    annotations: [
      {
        x: 0,
        y: -1.25,
        text: "0 and 2 (and every even) are the same place — returned",
        showarrow: false,
        font: { size: 11, color: MUTED },
      },
    ],
  };

  return (
    <main className="page">
      <h1>Rotation — turns as a number line</h1>
      <p className="lede">
        Slide <strong>t</strong> in e^(i · t · π). Landings at 0, ½, 1, 1½, 2.
        In Natural Mathematics, <strong>0 and 1 (as full-cycle marks) mean the
        same character: back to where it started</strong> — t=0 and t=2 are the
        same point on the circle. That is not the mute at base→1; it is return.
      </p>

      <div className="value">
        {Math.abs(im) < 1e-8
          ? fmt(re, 4)
          : Math.abs(re) < 1e-8
            ? `${fmt(im, 4)} i`
            : `${fmt(re, 4)}${im >= 0 ? " + " : " − "}${fmt(Math.abs(im), 4)} i`}
      </div>
      <div className="expr">
        e ^ (i · {fmt(t, 3)} · π) · nearest {nearest.label}
      </div>
      <div className="rule">{nearest.note}</div>

      <div className="graph2d" style={{ height: 380 }}>
        <Plot
          data={circle}
          layout={layout}
          config={plotConfig}
          style={{ width: "100%", height: "100%" }}
          useResizeHandler
        />
      </div>

      <div className="panel">
        <label className="row">
          <span>t (half-turns)</span>
          <span>{fmt(t, 3)}</span>
        </label>
        <input
          type="range"
          min={0}
          max={2}
          step={0.01}
          value={t}
          onChange={(e) => setT(parseFloat(e.target.value))}
        />
        <div className="actions">
          {STOPS.map((s) => (
            <button key={s.t} type="button" onClick={() => setT(s.t)}>
              {s.label}
            </button>
          ))}
        </div>
        <div className="catalogue-list" style={{ marginTop: "1rem" }}>
          <article className="catalogue-card grade-clean">
            <header className="catalogue-card-head">
              <h2>Return — 0 ≡ full turn</h2>
              <span className="grade-pill grade-clean">NM character</span>
            </header>
            <p>
              t=0 and t=2 both read 1. In this world that is one character:{" "}
              <em>back to where it started</em>. Same for every even t. Distinct
              from the mute (base→1, phase cannot lock −1) and the wind
              (base→0, never settles).
            </p>
          </article>
        </div>
      </div>
    </main>
  );
}
