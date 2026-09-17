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
 * Physics-adjacent Natural Mathematics.
 * Same alphabet {e, i, π}: a tone is Re(e^(i · ω · t)), a full period is return,
 * two tones interfere. Not new physics — the walk’s language on waves.
 */

type Scene = "tone" | "beat" | "phasor" | "damped";

export function PhysicsPage() {
  const [scene, setScene] = useState<Scene>("tone");
  const [omega, setOmega] = useState(1); // in units of π: phase = omega * π * t
  const [omega2, setOmega2] = useState(1.2);
  const [tNow, setTNow] = useState(0.25);
  const [gamma, setGamma] = useState(0.15); // damping in amplitude e^(-γ t)

  const N = 400;
  const tMax = 6;

  const tone: Data[] = useMemo(() => {
    const ts = Array.from({ length: N }, (_, i) => (i / (N - 1)) * tMax);
    const re = ts.map((t) => Math.cos(omega * Math.PI * t));
    const im = ts.map((t) => Math.sin(omega * Math.PI * t));
    return [
      {
        type: "scatter",
        mode: "lines",
        x: ts,
        y: re,
        name: "Re = cos(ω π t)",
        line: { color: MAROON, width: 2.5 },
      },
      {
        type: "scatter",
        mode: "lines",
        x: ts,
        y: im,
        name: "Im = sin(ω π t)",
        line: { color: NAVY, width: 1.5, dash: "dot" },
      },
      {
        type: "scatter",
        mode: "markers",
        x: [tNow],
        y: [Math.cos(omega * Math.PI * tNow)],
        marker: { size: 11, color: ORANGE, symbol: "diamond" },
        name: "now",
        showlegend: false,
      },
    ];
  }, [omega, tNow]);

  const beat: Data[] = useMemo(() => {
    const ts = Array.from({ length: N }, (_, i) => (i / (N - 1)) * tMax);
    const y = ts.map(
      (t) =>
        Math.cos(omega * Math.PI * t) + Math.cos(omega2 * Math.PI * t)
    );
    const env = ts.map((t) => {
      const a = 2 * Math.cos(((omega - omega2) * Math.PI * t) / 2);
      return Math.abs(a);
    });
    return [
      {
        type: "scatter",
        mode: "lines",
        x: ts,
        y,
        name: "sum of two tones",
        line: { color: MAROON, width: 2 },
      },
      {
        type: "scatter",
        mode: "lines",
        x: ts,
        y: env,
        name: "|beat envelope|",
        line: { color: NAVY, width: 1.5, dash: "dash" },
      },
      {
        type: "scatter",
        mode: "lines",
        x: ts,
        y: env.map((v) => -v),
        name: "−envelope",
        line: { color: NAVY, width: 1.5, dash: "dash" },
        showlegend: false,
      },
    ];
  }, [omega, omega2]);

  const phasor: Data[] = useMemo(() => {
    const th = Array.from({ length: 361 }, (_, i) => (i * Math.PI) / 180);
    const ang = omega * Math.PI * tNow;
    const re = Math.cos(ang);
    const im = Math.sin(ang);
    return [
      {
        type: "scatter",
        mode: "lines",
        x: th.map((a) => Math.cos(a)),
        y: th.map((a) => Math.sin(a)),
        line: { color: MUTED, width: 1 },
        name: "unit circle",
        hoverinfo: "skip",
      },
      {
        type: "scatter",
        mode: "lines+markers",
        x: [0, re],
        y: [0, im],
        line: { color: MAROON, width: 3 },
        marker: { size: [0, 12], color: ORANGE },
        name: "phasor e^(i ω π t)",
      },
      {
        type: "scatter",
        mode: "lines",
        x: [re, re],
        y: [0, im],
        line: { color: NAVY, width: 1, dash: "dot" },
        name: "Im drop",
        showlegend: false,
      },
      {
        type: "scatter",
        mode: "lines",
        x: [0, re],
        y: [0, 0],
        line: { color: NAVY, width: 1, dash: "dot" },
        name: "Re",
        showlegend: false,
      },
    ];
  }, [omega, tNow]);

  const damped: Data[] = useMemo(() => {
    const ts = Array.from({ length: N }, (_, i) => (i / (N - 1)) * tMax);
    const re = ts.map(
      (t) => Math.exp(-gamma * t) * Math.cos(omega * Math.PI * t)
    );
    const env = ts.map((t) => Math.exp(-gamma * t));
    return [
      {
        type: "scatter",
        mode: "lines",
        x: ts,
        y: re,
        name: "e^(−γt) cos(ω π t)",
        line: { color: MAROON, width: 2.5 },
      },
      {
        type: "scatter",
        mode: "lines",
        x: ts,
        y: env,
        name: "envelope e^(−γt)",
        line: { color: NAVY, width: 1.5, dash: "dash" },
      },
      {
        type: "scatter",
        mode: "lines",
        x: ts,
        y: env.map((v) => -v),
        line: { color: NAVY, width: 1.5, dash: "dash" },
        showlegend: false,
      },
    ];
  }, [omega, gamma]);

  const data =
    scene === "tone"
      ? tone
      : scene === "beat"
        ? beat
        : scene === "phasor"
          ? phasor
          : damped;

  const layout: Partial<Layout> = useMemo(() => {
    if (scene === "phasor") {
      return {
        paper_bgcolor: CREAM,
        plot_bgcolor: PAPER,
        margin: { l: 50, r: 30, t: 40, b: 45 },
        title: {
          text: "Phasor — same circle as Rotation",
          font: { size: 13, family: "Georgia, serif" },
        },
        xaxis: {
          title: { text: "real" },
          range: [-1.35, 1.35],
          scaleanchor: "y",
          zeroline: true,
        },
        yaxis: {
          title: { text: "i piece" },
          range: [-1.35, 1.35],
          zeroline: true,
        },
        showlegend: true,
        legend: { orientation: "h", y: -0.15 },
        font: { family: "Georgia, Palatino, serif" },
      };
    }
    return {
      paper_bgcolor: CREAM,
      plot_bgcolor: PAPER,
      margin: { l: 50, r: 30, t: 40, b: 45 },
      title: {
        text:
          scene === "tone"
            ? "One tone — Re and Im of e^(i ω π t)"
            : scene === "beat"
              ? "Two tones — interference / beat"
              : "Damped tone — amplitude e^(−γ t) (cousin of Magnitude σ)",
        font: { size: 13, family: "Georgia, serif" },
      },
      xaxis: { title: { text: "t" }, zeroline: false },
      yaxis: { title: { text: "amplitude" }, zeroline: true },
      showlegend: true,
      legend: { orientation: "h", y: -0.18 },
      font: { family: "Georgia, Palatino, serif" },
    };
  }, [scene]);

  // Period for return: ω π T = 2π ⇒ T = 2/ω (when ω≠0)
  const period = Math.abs(omega) > 1e-9 ? 2 / Math.abs(omega) : Infinity;
  const phaseNow = omega * Math.PI * tNow;
  const reNow = Math.cos(phaseNow);
  const imNow = Math.sin(phaseNow);

  return (
    <main className="page">
      <h1>Physics-adjacent — waves in the alphabet</h1>
      <p className="lede">
        A tone is already{" "}
        <strong>
          e<sup>i · ω · π · t</sup>
        </strong>
        . That is the same lettering as the walk and Rotation — not a costume
        change on Maxwell, just Natural Mathematics noticing that oscillators
        speak {`{e, i, π}`} for free. Period T = 2/ω (in these units) is the{" "}
        <em>return</em> character again.
      </p>

      <div className="value">
        {scene === "damped"
          ? `${fmt(Math.exp(-gamma * tNow) * reNow, 4)}`
          : scene === "beat"
            ? fmt(
                Math.cos(omega * Math.PI * tNow) +
                  Math.cos(omega2 * Math.PI * tNow),
                4
              )
            : Math.abs(imNow) < 1e-8
              ? fmt(reNow, 4)
              : Math.abs(reNow) < 1e-8
                ? `${fmt(imNow, 4)} i`
                : `${fmt(reNow, 4)}${imNow >= 0 ? " + " : " − "}${fmt(Math.abs(imNow), 4)} i`}
      </div>
      <div className="expr">
        {scene === "damped"
          ? `e^(−${fmt(gamma, 2)} t) · e^(i · ${fmt(omega, 2)} · π · t)`
          : scene === "beat"
            ? `e^(i ${fmt(omega, 2)} π t) + e^(i ${fmt(omega2, 2)} π t)  ·  look at Re`
            : `e^(i · ${fmt(omega, 2)} · π · t)`}
      </div>
      <div className="rule">
        period for return ≈ {Number.isFinite(period) ? fmt(period, 3) : "∞"} ·
        ω in units of π (phase = ω π t)
      </div>

      <div className="graph2d" style={{ height: 400 }}>
        <Plot
          data={data}
          layout={layout}
          config={plotConfig}
          style={{ width: "100%", height: "100%" }}
          useResizeHandler
        />
      </div>

      <div className="panel">
        <div className="modes" style={{ display: "flex", gap: "0.4rem", flexWrap: "wrap" }}>
          {(
            [
              ["tone", "One tone"],
              ["phasor", "Phasor"],
              ["beat", "Two tones"],
              ["damped", "Damped"],
            ] as const
          ).map(([id, label]) => (
            <button
              key={id}
              type="button"
              onClick={() => setScene(id)}
              style={{
                background: scene === id ? "#1f4e79" : "#fffaf3",
                color: scene === id ? "#fff" : "#1a1a1a",
                border: "1px solid #e2d8c8",
                borderRadius: 8,
                padding: "0.35rem 0.75rem",
                font: "inherit",
                cursor: "pointer",
              }}
            >
              {label}
            </button>
          ))}
        </div>

        <label className="row" style={{ marginTop: "0.9rem" }}>
          <span>ω (in π-units)</span>
          <span>{fmt(omega, 3)}</span>
        </label>
        <input
          type="range"
          min={0.25}
          max={4}
          step={0.05}
          value={omega}
          onChange={(e) => setOmega(parseFloat(e.target.value))}
        />

        {(scene === "tone" || scene === "phasor" || scene === "damped") && (
          <>
            <label className="row">
              <span>t now</span>
              <span>{fmt(tNow, 3)}</span>
            </label>
            <input
              type="range"
              min={0}
              max={tMax}
              step={0.02}
              value={tNow}
              onChange={(e) => setTNow(parseFloat(e.target.value))}
            />
          </>
        )}

        {scene === "beat" && (
          <>
            <label className="row">
              <span>ω₂ (second tone)</span>
              <span>{fmt(omega2, 3)}</span>
            </label>
            <input
              type="range"
              min={0.25}
              max={4}
              step={0.05}
              value={omega2}
              onChange={(e) => setOmega2(parseFloat(e.target.value))}
            />
            <p className="hint">
              Beat rate tracks |ω − ω₂|/2. Same alphabet, two clocks — interference
              without leaving {`{e, i, π}`}.
            </p>
          </>
        )}

        {scene === "damped" && (
          <>
            <label className="row">
              <span>γ (decay)</span>
              <span>{fmt(gamma, 3)}</span>
            </label>
            <input
              type="range"
              min={0}
              max={1.2}
              step={0.02}
              value={gamma}
              onChange={(e) => setGamma(parseFloat(e.target.value))}
            />
            <p className="hint">
              Amplitude e^(−γ t) is the time cousin of Magnitude’s base^σ. One dial
              shrinks the ribbon off the cylinder; here it pinches the wave.
            </p>
          </>
        )}

        <div className="actions" style={{ marginTop: "0.75rem" }}>
          <button type="button" onClick={() => { setOmega(1); setTNow(0); }}>
            ω=1 · start
          </button>
          <button type="button" onClick={() => { setOmega(1); setTNow(1); }}>
            half-turn (t=1)
          </button>
          <button type="button" onClick={() => { setOmega(1); setTNow(2); }}>
            return (t=2)
          </button>
          <button
            type="button"
            onClick={() => {
              setOmega(1);
              setOmega2(1.15);
              setScene("beat");
            }}
          >
            slow beat
          </button>
        </div>
      </div>

      <div className="catalogue-list" style={{ marginTop: "1.2rem" }}>
        <article className="catalogue-card grade-clean">
          <header className="catalogue-card-head">
            <h2>Shared spine with the walk</h2>
            <span className="grade-pill grade-clean">NM</span>
          </header>
          <p>
            Walk uses base^(α i β π). Freeze the base at e and read the exponent’s
            angular piece as time: you are watching a phasor. Physics didn’t invent
            a second alphabet — it borrowed this one.
          </p>
          <p className="catalogue-beat">
            Video beat: cut from the 3D ribbon to the unit-circle arrow — same e^(iθ).
          </p>
        </article>
        <article className="catalogue-card grade-clean">
          <header className="catalogue-card-head">
            <h2>Return is a period</h2>
            <span className="grade-pill grade-clean">character</span>
          </header>
          <p>
            When ω π T = 2π, T = 2/ω — you are back where you started. That is the
            same Return character as Rotation (t=0 ≡ t=2). Frequency is how often
            return happens.
          </p>
        </article>
        <article className="catalogue-card grade-calligraphy">
          <header className="catalogue-card-head">
            <h2>What this is not</h2>
            <span className="grade-pill grade-calligraphy">honest</span>
          </header>
          <p>
            Not a claim that e, i, π solve QFT. It is a teaching frame: waves,
            beats, and damping already live in the explorer’s letters. Keep company
            and token separate — and keep physics-adjacent NM in the open-notebook
            tone.
          </p>
        </article>
      </div>
    </main>
  );
}
