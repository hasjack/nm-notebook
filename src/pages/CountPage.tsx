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
 * From the −1 peg: what i must do to get counting.
 * Peg: e^(iπ) = −1.
 * Counting with i: multiply by i each step → 4-cycle (quarter-turns).
 * Counting with −1: multiply by −1 → 2-cycle (parity).
 * Counting with n: the integer index itself on the alphabet spiral.
 */

type Mode = "i-clock" | "parity" | "n-on-spiral" | "keep-peg";

function mulI(re: number, im: number): { re: number; im: number } {
  // (re + i im) * i = -im + i re
  return { re: -im, im: re };
}

function fmtZ(re: number, im: number): string {
  if (Math.abs(im) < 1e-9) return fmt(re, 4);
  if (Math.abs(re) < 1e-9) return `${fmt(im, 4)} i`;
  return `${fmt(re, 4)}${im >= 0 ? " + " : " − "}${fmt(Math.abs(im), 4)} i`;
}

const LABELS = ["1", "i", "−1", "−i"] as const;

export function CountPage() {
  const [mode, setMode] = useState<Mode>("keep-peg");
  const [steps, setSteps] = useState(2); // start at peg: 1 * i^2 = -1
  const [nMax, setNMax] = useState(40);
  const [sigmaStep, setSigmaStep] = useState(1);
  const [keepN, setKeepN] = useState(30);

  // Start at 1, apply i `steps` times. steps=2 → -1 peg.
  const point = useMemo(() => {
    let re = 1;
    let im = 0;
    for (let k = 0; k < steps; k++) {
      const n = mulI(re, im);
      re = n.re;
      im = n.im;
    }
    return { re, im };
  }, [steps]);

  const onPeg =
    Math.abs(point.re + 1) < 1e-9 && Math.abs(point.im) < 1e-9;
  const seat = ((steps % 4) + 4) % 4;

  // Harmonic growth: step n adds 1/n; H_n = sum_{k=1}^n 1/k ≈ ln n + γ
  // To hold the −1 peg with base = e^(H_n) and β = 1: need α · H_n = odd.
  // Classical peg at n=1: H_1=1, α=1. As H_n grows, α must fall as odd/H_n ("i retunes").
  const keepPeg = useMemo(() => {
    let H = 0;
    const rows: {
      n: number;
      H: number;
      alpha: number;
      step: number;
      kappaH: number;
      kappaN: number;
    }[] = [];
    for (let n = 1; n <= keepN; n++) {
      const step = 1 / n;
      H += step;
      const alpha = 1 / H; // hold odd=1 peg: α·H=1
      // Falsify: circle curvature κ=1/R. Same dial as α only if R = H_n.
      const kappaH = 1 / H; // R = H_n  → must sit on α
      const kappaN = 1 / n; // R = n    → should break away from α
      rows.push({ n, H, alpha, step, kappaH, kappaN });
    }
    return rows;
  }, [keepN]);

  const falsify = useMemo(() => {
    let maxMatch = 0;
    let maxBreak = 0;
    let breakAt = 1;
    for (const r of keepPeg) {
      const dH = Math.abs(r.alpha - r.kappaH);
      const dN = Math.abs(r.alpha - r.kappaN);
      if (dH > maxMatch) maxMatch = dH;
      if (dN > maxBreak) {
        maxBreak = dN;
        breakAt = r.n;
      }
    }
    return { maxMatch, maxBreak, breakAt };
  }, [keepPeg]);

  const keepTraces: Data[] = useMemo(() => {
    const ns = keepPeg.map((r) => r.n);
    return [
      {
        type: "scatter",
        mode: "lines+markers",
        x: ns,
        y: keepPeg.map((r) => r.alpha),
        name: "α = 1/H_n (peg law)",
        line: { color: ORANGE, width: 3 },
        marker: { size: 8, symbol: "diamond" },
      },
      {
        type: "scatter",
        mode: "lines+markers",
        x: ns,
        y: keepPeg.map((r) => r.kappaH),
        name: "κ = 1/H_n (R = pile)",
        line: { color: NAVY, width: 2, dash: "dot" },
        marker: { size: 5 },
      },
      {
        type: "scatter",
        mode: "lines+markers",
        x: ns,
        y: keepPeg.map((r) => r.kappaN),
        name: "κ = 1/n (R = count) — breaks",
        line: { color: MAROON, width: 2 },
        marker: { size: 6 },
      },
    ];
  }, [keepPeg]);

  const layoutKeep: Partial<Layout> = {
    paper_bgcolor: CREAM,
    plot_bgcolor: PAPER,
    margin: { l: 50, r: 20, t: 44, b: 55 },
    title: {
      text: "Falsify: κ=1/R equals α?  R=H_n matches · R=n breaks",
      font: { size: 13, family: "Georgia, serif" },
    },
    xaxis: { title: { text: "n (count)" } },
    yaxis: { title: { text: "α and κ" }, rangemode: "tozero" },
    showlegend: true,
    legend: { orientation: "h", y: -0.22 },
    font: { family: "Georgia, Palatino, serif" },
  };

    const clock2d: Data[] = useMemo(() => {
    const th = Array.from({ length: 361 }, (_, i) => (i * Math.PI) / 180);
    const seats = [
      { re: 1, im: 0, label: "1" },
      { re: 0, im: 1, label: "i" },
      { re: -1, im: 0, label: "−1 peg" },
      { re: 0, im: -1, label: "−i" },
    ];
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
        mode: "markers+text",
        x: seats.map((s) => s.re),
        y: seats.map((s) => s.im),
        text: seats.map((s) => s.label),
        textposition: "top center",
        marker: { size: 10, color: NAVY },
        name: "count seats",
      },
      {
        type: "scatter",
        mode: "lines+markers",
        x: [0, point.re],
        y: [0, point.im],
        line: { color: MAROON, width: 3 },
        marker: { size: [0, 14], color: ORANGE },
        name: "now",
      },
    ];
  }, [point]);

  const spiral: Data[] = useMemo(() => {
    const ns = Array.from({ length: nMax }, (_, i) => i + 1);
    const pts = ns.map((n) => {
      const th = n * sigmaStep * Math.PI;
      return { x: n * Math.cos(th), y: n * Math.sin(th), n };
    });
    return [
      {
        type: "scatter",
        mode: "lines+markers",
        x: pts.map((p) => p.x),
        y: pts.map((p) => p.y),
        text: ns.map(String),
        name: "n · e^(i n σ π)",
        line: { color: "#c4b8a4", width: 1.5 },
        marker: { size: 6, color: NAVY },
        hovertemplate: "n=%{text}<extra></extra>",
      },
    ];
  }, [nMax, sigmaStep]);

  const layoutClock: Partial<Layout> = {
    paper_bgcolor: CREAM,
    plot_bgcolor: PAPER,
    margin: { l: 40, r: 20, t: 40, b: 40 },
    title: {
      text: "Counting with i — each step ×i (quarter-turn)",
      font: { size: 13, family: "Georgia, serif" },
    },
    xaxis: { range: [-1.5, 1.5], scaleanchor: "y", zeroline: true },
    yaxis: { range: [-1.5, 1.5], zeroline: true },
    showlegend: false,
    font: { family: "Georgia, Palatino, serif" },
  };

  const layoutSpiral: Partial<Layout> = {
    paper_bgcolor: CREAM,
    plot_bgcolor: PAPER,
    margin: { l: 40, r: 20, t: 40, b: 40 },
    title: {
      text: "Counting with n — integers on the alphabet spiral",
      font: { size: 13, family: "Georgia, serif" },
    },
    xaxis: { zeroline: true, scaleanchor: "y" },
    yaxis: { zeroline: true },
    showlegend: false,
    font: { family: "Georgia, Palatino, serif" },
  };

  return (
    <main className="page">
      <h1>Count — from the −1 peg</h1>
      <p className="lede">
        Peg first: <strong>e^(iπ) = −1</strong>. Keep-peg mode falsifies whether
        curvature κ = 1/R is the same dial as α. Match when R is the growth pile
        H_n; break when R is the bare count n. Also: ×i clock, −1 parity, n on
        spiral — optional pictures, not required for the lemma.
      </p>

      <div
        className="value"
        style={{ color: onPeg ? "#1f4e79" : "#9a2f38", fontSize: "1.3rem" }}
      >
        {mode === "i-clock"
          ? onPeg
            ? "ON PEG −1"
            : fmtZ(point.re, point.im)
          : mode === "parity"
            ? steps % 2 === 0
              ? "+1 (even count)"
              : "−1 peg (odd count)"
            : mode === "keep-peg"
              ? falsify.maxMatch < 1e-12
                ? "MATCH on R=H_n · BREAK on R=n"
                : "unexpected residual on R=H_n"
              : "n counts on e^(i n σ π)"}
      </div>
      <div className="expr">
        {mode === "i-clock"
          ? `1 · i^${steps} = ${fmtZ(point.re, point.im)} · seat ${LABELS[seat]}`
          : mode === "parity"
            ? `(e^(iπ))^${steps} = (−1)^${steps}`
            : mode === "keep-peg"
              ? `max|α−1/H_n|=${fmt(falsify.maxMatch, 6)} · max|α−1/n|=${fmt(falsify.maxBreak, 4)} at n=${falsify.breakAt} · last α=${fmt(keepPeg[keepPeg.length - 1].alpha, 4)}`
              : `integers 1…${nMax} on the spiral · σ = ${fmt(sigmaStep, 3)}`}
      </div>
      <div className="rule">
        peg is odd half-turns · i-count is mod 4 · real count is the index n
      </div>

      <div className="graph2d" style={{ height: 420 }}>
        <Plot
          data={
            mode === "n-on-spiral"
              ? spiral
              : mode === "keep-peg"
                ? keepTraces
                : clock2d
          }
          layout={
            mode === "n-on-spiral"
              ? layoutSpiral
              : mode === "keep-peg"
                ? layoutKeep
                : layoutClock
          }
          config={plotConfig}
          style={{ width: "100%", height: "100%" }}
          useResizeHandler
        />
      </div>

      <div className="panel">
        <div className="modes" style={{ display: "flex", gap: "0.4rem", flexWrap: "wrap" }}>
          {(
            [
              ["i-clock", "×i clock"],
              ["parity", "−1 parity"],
              ["n-on-spiral", "n on spiral"],
              ["keep-peg", "keep peg"],
            ] as const
          ).map(([id, label]) => (
            <button
              key={id}
              type="button"
              onClick={() => setMode(id)}
              style={{
                background: mode === id ? "#1f4e79" : "#fffaf3",
                color: mode === id ? "#fff" : "#1a1a1a",
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

        {(mode === "i-clock" || mode === "parity") && (
          <>
            <label className="row" style={{ marginTop: "0.8rem" }}>
              <span>{mode === "i-clock" ? "steps ×i" : "steps ×(−1)"}</span>
              <span>{steps}</span>
            </label>
            <input
              type="range"
              min={0}
              max={16}
              step={1}
              value={steps}
              onChange={(e) => setSteps(parseInt(e.target.value, 10))}
            />
            <div className="actions">
              <button type="button" onClick={() => setSteps(0)}>
                1 (start)
              </button>
              <button type="button" onClick={() => setSteps(1)}>
                i
              </button>
              <button type="button" onClick={() => setSteps(2)}>
                −1 peg
              </button>
              <button type="button" onClick={() => setSteps(3)}>
                −i
              </button>
              <button type="button" onClick={() => setSteps(4)}>
                return 1
              </button>
            </div>
          </>
        )}

        {mode === "n-on-spiral" && (
          <>
            <label className="row" style={{ marginTop: "0.8rem" }}>
              <span>N max</span>
              <span>{nMax}</span>
            </label>
            <input
              type="range"
              min={10}
              max={120}
              step={1}
              value={nMax}
              onChange={(e) => setNMax(parseInt(e.target.value, 10))}
            />
            <label className="row">
              <span>σ (π-units)</span>
              <span>{fmt(sigmaStep, 3)}</span>
            </label>
            <input
              type="range"
              min={0.05}
              max={2}
              step={0.01}
              value={sigmaStep}
              onChange={(e) => setSigmaStep(parseFloat(e.target.value))}
            />
            <div className="actions">
              <button type="button" onClick={() => setSigmaStep(1)}>
                σ = 1
              </button>
              <button type="button" onClick={() => setSigmaStep(0.5)}>
                σ = ½
              </button>
              <button type="button" onClick={() => setSigmaStep(2 / 5)}>
                σ = ⅖
              </button>
            </div>
          </>
        )}

        {mode === "keep-peg" && (
          <>
            <label className="row" style={{ marginTop: "0.8rem" }}>
              <span>count up to n</span>
              <span>{keepN}</span>
            </label>
            <input
              type="range"
              min={2}
              max={80}
              step={1}
              value={keepN}
              onChange={(e) => setKeepN(parseInt(e.target.value, 10))}
            />
            <p className="hint">
              Orange α is the peg law (α·H_n = 1). Navy dotted κ = 1/H_n uses the
              growth pile as radius — it must sit on orange (match). Maroon κ =
              1/n uses the count itself as radius — it pulls away (break). So
              “curvature of π” is a beacon for i only when R is the same pile
              that enters the peg, not when R is bare n.
            </p>
          </>
        )}

        <p className="hint">
          Start at steps = 2 on the ×i clock — that is the peg. Each further ×i
          is one count on a 4-hour clock. Parity mode is the knife alone: odd →
          peg, even → return. Spiral mode is counting as the integer n itself,
          written into e, i, π.
        </p>
      </div>

      <div className="catalogue-list" style={{ marginTop: "1rem" }}>
        <article className="catalogue-card grade-clean">
          <header className="catalogue-card-head">
            <h2>Falsification: κ beacon for i</h2>
            <span className="grade-pill grade-clean">lemma</span>
          </header>
          <p>
            Claim: curvature κ = 1/R equals the peg dial α. True when R = H_n
            (identity: α = 1/H_n = κ). False when R = n: |α − 1/n| grows with n
            because H_n ~ ln n + γ, not n. Curvature is a beacon for i only under
            the radius that actually sits in the peg product.
          </p>
        </article>
        <article className="catalogue-card grade-clean">
          <header className="catalogue-card-head">
            <h2>What i must do (turn count)</h2>
            <span className="grade-pill grade-clean">count</span>
          </header>
          <p>
            To get discrete counting on the plane, i has to act as a{" "}
            <strong>unit step of turn</strong>: each ×i is +1 on a clock of 4.
            Two steps hit the peg; four steps return. That is counting, with π
            fixing the size of a half-turn and e^(iθ) doing the move.
          </p>
        </article>
        <article className="catalogue-card grade-clean">
          <header className="catalogue-card-head">
            <h2>What i need not do</h2>
            <span className="grade-pill grade-clean">honest</span>
          </header>
          <p>
            i does not replace 1, 2, 3 on the real line. Real counting stays the
            index n (or H_N ≈ ln N + γ for additive growth). i counts{" "}
            <em>turns</em>. Peg −1 is where turn-count is odd (in half-turns).
          </p>
        </article>
        <article className="catalogue-card grade-calligraphy">
          <header className="catalogue-card-head">
            <h2>e · π · i · count</h2>
            <span className="grade-pill grade-calligraphy">NM</span>
          </header>
          <p>
            e grows, π measures the turn, i executes one tick, n is which tick.
            Your sentence from earlier — growth, curvature, complex plane vs
            number line — is this page in four letters.
          </p>
        </article>
      </div>
    </main>
  );
}
