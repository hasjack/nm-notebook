import { useMemo, useState } from "react";
import Plot from "../components/Plot";
import {
  CREAM,
  MAROON,
  NAVY,
  ORANGE,
  PAPER,
  plotConfig,
} from "../lib/plotTheme";
import type { Data, Layout } from "plotly.js";

const BRAID_PRIMES = [2, 3, 5, 7, 11, 13] as const;
const COLORS = ["#1f4e79", "#9a2f38", "#c45c26", "#2f6b4f", "#6b4f8a", "#7a7468"];

function isPrime(n: number): boolean {
  if (n < 2) return false;
  if (n % 2 === 0) return n === 2;
  const lim = Math.floor(Math.sqrt(n));
  for (let d = 3; d <= lim; d += 2) {
    if (n % d === 0) return false;
  }
  return true;
}

/** Archimedean in xy; vertical is the integer itself. */
function xyz(n: number, step: number): { x: number; y: number; z: number } {
  const th = n * step;
  return { x: n * Math.cos(th), y: n * Math.sin(th), z: n };
}

function xy(n: number, step: number): { x: number; y: number } {
  const th = n * step;
  return { x: n * Math.cos(th), y: n * Math.sin(th) };
}

/**
 * Prime braids — 2D or 3D (rotate; vertical = n).
 * 2 plays nice; 3 jams.
 */
export function PrimesPage() {
  const [maxN, setMaxN] = useState(80);
  const [active, setActive] = useState<number[]>([2, 3]);
  const [step, setStep] = useState(0.35);
  const [showAll, setShowAll] = useState(true);
  const [dim, setDim] = useState<"2d" | "3d">("3d");

  const toggle = (p: number) => {
    setActive((a) =>
      a.includes(p) ? a.filter((x) => x !== p) : [...a, p].sort((x, y) => x - y)
    );
  };

  const { traces, lonely, jammed } = useMemo(() => {
    const hitCount = new Map<number, number>();
    for (let n = 2; n <= maxN; n++) hitCount.set(n, 0);

    const braidTraces: Data[] = [];
    active.forEach((p, i) => {
      const xs: number[] = [];
      const ys: number[] = [];
      const zs: number[] = [];
      const text: string[] = [];
      for (let k = 1; p * k <= maxN; k++) {
        const n = p * k;
        hitCount.set(n, (hitCount.get(n) ?? 0) + 1);
        const pt = xyz(n, step);
        xs.push(pt.x);
        ys.push(pt.y);
        zs.push(pt.z);
        text.push(`${n} = ${k}·${p}`);
      }
      if (dim === "3d") {
        braidTraces.push({
          type: "scatter3d",
          mode: "lines+markers",
          x: xs,
          y: ys,
          z: zs,
          text,
          name: `×${p}`,
          line: { color: COLORS[i % COLORS.length], width: p === 2 ? 8 : 5 },
          marker: { size: p === 2 ? 4 : 3, color: COLORS[i % COLORS.length] },
          hovertemplate: "%{text}<extra></extra>",
        });
      } else {
        braidTraces.push({
          type: "scatter",
          mode: "lines+markers",
          x: xs,
          y: ys,
          text,
          name: `×${p}`,
          line: { color: COLORS[i % COLORS.length], width: p === 2 ? 3 : 2 },
          marker: { size: p === 2 ? 8 : 6, color: COLORS[i % COLORS.length] },
          hovertemplate: "%{text}<extra></extra>",
        });
      }
    });

    const lonelyN: number[] = [];
    const jamN: number[] = [];
    for (let n = 2; n <= maxN; n++) {
      const h = hitCount.get(n) ?? 0;
      if (h >= 2) jamN.push(n);
      else if (h <= 1) lonelyN.push(n);
    }

    const primesTrue = lonelyN.filter(isPrime);
    const tracesOut: Data[] = [];

    if (showAll) {
      const ns = Array.from({ length: maxN - 1 }, (_, i) => i + 2);
      if (dim === "3d") {
        tracesOut.push({
          type: "scatter3d",
          mode: "markers",
          x: ns.map((n) => xyz(n, step).x),
          y: ns.map((n) => xyz(n, step).y),
          z: ns.map((n) => xyz(n, step).z),
          text: ns.map(String),
          name: "integers",
          marker: { size: 2, color: "#d4cbb8" },
          hovertemplate: "%{text}<extra></extra>",
        });
      } else {
        tracesOut.push({
          type: "scatter",
          mode: "markers",
          x: ns.map((n) => xy(n, step).x),
          y: ns.map((n) => xy(n, step).y),
          text: ns.map(String),
          name: "integers",
          marker: { size: 4, color: "#d4cbb8" },
          hovertemplate: "%{text}<extra></extra>",
        });
      }
    }

    tracesOut.push(...braidTraces);

    if (dim === "3d") {
      tracesOut.push({
        type: "scatter3d",
        mode: "markers",
        x: jamN.map((n) => xyz(n, step).x),
        y: jamN.map((n) => xyz(n, step).y),
        z: jamN.map((n) => xyz(n, step).z),
        text: jamN.map(String),
        name: "intersections",
        marker: { size: 5, color: ORANGE, symbol: "x" },
        hovertemplate: "meet %{text}<extra></extra>",
      });
      tracesOut.push({
        type: "scatter3d",
        mode: "markers+text",
        x: primesTrue.map((n) => xyz(n, step).x),
        y: primesTrue.map((n) => xyz(n, step).y),
        z: primesTrue.map((n) => xyz(n, step).z),
        text: primesTrue.map(String),
        textposition: "top center",
        textfont: { size: 10, color: NAVY },
        name: "primes",
        marker: { size: 5, color: NAVY, symbol: "diamond" },
        hovertemplate: "prime %{text}<extra></extra>",
      });
    } else {
      tracesOut.push({
        type: "scatter",
        mode: "markers",
        x: jamN.map((n) => xy(n, step).x),
        y: jamN.map((n) => xy(n, step).y),
        text: jamN.map(String),
        name: "intersections",
        marker: {
          size: 11,
          color: ORANGE,
          symbol: "x",
          line: { width: 1.5, color: MAROON },
        },
        hovertemplate: "meet %{text}<extra></extra>",
      });
      tracesOut.push({
        type: "scatter",
        mode: "markers+text",
        x: primesTrue.map((n) => xy(n, step).x),
        y: primesTrue.map((n) => xy(n, step).y),
        text: primesTrue.map(String),
        textposition: "top center",
        textfont: { size: 10, color: NAVY },
        name: "primes",
        marker: { size: 10, color: NAVY, symbol: "diamond" },
        hovertemplate: "prime %{text}<extra></extra>",
      });
    }

    return { traces: tracesOut, lonely: primesTrue, jammed: jamN };
  }, [maxN, active, step, showAll, dim]);

  const layout2d: Partial<Layout> = {
    paper_bgcolor: CREAM,
    plot_bgcolor: PAPER,
    margin: { l: 40, r: 20, t: 40, b: 40 },
    title: {
      text: "Prime braids (top view)",
      font: { size: 13, family: "Georgia, serif" },
    },
    xaxis: { zeroline: true, scaleanchor: "y" },
    yaxis: { zeroline: true },
    showlegend: true,
    legend: { orientation: "h", y: -0.18 },
    font: { family: "Georgia, Palatino, serif" },
  };

  const layout3d: Partial<Layout> = {
    paper_bgcolor: CREAM,
    margin: { l: 0, r: 0, t: 36, b: 0 },
    title: {
      text: "Prime braids — drag to rotate · vertical = n",
      font: { size: 13, family: "Georgia, serif" },
    },
    showlegend: true,
    legend: { orientation: "h", y: -0.05 },
    font: { family: "Georgia, Palatino, serif" },
    scene: {
      bgcolor: PAPER,
      xaxis: { title: { text: "spiral x" }, gridcolor: "#e2d8c8" },
      yaxis: { title: { text: "spiral y" }, gridcolor: "#e2d8c8" },
      zaxis: { title: { text: "n (vertical)" }, gridcolor: "#e2d8c8" },
      camera: { eye: { x: 1.6, y: 1.4, z: 1.1 } },
      aspectmode: "manual",
      aspectratio: { x: 1, y: 1, z: 1.2 },
    },
  };

  const only2 = active.length === 1 && active[0] === 2;
  const twoAndThree = active.includes(2) && active.includes(3);

  return (
    <main className="page">
      <h1>Primes — braids &amp; jams</h1>
      <p className="lede">
        Each prime draws a spiral of its multiples. Where braids meet, composites.
        Lonely marks are primes. <strong>2 plays nice</strong>; <strong>3 jams</strong>{" "}
        because it adds an irreducible braid. In 3D the vertical is n — drag to
        rotate, same habit as the walk ribbon.
      </p>

      <div className="value" style={{ fontSize: "1.25rem" }}>
        {only2
          ? "2 alone — knife, no jam yet"
          : twoAndThree
            ? "2 + 3 — first jam"
            : `${active.map((p) => `×${p}`).join(" · ") || "no braids"}`}
      </div>
      <div className="expr">
        {dim === "3d" ? "3D · drag to orbit · z = n" : "2D top view"} ·
        intersections {jammed.length} · primes {lonely.length} · N ≤ {maxN}
      </div>
      <div className="rule">
        orange X = braid meetings · navy diamonds = primes · ×2 braid drawn heavier
      </div>

      <div className="graph2d" style={{ height: dim === "3d" ? 520 : 460 }}>
        <Plot
          data={traces}
          layout={dim === "3d" ? layout3d : layout2d}
          config={plotConfig}
          style={{ width: "100%", height: "100%" }}
          useResizeHandler
        />
      </div>

      <div className="panel">
        <label className="row">
          <span>view</span>
          <span>{dim === "3d" ? "3D rotate" : "2D top"}</span>
        </label>
        <div className="modes" style={{ display: "flex", gap: "0.4rem", flexWrap: "wrap" }}>
          <button
            type="button"
            onClick={() => setDim("3d")}
            style={{
              background: dim === "3d" ? "#1f4e79" : "#fffaf3",
              color: dim === "3d" ? "#fff" : "#1a1a1a",
              border: "1px solid #e2d8c8",
              borderRadius: 8,
              padding: "0.35rem 0.75rem",
              font: "inherit",
              cursor: "pointer",
            }}
          >
            3D rotate
          </button>
          <button
            type="button"
            onClick={() => setDim("2d")}
            style={{
              background: dim === "2d" ? "#1f4e79" : "#fffaf3",
              color: dim === "2d" ? "#fff" : "#1a1a1a",
              border: "1px solid #e2d8c8",
              borderRadius: 8,
              padding: "0.35rem 0.75rem",
              font: "inherit",
              cursor: "pointer",
            }}
          >
            2D top
          </button>
        </div>

        <label className="row" style={{ marginTop: "0.75rem" }}>
          <span>braids</span>
          <span>{active.length ? active.map((p) => `×${p}`).join(" ") : "none"}</span>
        </label>
        <div className="modes" style={{ display: "flex", gap: "0.4rem", flexWrap: "wrap" }}>
          {BRAID_PRIMES.map((p) => (
            <button
              key={p}
              type="button"
              onClick={() => toggle(p)}
              style={{
                background: active.includes(p)
                  ? p === 2
                    ? "#1f4e79"
                    : "#9a2f38"
                  : "#fffaf3",
                color: active.includes(p) ? "#fff" : "#1a1a1a",
                border: "1px solid #e2d8c8",
                borderRadius: 8,
                padding: "0.35rem 0.75rem",
                font: "inherit",
                cursor: "pointer",
              }}
            >
              ×{p}
            </button>
          ))}
        </div>

        <div className="actions" style={{ marginTop: "0.75rem" }}>
          <button type="button" onClick={() => setActive([2])}>
            only 2 — plays nice
          </button>
          <button type="button" onClick={() => setActive([2, 3])}>
            2 then 3 — jam
          </button>
          <button type="button" onClick={() => setActive([2, 3, 5, 7])}>
            sieve braid
          </button>
          <button type="button" onClick={() => setActive([])}>
            clear braids
          </button>
        </div>

        <label className="row" style={{ marginTop: "0.8rem" }}>
          <span>N max</span>
          <span>{maxN}</span>
        </label>
        <input
          type="range"
          min={30}
          max={200}
          step={5}
          value={maxN}
          onChange={(e) => setMaxN(parseInt(e.target.value, 10))}
        />

        <label className="row">
          <span>spiral tightness</span>
          <span>{step.toFixed(2)}</span>
        </label>
        <input
          type="range"
          min={0.15}
          max={0.7}
          step={0.01}
          value={step}
          onChange={(e) => setStep(parseFloat(e.target.value))}
        />

        <label className="row">
          <span>show all integers</span>
          <select
            value={showAll ? "on" : "off"}
            onChange={(e) => setShowAll(e.target.value === "on")}
          >
            <option value="on">on</option>
            <option value="off">off — braids only</option>
          </select>
        </label>

        <p className="hint">
          Default is 3D: click-drag to orbit, scroll to zoom. Vertical axis is the
          integer n climbing out of the plane — the “up” you asked for. Switch to
          2D for the flat octagonal top view.
        </p>
      </div>

      <div className="catalogue-list" style={{ marginTop: "1rem" }}>
        <article className="catalogue-card grade-clean">
          <header className="catalogue-card-head">
            <h2>2 plays nice</h2>
            <span className="grade-pill grade-clean">knife</span>
          </header>
          <p>
            One braid. Even versus odd. Same knife as return / half-turn / order 2.
          </p>
        </article>
        <article className="catalogue-card grade-clean">
          <header className="catalogue-card-head">
            <h2>3 jams because it is prime</h2>
            <span className="grade-pill grade-clean">NM</span>
          </header>
          <p>
            A new irreducible braid cannot be drawn from ×2. Intersections are the
            jam; lonely heights are primes.
          </p>
        </article>
        <article className="catalogue-card grade-calligraphy">
          <header className="catalogue-card-head">
            <h2>Vertical = n</h2>
            <span className="grade-pill grade-calligraphy">3D</span>
          </header>
          <p>
            Height is the number itself. Rotate to see braids as helices climbing
            the integer tower — prettier cousin of the walk ribbon.
          </p>
        </article>
        <article className="catalogue-card grade-calligraphy">
          <header className="catalogue-card-head">
            <h2>Side bay, not the alphabet</h2>
            <span className="grade-pill grade-calligraphy">honest</span>
          </header>
          <p>
            Fun sieve geometry — but it does not speak e, i, π yet. The island’s
            native prime door is still open: prime marks on the walk axis, odd
            peg ∩ primes, +1 past a product of e-powers. Keep this page as a
            sketch unless those doors light up.
          </p>
        </article>
      </div>
    </main>
  );
}
