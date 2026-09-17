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

function isPrime(n: number): boolean {
  if (n < 2) return false;
  if (n % 2 === 0) return n === 2;
  const lim = Math.floor(Math.sqrt(n));
  for (let d = 3; d <= lim; d += 2) {
    if (n % d === 0) return false;
  }
  return true;
}

/**
 * Point on the alphabet spiral:
 *   z = n · e^(i · n · σ · π) = n (cos(n σ π) + i sin(n σ π))
 * σ (sigmaStep) is in π-units so arm spacing speaks π.
 */
function point(n: number, sigmaStep: number) {
  const th = n * sigmaStep * Math.PI;
  return {
    x: n * Math.cos(th),
    y: n * Math.sin(th),
    z: n,
  };
}

/**
 * Alphabet spiral — primes as marks on n e^(i n σ π).
 * Form from e, i, π; primality chooses the diamonds.
 */
export function AlphabetSpiralPage() {
  const [maxN, setMaxN] = useState(120);
  const [sigmaStep, setSigmaStep] = useState(1); // θ = n · σ · π ; σ=1 → θ = nπ
  const [dim, setDim] = useState<"2d" | "3d">("2d");
  const [showComposites, setShowComposites] = useState(true);

  // Arm period: angle advances by σ π per integer; full 2π turn every Δn = 2/σ
  const armPeriod = Math.abs(sigmaStep) > 1e-9 ? 2 / Math.abs(sigmaStep) : Infinity;

  const { traces, primes, composites } = useMemo(() => {
    const ns = Array.from({ length: maxN - 1 }, (_, i) => i + 2);
    const primesN = ns.filter(isPrime);
    const compsN = ns.filter((n) => !isPrime(n));

    const mapPts = (list: number[]) => list.map((n) => point(n, sigmaStep));

    if (dim === "3d") {
      const data: Data[] = [];
      if (showComposites) {
        const c = mapPts(compsN);
        data.push({
          type: "scatter3d",
          mode: "markers",
          x: c.map((p) => p.x),
          y: c.map((p) => p.y),
          z: c.map((p) => p.z),
          text: compsN.map(String),
          name: "composites",
          marker: { size: 2, color: "#d4cbb8" },
          hovertemplate: "%{text}<extra></extra>",
        });
      }
      // faint polyline through all n for the spiral ribbon
      const all = mapPts(ns);
      data.push({
        type: "scatter3d",
        mode: "lines",
        x: all.map((p) => p.x),
        y: all.map((p) => p.y),
        z: all.map((p) => p.z),
        name: "n e^(i n σ π)",
        line: { color: "#c4b8a4", width: 3 },
        hoverinfo: "skip",
      });
      const pr = mapPts(primesN);
      data.push({
        type: "scatter3d",
        mode: "markers+text",
        x: pr.map((p) => p.x),
        y: pr.map((p) => p.y),
        z: pr.map((p) => p.z),
        text: primesN.map(String),
        textposition: "top center",
        textfont: { size: 9, color: NAVY },
        name: "primes",
        marker: { size: 4, color: NAVY, symbol: "diamond" },
        hovertemplate: "prime %{text}<extra></extra>",
      });
      return { traces: data, primes: primesN, composites: compsN };
    }

    const data: Data[] = [];
    if (showComposites) {
      const c = mapPts(compsN);
      data.push({
        type: "scatter",
        mode: "markers",
        x: c.map((p) => p.x),
        y: c.map((p) => p.y),
        text: compsN.map(String),
        name: "composites",
        marker: { size: 5, color: "#d4cbb8" },
        hovertemplate: "%{text}<extra></extra>",
      });
    }
    const all = mapPts(ns);
    data.push({
      type: "scatter",
      mode: "lines",
      x: all.map((p) => p.x),
      y: all.map((p) => p.y),
      name: "n e^(i n σ π)",
      line: { color: "#c4b8a4", width: 1.5 },
      hoverinfo: "skip",
    });
    const pr = mapPts(primesN);
    data.push({
      type: "scatter",
      mode: "markers+text",
      x: pr.map((p) => p.x),
      y: pr.map((p) => p.y),
      text: primesN.map(String),
      textposition: "top center",
      textfont: { size: 10, color: NAVY },
      name: "primes",
      marker: { size: 9, color: NAVY, symbol: "diamond" },
      hovertemplate: "prime %{text}<extra></extra>",
    });
    // highlight 2 and 3
    for (const [n, color, label] of [
      [2, ORANGE, "2 knife"],
      [3, MAROON, "3 jam"],
    ] as const) {
      if (n <= maxN) {
        const p = point(n, sigmaStep);
        data.push({
          type: "scatter",
          mode: "markers+text",
          x: [p.x],
          y: [p.y],
          text: [label],
          textposition: "bottom center",
          name: label,
          marker: { size: 12, color, symbol: "diamond" },
          hovertemplate: `${n}<extra></extra>`,
          showlegend: false,
        });
      }
    }
    return { traces: data, primes: primesN, composites: compsN };
  }, [maxN, sigmaStep, dim, showComposites]);

  const layout2d: Partial<Layout> = {
    paper_bgcolor: CREAM,
    plot_bgcolor: PAPER,
    margin: { l: 40, r: 20, t: 44, b: 40 },
    title: {
      text: `Alphabet spiral · z = n e^(i n σ π) · σ = ${sigmaStep}`,
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
    margin: { l: 0, r: 0, t: 40, b: 0 },
    title: {
      text: "Alphabet spiral 3D · drag to rotate · vertical = n",
      font: { size: 13, family: "Georgia, serif" },
    },
    showlegend: true,
    legend: { orientation: "h", y: -0.05 },
    font: { family: "Georgia, Palatino, serif" },
    scene: {
      bgcolor: PAPER,
      xaxis: { title: { text: "Re" }, gridcolor: "#e2d8c8" },
      yaxis: { title: { text: "Im" }, gridcolor: "#e2d8c8" },
      zaxis: { title: { text: "n" }, gridcolor: "#e2d8c8" },
      camera: { eye: { x: 1.55, y: 1.35, z: 1.05 } },
      aspectmode: "manual",
      aspectratio: { x: 1, y: 1, z: 1.15 },
    },
  };

  return (
    <main className="page">
      <h1>Alphabet spiral</h1>
      <p className="lede">
        Integers on{" "}
        <strong>
          z = n · e<sup>i · n · σ · π</sup>
        </strong>
        . The arms are the alphabet (e, i, π) wrapping angle by σπ each step;
        roughly every Δn = 2/σ you complete a turn. Diamonds are primes — arithmetic
        choosing seats on an e, i, π curve. Separate from the braid-sieve sketch.
      </p>

      <div className="value" style={{ fontSize: "1.2rem" }}>
        n e^(i n σ π)
      </div>
      <div className="expr">
        σ = {sigmaStep} · arm period Δn ≈{" "}
        {Number.isFinite(armPeriod) ? armPeriod.toFixed(2) : "∞"} · primes{" "}
        {primes.length} / N≤{maxN}
      </div>
      <div className="rule">
        form from the map · who sits on the arms from primality · 2 knife · 3 first
        odd
      </div>

      <div className="graph2d" style={{ height: dim === "3d" ? 520 : 480 }}>
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
          <span>{dim === "3d" ? "3D" : "2D"}</span>
        </label>
        <div className="modes" style={{ display: "flex", gap: "0.4rem", flexWrap: "wrap" }}>
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
            2D
          </button>
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
        </div>

        <label className="row" style={{ marginTop: "0.75rem" }}>
          <span>σ (π-units in the exponent)</span>
          <span>{sigmaStep.toFixed(3)}</span>
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
            σ = 1 · half-turns
          </button>
          <button type="button" onClick={() => setSigmaStep(0.5)}>
            σ = ½ · 2-fold
          </button>
          <button type="button" onClick={() => setSigmaStep(2 / 3)}>
            σ = ⅔ · 3-fold
          </button>
          <button type="button" onClick={() => setSigmaStep(1 / 3)}>
            σ = ⅓ · 6-fold
          </button>
          <button type="button" onClick={() => setSigmaStep(2 / 5)}>
            σ = ⅖ · 5-fold
          </button>
          <button type="button" onClick={() => setSigmaStep(2 / 7)}>
            σ = 2/7 · 7-fold
          </button>
          <button type="button" onClick={() => setSigmaStep(1 / Math.PI)}>
            σ = 1/π · soft arms
          </button>
          <button type="button" onClick={() => setSigmaStep(2)}>
            σ = 2 · return
          </button>
        </div>

        <label className="row" style={{ marginTop: "0.75rem" }}>
          <span>N max</span>
          <span>{maxN}</span>
        </label>
        <input
          type="range"
          min={40}
          max={250}
          step={5}
          value={maxN}
          onChange={(e) => setMaxN(parseInt(e.target.value, 10))}
        />

        <label className="row">
          <span>show composites</span>
          <select
            value={showComposites ? "on" : "off"}
            onChange={(e) => setShowComposites(e.target.value === "on")}
          >
            <option value="on">on — see the arms</option>
            <option value="off">off — primes only</option>
          </select>
        </label>

        <p className="hint">
          When 2/σ is an integer you get a regular polygonal tower: σ = 2/k gives
          k-fold symmetry (⅖ → pentagon, ⅔ → triangle, 2/7 → heptagon). That is π
          in the exponent forcing arm closure — the surprise is arithmetic of the
          dial, not a new prime law. Diamonds still just choose seats.
        </p>
      </div>

      <div className="catalogue-list" style={{ marginTop: "1rem" }}>
        <article className="catalogue-card grade-clean">
          <header className="catalogue-card-head">
            <h2>Form from the alphabet</h2>
            <span className="grade-pill grade-clean">e i π</span>
          </header>
          <p>
            Arms appear because e^(iθ) wraps; the period knows π. That is the
            pattern you saw — map first, primes second.
          </p>
        </article>
        <article className="catalogue-card grade-clean">
          <header className="catalogue-card-head">
            <h2>Primes choose seats</h2>
            <span className="grade-pill grade-clean">NM</span>
          </header>
          <p>
            Every n sits on the spiral. Diamonds are where arithmetic leaves a
            lonely mark. 2 and 3 still open the story: knife, then first jam.
          </p>
        </article>
        <article className="catalogue-card grade-calligraphy">
          <header className="catalogue-card-head">
            <h2>Not the braid page</h2>
            <span className="grade-pill grade-calligraphy">split</span>
          </header>
          <p>
            /primes is the sieve-braid sketch. This page is the island-native
            door: same spiral language as the walk, with primes as marks.
          </p>
        </article>
      </div>
    </main>
  );
}
