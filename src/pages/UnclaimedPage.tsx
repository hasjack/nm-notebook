import { useMemo, useState } from "react";
import type { Data, Layout } from "plotly.js";
import Plot from "../components/Plot";
import {
  CREAM,
  MAROON,
  NAVY,
  ORANGE,
  PAPER,
  plotConfig,
} from "../lib/plotTheme";

const MUTED = "#7a7468";
const SEAT = 3;
const POW3 = "#2f6b4f"; // 3-powers — second colour

function xy(n: number, step: number) {
  const th = n * step;
  return { x: n * Math.cos(th), y: n * Math.sin(th) };
}

function xyz(n: number, step: number) {
  const th = n * step;
  return { x: n * Math.cos(th), y: n * Math.sin(th), z: n };
}

function primesUpTo(n: number): number[] {
  if (n < 2) return [];
  const sieve = new Uint8Array(n + 1);
  sieve.fill(1);
  sieve[0] = 0;
  sieve[1] = 0;
  for (let i = 2; i * i <= n; i++) {
    if (!sieve[i]) continue;
    for (let j = i * i; j <= n; j += i) sieve[j] = 0;
  }
  const out: number[] = [];
  for (let i = 2; i <= n; i++) if (sieve[i]) out.push(i);
  return out;
}

function uniquePrimeFactors(n: number): number[] {
  if (n < 2) return [];
  const fac: number[] = [];
  let x = n;
  if (x % 2 === 0) {
    fac.push(2);
    while (x % 2 === 0) x = Math.floor(x / 2);
  }
  for (let f = 3; f * f <= x; f += 2) {
    if (x % f === 0) {
      fac.push(f);
      while (x % f === 0) x = Math.floor(x / f);
    }
  }
  if (x > 1) fac.push(x);
  return fac;
}

function isPowerOf3(n: number): boolean {
  if (n < 3) return false;
  let x = n;
  while (x % 3 === 0) x = Math.floor(x / 3);
  return x === 1;
}

/**
 * Strict seat-3 rule (shared with Super primes research):
 * prefer p = m + 3; 3 must not divide m; new factors of m join S; 3 never in S.
 */
function computeStrictS(maxN: number): number[] {
  const odds = primesUpTo(maxN).filter((p) => p >= 3);
  const S = new Set<number>();

  const missingCost = (door: number, p: number) => {
    const m = p - door;
    if (m < 2) return null;
    const facs = uniquePrimeFactors(m);
    if (facs.includes(SEAT)) return null;
    const missing = facs.filter((f) => !S.has(f));
    const sum = missing.reduce((a, b) => a + b, 0);
    return { missing, key: [missing.length, sum, door === 3 ? 0 : 1] as const };
  };

  for (const p of odds) {
    const c3 = missingCost(3, p);
    const c1 = missingCost(1, p);
    let best = c3 ?? c1;
    if (c1 && c3) best = c3.key <= c1.key ? c3 : c1;
    if (best) for (const f of best.missing) S.add(f);
  }
  return [...S].sort((a, b) => a - b);
}

function claimedMask(maxN: number, S: number[]): Uint8Array {
  const hit = new Uint8Array(maxN + 1);
  for (const s of S) {
    for (let n = s; n <= maxN; n += s) hit[n] = 1;
  }
  return hit;
}

const DEFAULT_N = 120;
const MAX_N = 600;

export function UnclaimedPage() {
  const [maxN, setMaxN] = useState(DEFAULT_N);
  const [tightness, setTightness] = useState(0.12);
  const [view3d, setView3d] = useState(false);
  const [showClaimedLines, setShowClaimedLines] = useState(true);
  const [showUnclaimed, setShowUnclaimed] = useState(true);
  const [showPow3, setShowPow3] = useState(true);

  const analysis = useMemo(() => {
    const S = computeStrictS(maxN);
    const hit = claimedMask(maxN, S);
    const unclaimed: number[] = [];
    const powers3: number[] = [];
    const otherUnclaimed: number[] = [];
    for (let n = 2; n <= maxN; n++) {
      if (hit[n]) continue;
      unclaimed.push(n);
      if (isPowerOf3(n)) powers3.push(n);
      else otherUnclaimed.push(n);
    }
    return { S, hit, unclaimed, powers3, otherUnclaimed };
  }, [maxN]);

  const { data, layout } = useMemo(() => {
    const step = tightness;
    const traces: Data[] = [];
    const { S, otherUnclaimed, powers3 } = analysis;

    if (showClaimedLines) {
      // Overlay: one faint braid per super (cap how many full lines for perf)
      const lineSupers = S.filter((s) => s <= maxN);
      for (const s of lineSupers) {
        const ns: number[] = [];
        for (let k = 1; s * k <= maxN; k++) ns.push(s * k);
        if (view3d) {
          traces.push({
            type: "scatter3d",
            mode: "lines",
            x: ns.map((n) => xyz(n, step).x),
            y: ns.map((n) => xyz(n, step).y),
            z: ns.map((n) => xyz(n, step).z),
            line: { color: "rgba(154,47,56,0.28)", width: 3 },
            name: `×${s}`,
            hoverinfo: "skip",
            showlegend: false,
          });
        } else {
          traces.push({
            type: "scatter",
            mode: "lines",
            x: ns.map((n) => xy(n, step).x),
            y: ns.map((n) => xy(n, step).y),
            line: { color: "rgba(154,47,56,0.28)", width: 1.5 },
            name: `×${s}`,
            hoverinfo: "skip",
            showlegend: false,
          });
        }
      }
      // Launch points
      if (view3d) {
        traces.push({
          type: "scatter3d",
          mode: "markers+text",
          x: S.map((s) => xyz(s, step).x),
          y: S.map((s) => xyz(s, step).y),
          z: S.map((s) => xyz(s, step).z),
          text: S.map(String),
          textposition: "top center",
          marker: { size: 5, color: ORANGE, symbol: "diamond" },
          name: "super launches",
          hovertemplate: "super %{text}<extra></extra>",
        });
      } else {
        traces.push({
          type: "scatter",
          mode: "markers+text",
          x: S.map((s) => xy(s, step).x),
          y: S.map((s) => xy(s, step).y),
          text: S.map(String),
          textposition: "top center",
          textfont: { size: 9 },
          marker: { size: 9, color: ORANGE, symbol: "diamond" },
          name: "super launches",
          hovertemplate: "super %{text}<extra></extra>",
        });
      }
    }

    if (showUnclaimed && otherUnclaimed.length) {
      if (view3d) {
        traces.push({
          type: "scatter3d",
          mode: "markers",
          x: otherUnclaimed.map((n) => xyz(n, step).x),
          y: otherUnclaimed.map((n) => xyz(n, step).y),
          z: otherUnclaimed.map((n) => xyz(n, step).z),
          text: otherUnclaimed.map(String),
          marker: { size: 3, color: NAVY },
          name: "unclaimed (other)",
          hovertemplate: "unclaimed %{text}<extra></extra>",
        });
      } else {
        traces.push({
          type: "scatter",
          mode: "markers",
          x: otherUnclaimed.map((n) => xy(n, step).x),
          y: otherUnclaimed.map((n) => xy(n, step).y),
          text: otherUnclaimed.map(String),
          marker: { size: 6, color: NAVY, opacity: 0.75 },
          name: "unclaimed (other)",
          hovertemplate: "unclaimed %{text}<extra></extra>",
        });
      }
    }

    if (showPow3 && powers3.length) {
      if (view3d) {
        traces.push({
          type: "scatter3d",
          mode: "markers+text",
          x: powers3.map((n) => xyz(n, step).x),
          y: powers3.map((n) => xyz(n, step).y),
          z: powers3.map((n) => xyz(n, step).z),
          text: powers3.map(String),
          textposition: "top center",
          marker: { size: 7, color: POW3, symbol: "diamond" },
          name: "3-powers (unclaimed)",
          hovertemplate: "3-power %{text}<extra></extra>",
        });
      } else {
        traces.push({
          type: "scatter",
          mode: "markers+text",
          x: powers3.map((n) => xy(n, step).x),
          y: powers3.map((n) => xy(n, step).y),
          text: powers3.map(String),
          textposition: "top center",
          textfont: { size: 10, color: POW3 },
          marker: { size: 11, color: POW3, symbol: "diamond" },
          name: "3-powers (unclaimed)",
          hovertemplate: "3-power %{text}<extra></extra>",
        });
      }
    }

    const baseLayout: Partial<Layout> = {
      paper_bgcolor: CREAM,
      plot_bgcolor: PAPER,
      margin: { l: 40, r: 20, t: 44, b: 40 },
      title: {
        text: view3d
          ? "Unclaimed research — overlay (3D)"
          : "Unclaimed research — supers overlaid, holes lit",
        font: { size: 13, family: "Georgia, serif" },
      },
      showlegend: true,
      legend: { orientation: "h", y: -0.18 },
      font: { family: "Georgia, Palatino, serif" },
    };

    if (view3d) {
      return {
        data: traces,
        layout: {
          ...baseLayout,
          scene: {
            xaxis: { title: { text: "spiral x" } },
            yaxis: { title: { text: "spiral y" } },
            zaxis: { title: { text: "n" } },
            aspectmode: "data" as const,
          },
        } satisfies Partial<Layout>,
      };
    }
    return {
      data: traces,
      layout: {
        ...baseLayout,
        xaxis: { title: { text: "x" }, zeroline: true, scaleanchor: "y" },
        yaxis: { title: { text: "y" }, zeroline: true },
      } satisfies Partial<Layout>,
    };
  }, [analysis, maxN, tightness, view3d, showClaimedLines, showUnclaimed, showPow3]);

  return (
    <main className="page">
      <h1>Unclaimed — overlay research bay</h1>
      <p className="lede">
        Project every <strong>super-prime spiral</strong> on top of the same
        Archimedean number walk (strict seat-3 rule: 3 only as +3, never ×3, never
        a launcher). A mark n is <strong>claimed</strong> if some s in S divides
        n. Everything else is <strong>unclaimed</strong> — including all{" "}
        <strong>powers of 3</strong> (9, 27, 81, …), which no orange helix can
        hit. This page is for researching those holes.
      </p>

      <div className="split-readout">
        <div>
          <div className="kv-label">|S| launchers</div>
          <div className="kv-value">{analysis.S.length}</div>
        </div>
        <div>
          <div className="kv-label">unclaimed ≤ N</div>
          <div className="kv-value">{analysis.unclaimed.length}</div>
        </div>
        <div>
          <div className="kv-label">3-powers unclaimed</div>
          <div className="kv-value" style={{ color: POW3 }}>
            {analysis.powers3.length}
          </div>
        </div>
        <div>
          <div className="kv-label">other unclaimed</div>
          <div className="kv-value">{analysis.otherUnclaimed.length}</div>
        </div>
      </div>
      <p className="hint" style={{ marginTop: 0 }}>
        Green diamonds = 3^k. Navy = other unclaimed (passenger-prime products,
        etc.). Faint maroon = overlaid ×s braids; orange = launches.
      </p>

      <div className={view3d ? "graph3d" : "graph2d"} style={{ height: 500 }}>
        <Plot
          data={data}
          layout={layout}
          config={plotConfig}
          style={{ width: "100%", height: "100%" }}
          useResizeHandler
        />
      </div>

      <div className="panel">
        <label className="row">
          <span>N max</span>
          <span>{maxN}</span>
        </label>
        <input
          type="range"
          min={30}
          max={MAX_N}
          step={10}
          value={maxN}
          onChange={(e) => setMaxN(parseInt(e.target.value, 10))}
        />

        <label className="row">
          <span>spiral tightness</span>
          <span>{tightness.toFixed(3)}</span>
        </label>
        <input
          type="range"
          min={0.02}
          max={0.45}
          step={0.005}
          value={tightness}
          onChange={(e) => setTightness(parseFloat(e.target.value))}
        />

        <label className="row">
          <span>show super overlays</span>
          <input
            type="checkbox"
            checked={showClaimedLines}
            onChange={(e) => setShowClaimedLines(e.target.checked)}
          />
        </label>
        <label className="row">
          <span>show other unclaimed</span>
          <input
            type="checkbox"
            checked={showUnclaimed}
            onChange={(e) => setShowUnclaimed(e.target.checked)}
          />
        </label>
        <label className="row">
          <span>show 3-powers</span>
          <input
            type="checkbox"
            checked={showPow3}
            onChange={(e) => setShowPow3(e.target.checked)}
          />
        </label>
        <label className="row">
          <span>3D view (z = n)</span>
          <input
            type="checkbox"
            checked={view3d}
            onChange={(e) => setView3d(e.target.checked)}
          />
        </label>

        <p className="hint">
          Research note: under seat-3 / no ×3, the set of forever-unclaimed
          families always includes the powers of 3. Other holes are integers whose
          prime factors all lie outside S (passenger primes). As N grows, S
          densifies and many holes close — except pure 3-powers.
        </p>

        <blockquote
          style={{
            margin: "0.8rem 0 0",
            padding: "0.65rem 0.9rem",
            borderLeft: "3px solid " + NAVY,
            background: PAPER,
            color: "#1a1a1a",
            fontSize: "0.9rem",
            lineHeight: 1.45,
          }}
        >
          <strong style={{ color: MAROON }}>Claim test.</strong> n is claimed
          iff some super s divides n. Unclaimed iff n is built only from primes
          outside S (including the seat prime 3). Separate bay from Super so this
          overlay can grow without crowding the launcher page.
        </blockquote>
      </div>
    </main>
  );
}
