import { useMemo, useState } from "react";
import type { Data, Layout } from "plotly.js";
import Plot from "../components/Plot";
import {
  CREAM,
  MAROON,
  NAVY,
  PAPER,
  plotConfig,
} from "../lib/plotTheme";

const SEAT = 3;
const ORANGE = "#c45c26";
const GREEN = "#2f6b4f";

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
  const abs = Math.abs(n);
  if (abs < 2) return [];
  const fac: number[] = [];
  let x = abs;
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

type DoorHit = {
  missing: number[];
  key: readonly [number, number, number, number];
  door: number;
};

function tryDoor(
  door: number,
  p: number,
  S: Set<number>
): DoorHit | null {
  const m = p - door;
  if (m <= 1 && m >= -1) return null;
  const fs = uniquePrimeFactors(m);
  if (fs.includes(SEAT)) return null;
  const missing = fs.filter((f) => !S.has(f));
  const sum = missing.reduce((a, b) => a + b, 0);
  const magPref = Math.abs(door) === 3 ? 0 : 1;
  const signPref = door > 0 ? 0 : 1;
  return {
    missing,
    key: [missing.length, sum, magPref, signPref] as const,
    door,
  };
}

function better(a: DoorHit, b: DoorHit): boolean {
  for (let i = 0; i < 4; i++) {
    if (a.key[i] < b.key[i]) return true;
    if (a.key[i] > b.key[i]) return false;
  }
  return false;
}

function computeCover(
  buildN: number,
  doors: number[]
): { S: number[]; usage: Record<number, number>; covers: { p: number; door: number; m: number }[] } {
  const odds = primesUpTo(buildN).filter((p) => p >= 3);
  const S = new Set<number>();
  const usage: Record<number, number> = {};
  for (const d of doors) usage[d] = 0;
  const covers: { p: number; door: number; m: number }[] = [];

  for (const p of odds) {
    let best: DoorHit | null = null;
    for (const d of doors) {
      const c = tryDoor(d, p, S);
      if (!c) continue;
      if (!best || better(c, best)) best = c;
    }
    if (best) {
      usage[best.door]++;
      covers.push({ p, door: best.door, m: p - best.door });
      for (const f of best.missing) S.add(f);
    }
  }
  return { S: [...S].sort((a, b) => a - b), usage, covers };
}

const PRESETS: { id: string; label: string; doors: number[] }[] = [
  { id: "classic", label: "+1, +3 (classic)", doors: [3, 1] },
  { id: "signed", label: "±1, ±3 (signed)", doors: [3, 1, -3, -1] },
  { id: "pm3", label: "±3 only", doors: [3, -3] },
  { id: "no_m3", label: "+1, +3, −1", doors: [3, 1, -1] },
];

const DEFAULT_N = 2000;

export function SignedDoorsPage() {
  const [N, setN] = useState(DEFAULT_N);

  const runs = useMemo(() => {
    return PRESETS.map((p) => {
      const { S, usage, covers } = computeCover(N, p.doors);
      const Pno3 = primesUpTo(N).filter((x) => x !== 3);
      const Sset = new Set(S);
      const missed = Pno3.filter((x) => !Sset.has(x));
      return { ...p, S, usage, covers, missed };
    });
  }, [N]);

  const classic = runs.find((r) => r.id === "classic")!;
  const signed = runs.find((r) => r.id === "signed")!;

  const growth = useMemo(() => {
    const xs: number[] = [];
    for (let n = 100; n <= Math.min(N, 5000); n += 100) xs.push(n);
    if (!xs.includes(N)) xs.push(N);
    const yC: number[] = [];
    const yS: number[] = [];
    for (const n of xs) {
      yC.push(computeCover(n, [3, 1]).S.length);
      yS.push(computeCover(n, [3, 1, -3, -1]).S.length);
    }
    return { xs, yC, yS };
  }, [N]);

  const sizeBar: Data[] = [
    {
      type: "bar",
      name: "|S|",
      x: runs.map((r) => r.label),
      y: runs.map((r) => r.S.length),
      marker: { color: MAROON },
    },
    {
      type: "bar",
      name: "missed primes",
      x: runs.map((r) => r.label),
      y: runs.map((r) => r.missed.length),
      marker: { color: NAVY },
      yaxis: "y2",
    },
  ];

  const sizeLayout: Partial<Layout> = {
    paper_bgcolor: CREAM,
    plot_bgcolor: PAPER,
    barmode: "group",
    margin: { l: 50, r: 55, t: 40, b: 90 },
    title: {
      text: "Spectral cover — |S| vs door set (3 ∉ S, 3 ∤ m)",
      font: { size: 13, family: "Georgia, serif" },
    },
    yaxis: { title: { text: "|S|" }, rangemode: "tozero" },
    yaxis2: {
      title: { text: "missed" },
      overlaying: "y",
      side: "right",
      rangemode: "tozero",
    },
    legend: { orientation: "h", y: -0.4 },
    font: { family: "Georgia, Palatino, serif" },
  };

  const growthData: Data[] = [
    {
      type: "scatter",
      mode: "lines+markers",
      name: "classic +1,+3",
      x: growth.xs,
      y: growth.yC,
      line: { color: MAROON },
    },
    {
      type: "scatter",
      mode: "lines+markers",
      name: "signed ±1,±3",
      x: growth.xs,
      y: growth.yS,
      line: { color: GREEN },
    },
  ];

  const growthLayout: Partial<Layout> = {
    paper_bgcolor: CREAM,
    plot_bgcolor: PAPER,
    margin: { l: 50, r: 20, t: 40, b: 45 },
    title: {
      text: "|S| growth — classic vs signed doors",
      font: { size: 13, family: "Georgia, serif" },
    },
    xaxis: { title: { text: "N" } },
    yaxis: { title: { text: "|S|" }, rangemode: "tozero" },
    legend: { orientation: "h", y: -0.2 },
    font: { family: "Georgia, Palatino, serif" },
  };

  const usageDoors = [-3, -1, 1, 3];
  const usageData: Data[] = [
    {
      type: "bar",
      name: "classic",
      x: usageDoors.map(String),
      y: usageDoors.map((d) => classic.usage[d] ?? 0),
      marker: { color: MAROON },
    },
    {
      type: "bar",
      name: "signed",
      x: usageDoors.map(String),
      y: usageDoors.map((d) => signed.usage[d] ?? 0),
      marker: { color: GREEN },
    },
  ];

  const usageLayout: Partial<Layout> = {
    paper_bgcolor: CREAM,
    plot_bgcolor: PAPER,
    barmode: "group",
    margin: { l: 45, r: 20, t: 40, b: 45 },
    title: {
      text: "Door usage counts (how often each door wins)",
      font: { size: 13, family: "Georgia, serif" },
    },
    xaxis: { title: { text: "door" } },
    yaxis: { title: { text: "covers" }, rangemode: "tozero" },
    legend: { orientation: "h", y: -0.2 },
    font: { family: "Georgia, Palatino, serif" },
  };

  return (
    <main className="page">
      <h1>Signed doors — spectral cover (not a sieve)</h1>
      <p className="lede">
        Riemann-type thread only: which launcher frequencies does the covering
        walk need, once doors can point both ways on the quarter-clock?
        Classic doors are <code>+1</code> and <code>+3</code>. Signed adds{" "}
        <code>−1</code> and <code>−3</code> (backward increments). Still:{" "}
        <strong>3 never joins S</strong>, and <code>3 ∤ m</code> for{" "}
        <code>m = p − door</code>. Cost prefers fewer / smaller new launchers,
        then |door|=3 over 1, then + over −. This is spectrum size, not cheap
        primality.
      </p>

      <div className="split-readout">
        <div>
          <div className="kv-label">N</div>
          <div className="kv-value">{N}</div>
        </div>
        <div>
          <div className="kv-label">|S| classic</div>
          <div className="kv-value">{classic.S.length}</div>
        </div>
        <div>
          <div className="kv-label">|S| signed</div>
          <div className="kv-value" style={{ color: GREEN }}>
            {signed.S.length}
          </div>
        </div>
        <div>
          <div className="kv-label">shrink</div>
          <div className="kv-value" style={{ color: ORANGE }}>
            {classic.S.length - signed.S.length}
          </div>
        </div>
      </div>

      <div className="panel">
        <label className="row">
          <span>N (odd primes ≤ N)</span>
          <span>{N}</span>
        </label>
        <input
          type="range"
          min={100}
          max={5000}
          step={50}
          value={N}
          onChange={(e) => setN(parseInt(e.target.value, 10))}
        />
      </div>

      <div className="graph2d" style={{ height: 360 }}>
        <Plot
          data={sizeBar}
          layout={sizeLayout}
          config={plotConfig}
          style={{ width: "100%", height: "100%" }}
          useResizeHandler
        />
      </div>

      <div className="graph2d" style={{ height: 320, marginTop: "1rem" }}>
        <Plot
          data={growthData}
          layout={growthLayout}
          config={plotConfig}
          style={{ width: "100%", height: "100%" }}
          useResizeHandler
        />
      </div>

      <div className="graph2d" style={{ height: 300, marginTop: "1rem" }}>
        <Plot
          data={usageData}
          layout={usageLayout}
          config={plotConfig}
          style={{ width: "100%", height: "100%" }}
          useResizeHandler
        />
      </div>

      <div className="panel">
        <table
          style={{
            width: "100%",
            borderCollapse: "collapse",
            fontSize: "0.9rem",
          }}
        >
          <thead>
            <tr style={{ textAlign: "left", borderBottom: "1px solid #e2d8c8" }}>
              <th>door set</th>
              <th>|S|</th>
              <th>missed</th>
              <th>S head</th>
            </tr>
          </thead>
          <tbody>
            {runs.map((r) => (
              <tr key={r.id} style={{ borderBottom: "1px solid #f0e6d8" }}>
                <td>{r.label}</td>
                <td>{r.S.length}</td>
                <td>{r.missed.length}</td>
                <td style={{ fontSize: "0.82rem" }}>
                  {r.S.slice(0, 14).join(", ")}
                  {r.S.length > 14 ? "…" : ""}
                </td>
              </tr>
            ))}
          </tbody>
        </table>

        <p className="hint" style={{ marginTop: "0.9rem" }}>
          <strong>Signed S:</strong> {signed.S.join(", ")}
        </p>
        <p className="hint">
          <strong>Classic-only launchers (dropped when signed):</strong>{" "}
          {classic.S.filter((s) => !signed.S.includes(s)).slice(0, 30).join(", ")}
          {classic.S.filter((s) => !signed.S.includes(s)).length > 30 ? "…" : ""}
        </p>
        <p className="hint">
          Door usage (signed):{" "}
          {usageDoors
            .map((d) => `${d}: ${signed.usage[d] ?? 0}`)
            .join(" · ")}
        </p>

        <blockquote
          style={{
            margin: "0.9rem 0 0",
            padding: "0.7rem 0.95rem",
            borderLeft: "3px solid " + GREEN,
            background: PAPER,
            fontSize: "0.92rem",
            lineHeight: 1.45,
          }}
        >
          <strong style={{ color: GREEN }}>Reading.</strong> Backward doors are
          not a rename: at these N, signed ±1,±3 roughly halves |S| or better
          (classic 78 → signed 33 at N=2000 in the probe that motivated this
          page). −3 carries real load on the quarter-clock. Still instrument
          news for a covering spectrum — 2 plus a thinner super set, doors on
          both signs — not a claim about zeta zeros.
        </blockquote>
      </div>
    </main>
  );
}
