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

type DoorCost = {
  missing: number[];
  door: number;
  key: readonly [number, number, number, number];
};

function tryDoor(
  door: number,
  p: number,
  S: Set<number>
): DoorCost | null {
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
    door,
    key: [missing.length, sum, magPref, signPref],
  };
}

function better(a: DoorCost, b: DoorCost): boolean {
  for (let i = 0; i < 4; i++) {
    if (a.key[i] < b.key[i]) return true;
    if (a.key[i] > b.key[i]) return false;
  }
  return false;
}

function computeSpectrum(buildN: number, doors: number[]) {
  const odds = primesUpTo(buildN).filter((p) => p >= 3);
  const S = new Set<number>();
  const usage: Record<string, number> = {};
  for (const d of doors) usage[String(d)] = 0;
  const covers: { p: number; door: number; m: number }[] = [];

  for (const p of odds) {
    let best: DoorCost | null = null;
    for (const d of doors) {
      const c = tryDoor(d, p, S);
      if (!c) continue;
      if (!best || better(c, best)) best = c;
    }
    if (best) {
      usage[String(best.door)]++;
      covers.push({ p, door: best.door, m: p - best.door });
      for (const f of best.missing) S.add(f);
    }
  }
  const sorted = [...S].sort((a, b) => a - b);
  const Pno3 = primesUpTo(buildN).filter((p) => p !== 3);
  const missed = Pno3.filter((p) => !S.has(p));
  return { S: sorted, missed, usage, covers };
}

const PRESETS: { id: string; label: string; doors: number[] }[] = [
  { id: "classic", label: "classic +1,+3", doors: [3, 1] },
  { id: "signed", label: "signed ±1,±3", doors: [3, 1, -3, -1] },
  { id: "pm3", label: "only ±3", doors: [3, -3] },
  { id: "no_m3", label: "+1,+3,−1", doors: [3, 1, -1] },
  { id: "pm1", label: "only ±1", doors: [1, -1] },
];

const DEFAULT_N = 2000;

export function SpectrumPage() {
  const [N, setN] = useState(DEFAULT_N);
  const [presetId, setPresetId] = useState("signed");

  const preset = PRESETS.find((p) => p.id === presetId) ?? PRESETS[1];

  const all = useMemo(() => {
    const map: Record<string, ReturnType<typeof computeSpectrum>> = {};
    for (const p of PRESETS) map[p.id] = computeSpectrum(N, p.doors);
    return map;
  }, [N]);

  const active = all[preset.id];
  const classic = all.classic;
  const signed = all.signed;

  const sizeBars: Data[] = useMemo(
    () => [
      {
        type: "bar",
        name: "|S|",
        x: PRESETS.map((p) => p.label),
        y: PRESETS.map((p) => all[p.id].S.length),
        marker: { color: MAROON },
      },
      {
        type: "bar",
        name: "missed",
        x: PRESETS.map((p) => p.label),
        y: PRESETS.map((p) => all[p.id].missed.length),
        marker: { color: NAVY },
        yaxis: "y2",
      },
    ],
    [all]
  );

  const sizeLayout: Partial<Layout> = {
    paper_bgcolor: CREAM,
    plot_bgcolor: PAPER,
    barmode: "group",
    margin: { l: 50, r: 55, t: 40, b: 90 },
    title: {
      text: "Spectral budget — |S| vs missed (walk ≤ N)",
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

  const doorKeys = Object.keys(active.usage);
  const usageData: Data[] = useMemo(
    () => [
      {
        type: "bar",
        x: doorKeys.map((k) => `door ${k}`),
        y: doorKeys.map((k) => active.usage[k]),
        marker: { color: ORANGE },
        name: "covers",
      },
    ],
    [active, doorKeys]
  );

  const usageLayout: Partial<Layout> = {
    paper_bgcolor: CREAM,
    plot_bgcolor: PAPER,
    margin: { l: 45, r: 20, t: 36, b: 50 },
    title: {
      text: `Door usage — ${preset.label}`,
      font: { size: 13, family: "Georgia, serif" },
    },
    yaxis: { rangemode: "tozero", title: { text: "odd primes covered" } },
    font: { family: "Georgia, Palatino, serif" },
  };

  const delta =
    classic.S.length - signed.S.length;

  const growth = useMemo(() => {
    const xs: number[] = [];
    for (let n = 100; n <= Math.min(N, 8000); ) {
      xs.push(n);
      if (n < 1000) n += 100;
      else if (n < 4000) n += 250;
      else n += 500;
    }
    if (!xs.includes(N) && N <= 8000) xs.push(N);
    const yC: number[] = [];
    const yS: number[] = [];
    for (const n of xs) {
      yC.push(computeSpectrum(n, [3, 1]).S.length);
      yS.push(computeSpectrum(n, [3, 1, -3, -1]).S.length);
    }
    return { xs, yC, yS };
  }, [N]);

  const growthData: Data[] = useMemo(
    () => [
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
    ],
    [growth]
  );

  const growthLayout: Partial<Layout> = {
    paper_bgcolor: CREAM,
    plot_bgcolor: PAPER,
    margin: { l: 50, r: 20, t: 40, b: 50 },
    title: {
      text: "|S| growth vs N — still climbing (signed slower)",
      font: { size: 13, family: "Georgia, serif" },
    },
    xaxis: { title: { text: "N" } },
    yaxis: { title: { text: "|S|" }, rangemode: "tozero" },
    legend: { orientation: "h", y: -0.25 },
    font: { family: "Georgia, Palatino, serif" },
  };


  return (
    <main className="page">
      <h1>Spectrum — doors, not sieves</h1>
      <p className="lede">
        Riemann-type thread only: which <strong>frequencies</strong> (launchers
        in S) plus which <strong>doors</strong> cover the odd primes. Seat 3
        still never joins S (<code>3 ∤ |m|</code>). Classic doors are{" "}
        <code>+1</code> and <code>+3</code>. Signed doors add{" "}
        <code>−1</code> and <code>−3</code> (so <code>m = p − door</code> can be{" "}
        <code>p+1</code> or <code>p+3</code>). Cost still prefers fewer / smaller
        new launchers, then magnitude-3 doors, then positive sign. This is a
        covering spectrum, not a cheap prime test.
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
          <div className="kv-value" style={{ color: delta > 0 ? GREEN : MAROON }}>
            {delta > 0 ? `−${delta}` : delta}
          </div>
        </div>
      </div>

      <div className="graph2d" style={{ height: 360 }}>
        <Plot
          data={sizeBars}
          layout={sizeLayout}
          config={plotConfig}
          style={{ width: "100%", height: "100%" }}
          useResizeHandler
        />
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
        <label className="row">
          <span>active door set (usage chart + lists)</span>
          <span>{preset.label}</span>
        </label>
        <div style={{ display: "flex", flexWrap: "wrap", gap: "0.4rem" }}>
          {PRESETS.map((p) => (
            <button
              key={p.id}
              type="button"
              className={p.id === presetId ? "nav-link on" : "nav-link"}
              style={{ cursor: "pointer", border: "1px solid #d4c8b8" }}
              onClick={() => setPresetId(p.id)}
            >
              {p.label}
            </button>
          ))}
        </div>
      </div>

      <div className="graph2d" style={{ height: 280, marginTop: "1rem" }}>
        <Plot
          data={usageData}
          layout={usageLayout}
          config={plotConfig}
          style={{ width: "100%", height: "100%" }}
          useResizeHandler
        />
      </div>

      <blockquote
        style={{
          margin: "1rem 0",
          padding: "0.75rem 0.95rem",
          borderLeft: "3px solid " + ORANGE,
          background: PAPER,
          fontSize: "0.92rem",
          lineHeight: 1.45,
        }}
      >
        <strong style={{ color: ORANGE }}>Signed doors help the spectrum.</strong>{" "}
        At N=2000, classic |S|≈78 vs signed ≈33 — roughly half the launcher
        budget for the same covering walk. −3 is load-bearing (many covers use
        it). That fits the quarter-clock: −3 is the other three-tick / −90°
        family, not a new frequency. Smaller S means a thinner “needed
        frequencies” list — still with 2, still without 3 as a tone.
      </blockquote>

      <h2 style={{ marginTop: "1.2rem", fontSize: "1.1rem" }}>
        Does |S| finish?
      </h2>
      <p className="lede" style={{ fontSize: "0.95rem" }}>
        Chart below recomputes |S|(N) up to the dial (capped at 8k in-browser).
        Finite S is ruled out by counting: too few S-smooth neighbours to seat
        ~X/log X primes. The walk still succeeds only by hiring. Limit of the
        ±1 walk: finished S is every prime except 3 (Dirichlet on the legal
        neighbour); supers are a <strong>hiring order</strong>, not a thin
        forever-family. Live question: growth rate of |S| after walking to X.
      </p>
      <div className="graph2d" style={{ height: 320 }}>
        <Plot
          data={growthData}
          layout={growthLayout}
          config={plotConfig}
          style={{ width: "100%", height: "100%" }}
          useResizeHandler
        />
      </div>


      <div className="panel">
        <p className="hint" style={{ marginTop: 0 }}>
          <strong>S ({preset.label}):</strong> {active.S.join(", ") || "—"}
        </p>
        <p className="hint">
          <strong>Missed head:</strong>{" "}
          {active.missed.slice(0, 30).join(", ") || "—"}
          {active.missed.length > 30 ? "…" : ""}
        </p>
        <p className="hint">
          <strong>Classic S head:</strong> {classic.S.slice(0, 24).join(", ")}
        </p>
        <p className="hint">
          <strong>Signed S head:</strong> {signed.S.slice(0, 24).join(", ")}
        </p>
        <p className="hint">
          Read: for p&gt;3 the legal ±1 door is unique (fire 3). |S| after a walk
          to N is how many primes have been hired as factors of legal midranges
          so far — not a forever-thin family. Not-yet-hired primes ≤ N are still
          ordinary primes that will be hired later when they first divide a
          legal neighbour (e.g. 43 is covered at 43 by 2²·11, hired at
          173=4·43−1). Finite S is impossible; under ±1 the finished S is every
          prime except 3. Remaining question: growth rate of |S| after walking
          to X.
        </p>
      </div>
    </main>
  );
}
