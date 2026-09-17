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
const GREEN = "#2f6b4f";
const ORANGE = "#c45c26";
const MUTED = "#7a7468";

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

function computeStrictS(buildN: number): number[] {
  const odds = primesUpTo(buildN).filter((p) => p >= 3);
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

type MissRow = {
  q: number;
  mod4: number;
  timesCould: number;
  timesOtherDoor: number;
  neverFactor: boolean;
  nearestS: number | null;
  gap: number | null;
};

/** Re-walk and classify why each missed q never joined S. */
function classifyMissed(N: number, S: number[], missed: number[]): MissRow[] {
  const Ss = S;
  const rows: MissRow[] = [];
  for (const q of missed) {
    let timesCould = 0;
    let timesOtherDoor = 0;
    const live = new Set<number>();
    for (const p of primesUpTo(N).filter((x) => x >= 3)) {
      const tryDoor = (door: number) => {
        const m = p - door;
        if (m < 2) return null;
        const fs = uniquePrimeFactors(m);
        if (fs.includes(SEAT)) return null;
        const miss = fs.filter((f) => !live.has(f));
        const sum = miss.reduce((a, b) => a + b, 0);
        return {
          miss,
          hasQ: fs.includes(q),
          key: [miss.length, sum, door === 3 ? 0 : 1] as const,
        };
      };
      const c3 = tryDoor(3);
      const c1 = tryDoor(1);
      const qInC3 = !!(c3 && c3.hasQ);
      const qInC1 = !!(c1 && c1.hasQ);
      if (qInC3 || qInC1) timesCould++;
      let best = c3 ?? c1;
      if (c1 && c3) best = c3.key <= c1.key ? c3 : c1;
      if ((qInC3 || qInC1) && best && !best.hasQ) timesOtherDoor++;
      if (best) for (const f of best.miss) live.add(f);
    }
    let nearestS: number | null = null;
    let gap: number | null = null;
    for (const s of Ss) {
      const d = Math.abs(s - q);
      if (gap === null || d < gap) {
        gap = d;
        nearestS = s;
      }
    }
    rows.push({
      q,
      mod4: q % 4,
      timesCould,
      timesOtherDoor,
      neverFactor: timesCould === 0,
      nearestS,
      gap,
    });
  }
  return rows;
}

function mod4Counts(arr: number[]) {
  let m1 = 0;
  let m3 = 0;
  for (const p of arr) {
    if (p % 4 === 1) m1++;
    else if (p % 4 === 3) m3++;
  }
  return { m1, m3 };
}

/** Polar: radius ~ p, angle = (p mod 4) * 90° — four rays for the quarter-clock. */
function polarMod4(p: number): { x: number; y: number } {
  const ray = p % 4; // 1 or 3 for odds; 2 for two
  const theta = (ray * Math.PI) / 2;
  const r = Math.sqrt(p);
  return { x: r * Math.cos(theta), y: r * Math.sin(theta) };
}

const DEFAULT_N = 500;

export function MissedPage() {
  const [N, setN] = useState(DEFAULT_N);

  const data = useMemo(() => {
    const S = computeStrictS(N);
    const Pno3 = primesUpTo(N).filter((p) => p !== 3);
    const Sset = new Set(S);
    const missed = Pno3.filter((p) => !Sset.has(p));
    const rows = classifyMissed(N, S, missed);
    const never = rows.filter((r) => r.neverFactor);
    const skipped = rows.filter((r) => !r.neverFactor);
    return {
      S,
      missed,
      rows,
      never,
      skipped,
      Smod: mod4Counts(S),
      Mmod: mod4Counts(missed),
    };
  }, [N]);

  const circleData: Data[] = useMemo(() => {
    const sPts = data.S.map(polarMod4);
    const mPts = data.missed.map(polarMod4);
    // four pole markers at r=sqrt(N)*1.05
    const R = Math.sqrt(N) * 1.08;
    const poles = [0, 1, 2, 3].map((k) => ({
      x: R * Math.cos((k * Math.PI) / 2),
      y: R * Math.sin((k * Math.PI) / 2),
      label: `${k}×90°`,
    }));
    return [
      {
        type: "scatter",
        mode: "markers",
        name: "in S (launchers)",
        x: sPts.map((p) => p.x),
        y: sPts.map((p) => p.y),
        text: data.S.map(String),
        marker: { size: 8, color: MAROON },
        hovertemplate: "S %{text}<extra></extra>",
      },
      {
        type: "scatter",
        mode: "markers",
        name: "missed (not in S)",
        x: mPts.map((p) => p.x),
        y: mPts.map((p) => p.y),
        text: data.missed.map(String),
        marker: { size: 7, color: NAVY, opacity: 0.75 },
        hovertemplate: "missed %{text}<extra></extra>",
      },
      {
        type: "scatter",
        mode: "markers+text",
        name: "quarter poles",
        x: poles.map((p) => p.x),
        y: poles.map((p) => p.y),
        text: poles.map((p) => p.label),
        textposition: "top center",
        marker: { size: 10, color: ORANGE, symbol: "diamond" },
        hoverinfo: "skip",
      },
    ];
  }, [data, N]);

  const circleLayout: Partial<Layout> = {
    paper_bgcolor: CREAM,
    plot_bgcolor: PAPER,
    margin: { l: 40, r: 20, t: 40, b: 40 },
    title: {
      text: "Mod-4 rays — angle = (p mod 4)×90°, radius √p",
      font: { size: 13, family: "Georgia, serif" },
    },
    xaxis: { zeroline: true, scaleanchor: "y", scaleratio: 1, showgrid: true },
    yaxis: { zeroline: true, showgrid: true },
    legend: { orientation: "h", y: -0.15 },
    font: { family: "Georgia, Palatino, serif" },
    annotations: [
      {
        x: 0,
        y: 0,
        text: "3 ticks = 270° ≡ −90°",
        showarrow: false,
        font: { size: 11, color: MUTED },
      },
    ],
  };

  const barData: Data[] = useMemo(
    () => [
      {
        type: "bar",
        name: "≡1 mod 4",
        x: ["in S", "missed"],
        y: [data.Smod.m1, data.Mmod.m1],
        marker: { color: MAROON },
      },
      {
        type: "bar",
        name: "≡3 mod 4",
        x: ["in S", "missed"],
        y: [data.Smod.m3, data.Mmod.m3],
        marker: { color: NAVY },
      },
    ],
    [data]
  );

  const barLayout: Partial<Layout> = {
    paper_bgcolor: CREAM,
    plot_bgcolor: PAPER,
    barmode: "group",
    margin: { l: 45, r: 20, t: 36, b: 40 },
    title: {
      text: "Mod-4 seat counts — S vs missed",
      font: { size: 13, family: "Georgia, serif" },
    },
    yaxis: { rangemode: "tozero", title: { text: "count" } },
    legend: { orientation: "h", y: -0.2 },
    font: { family: "Georgia, Palatino, serif" },
  };

  return (
    <main className="page">
      <h1>Missed primes — shape of the proper subset</h1>
      <p className="lede">
        Under seat-3 / no ×3, S is a proper subset of the primes except 3.
        <strong> Missed</strong> primes are ordinary primes ≠ 3 that the covering
        walk never needed as launchers. Two shapes show up: some never appear as
        a 3-free factor of <code>p−1</code> or <code>p−3</code> in range
        (never-factor); others could have joined but a cheaper door skipped them
        (other-door). Beside that: on a four-pole circle, three quarter-steps are
        270°, which is the same as decrementing 90° from a full turn — seat 3 as
        a −90° tick, not a launcher frequency.
      </p>

      <div className="split-readout">
        <div>
          <div className="kv-label">N</div>
          <div className="kv-value">{N}</div>
        </div>
        <div>
          <div className="kv-label">|S|</div>
          <div className="kv-value">{data.S.length}</div>
        </div>
        <div>
          <div className="kv-label">missed</div>
          <div className="kv-value">{data.missed.length}</div>
        </div>
        <div>
          <div className="kv-label">never-factor</div>
          <div className="kv-value">{data.never.length}</div>
        </div>
      </div>

      <div className="panel" style={{ marginBottom: "1rem" }}>
        <label className="row">
          <span>N (walk odd primes ≤ N)</span>
          <span>{N}</span>
        </label>
        <input
          type="range"
          min={100}
          max={3000}
          step={50}
          value={N}
          onChange={(e) => setN(parseInt(e.target.value, 10))}
        />
      </div>

      <div className="graph2d" style={{ height: 420 }}>
        <Plot
          data={circleData}
          layout={circleLayout}
          config={plotConfig}
          style={{ width: "100%", height: "100%" }}
          useResizeHandler
        />
      </div>

      <div className="graph2d" style={{ height: 280, marginTop: "1rem" }}>
        <Plot
          data={barData}
          layout={barLayout}
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
        <strong style={{ color: ORANGE }}>Quarter-clock.</strong> Four poles at
        0° / 90° / 180° / 270°. One full return is four quarter-ticks. Taking
        three ticks lands at 270°, which is one quarter short of return — the
        same as stepping −90°. Door <code>+3</code> is that three-tick move on
        the mod-4 circle; the rule keeps 3 as seat / door, never as a spiral
        frequency in S. Odd primes sit on the 90° and 270° rays (≡1 and ≡3 mod
        4).
      </blockquote>

      <div className="panel">
        <p className="hint" style={{ marginTop: 0 }}>
          <strong>Missed head:</strong> {data.missed.slice(0, 24).join(", ")}
          {data.missed.length > 24 ? "…" : ""}
        </p>
        <p className="hint">
          <strong>Never-factor sample:</strong>{" "}
          {data.never
            .slice(0, 16)
            .map((r) => r.q)
            .join(", ") || "—"}
        </p>
        <p className="hint">
          <strong>Other-door sample:</strong>{" "}
          {data.skipped
            .slice(0, 16)
            .map((r) => r.q)
            .join(", ") || "—"}
        </p>

        <table
          style={{
            width: "100%",
            borderCollapse: "collapse",
            marginTop: "0.75rem",
            fontSize: "0.88rem",
          }}
        >
          <thead>
            <tr style={{ textAlign: "left", borderBottom: "1px solid #e2d8c8" }}>
              <th>q (missed)</th>
              <th>mod 4</th>
              <th>could join</th>
              <th>other-door skips</th>
              <th>class</th>
              <th>nearest S</th>
              <th>gap</th>
            </tr>
          </thead>
          <tbody>
            {data.rows.slice(0, 40).map((r) => (
              <tr key={r.q} style={{ borderBottom: "1px solid #f0e6d8" }}>
                <td>{r.q}</td>
                <td>{r.mod4}</td>
                <td>{r.timesCould}</td>
                <td>{r.timesOtherDoor}</td>
                <td style={{ color: r.neverFactor ? MAROON : GREEN }}>
                  {r.neverFactor ? "never-factor" : "other-door"}
                </td>
                <td>{r.nearestS ?? "—"}</td>
                <td>{r.gap ?? "—"}</td>
              </tr>
            ))}
          </tbody>
        </table>
        {data.rows.length > 40 && (
          <p className="hint">Showing first 40 of {data.rows.length} missed.</p>
        )}

        <p className="hint" style={{ marginTop: "0.9rem" }}>
          Read: never-factor primes are invisible to both doors as 3-free
          cofactors in this range — the walk has no occasion to recruit them.
          Other-door primes show up as possible missing factors, but the cheap
          preference (favor +3, fewer/smaller new launchers) covers p without
          them. That is the shape of the proper subset: not “random holes,” but
          primes the cost rule never had to buy.
        </p>
      </div>
    </main>
  );
}
