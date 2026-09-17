import { useMemo, useState, type ReactNode } from "react";
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
const GREEN = "#2f6b4f";

/** Archimedean helpers — match PrimesPage: th = n * step. */
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


function factorParts(n: number): number[] {
  const abs = Math.abs(n);
  if (abs < 2) return [];
  const parts: number[] = [];
  let x = abs;
  for (let d = 2; d * d <= x; d++) {
    while (x % d === 0) {
      parts.push(d);
      x = Math.floor(x / d);
    }
  }
  if (x > 1) parts.push(x);
  return parts;
}

/** Raise exponents as real superscripts (2³), never caret form. */
const SUP_DIGITS = "⁰¹²³⁴⁵⁶⁷⁸⁹";
function toSup(n: number): string {
  return String(n)
    .split("")
    .map((d) => SUP_DIGITS[Number(d)] ?? d)
    .join("");
}

function fmtParts(parts: number[]): string {
  if (parts.length === 0) return "—";
  const counts = new Map<number, number>();
  for (const f of parts) counts.set(f, (counts.get(f) ?? 0) + 1);
  return [...counts.entries()]
    .map(([f, e]) => (e === 1 ? String(f) : `${f}${toSup(e)}`))
    .join(" · ");
}

function fmtPartsEl(parts: number[]): ReactNode {
  if (parts.length === 0) return "—";
  const counts = new Map<number, number>();
  for (const f of parts) counts.set(f, (counts.get(f) ?? 0) + 1);
  const entries = [...counts.entries()];
  return entries.map(([f, e], i) => (
    <span key={`${f}-${e}-${i}`}>
      {i > 0 ? " · " : null}
      {e === 1 ? (
        f
      ) : (
        <>
          {f}
          <sup style={{ fontSize: "0.7em", lineHeight: 0 }}>{e}</sup>
        </>
      )}
    </span>
  ));
}

function writingEl(
  door: "+" | "−" | "seed",
  parts: number[],
  fallback: string,
): ReactNode {
  if (door === "seed") return fallback;
  if (door === "+" && parts.length === 0) return fallback; // 3 = 2+1 handled separately
  return (
    <>
      {fmtPartsEl(parts)}
      {door === "+" ? " + 1" : " − 1"}
    </>
  );
}

/** Unique ±1 door (fire 3). */
function legalPm1(p: number): {
  m: number;
  door: "+" | "−" | "seed";
  writing: string;
  banned: number;
  kept: number;
} {
  if (p === 2) {
    return {
      m: 0,
      door: "seed",
      writing: "base tone (even prime)",
      banned: 0,
      kept: 0,
    };
  }
  if (p === 3) {
    return {
      m: 2,
      door: "+",
      writing: "2 + 1",
      banned: 4,
      kept: 2,
    };
  }
  const mMinus = p - 1;
  const mPlus = p + 1;
  const minusHas3 = mMinus % 3 === 0;
  const door: "+" | "−" = minusHas3 ? "−" : "+";
  const m = door === "+" ? mMinus : mPlus;
  const banned = door === "+" ? mPlus : mMinus;
  const parts = factorParts(m);
  const prod = fmtParts(parts);
  const writing = door === "+" ? `${prod} + 1` : `${prod} − 1`;
  return { m, door, writing, banned, kept: m };
}

/** Hire set S from ±1 walk through N (factors of legal m). */
function hireSThrough(N: number): Set<number> {
  const S = new Set<number>([2]);
  for (const p of primesUpTo(N).filter((x) => x >= 3)) {
    const { m } = legalPm1(p);
    if (m < 2) continue;
    for (const q of uniquePrimeFactors(m)) S.add(q);
  }
  return S;
}

type Pm1Row = {
  p: number;
  writing: string;
  writingNode: ReactNode;
  door: string;
  m: number;
  banned: number;
  hired: boolean;
  hireNote: string;
};

function pm1Table(N: number): Pm1Row[] {
  const primes = primesUpTo(N);
  const S = hireSThrough(N);
  // Newly hired primes at each walk step (the numbers that join S)
  const hiredHere = new Map<number, number[]>([[2, [2]]]);
  const live = new Set<number>([2]);
  for (const p of primes.filter((x) => x >= 3)) {
    const { m } = legalPm1(p);
    if (m < 2) continue;
    const fresh: number[] = [];
    for (const q of uniquePrimeFactors(m)) {
      if (!live.has(q)) {
        live.add(q);
        fresh.push(q);
      }
    }
    if (fresh.length) hiredHere.set(p, fresh);
  }
  return primes.map((p) => {
    const L = legalPm1(p);
    const hired = S.has(p);
    let hireNote = "—";
    if (p !== 3) {
      const fresh = hiredHere.get(p);
      if (fresh?.length) hireNote = fresh.join(" · ");
    }
    const parts =
      p === 2 ? [] : p === 3 ? [2] : factorParts(L.m);
    const doorSym: "+" | "−" | "seed" =
      L.door === "seed" ? "seed" : L.door === "+" ? "+" : "−";
    return {
      p,
      writing: L.writing,
      writingNode:
        p === 2
          ? L.writing
          : p === 3
            ? "2 + 1"
            : writingEl(doorSym, parts, L.writing),
      door: L.door === "seed" ? "—" : `${L.door}1`,
      m: L.m,
      banned: L.banned,
      hired: p === 2 ? true : p === 3 ? false : hired,
      hireNote,
    };
  });
}

type FlipRow = {
  p: number;
  avoidedNode: ReactNode; // 3-free door that carries 5
  usedNode: ReactNode; // ×3 neighbour used instead
  avoidedM: number;
  usedM: number;
  hiredNote: string; // non-3 factors of used m (what the flip door brings)
};

/** Primes whose 3-free ±1 door carries 5 — flip to the ×3 neighbour (sack-5 exception). */
function flipTable(N: number): FlipRow[] {
  const out: FlipRow[] = [];
  for (const p of primesUpTo(N).filter((x) => x > 3)) {
    const mMinus = p - 1;
    const mPlus = p + 1;
    const minusHas3 = mMinus % 3 === 0;
    const freeM = minusHas3 ? mPlus : mMinus;
    const freeDoor: "+" | "−" = minusHas3 ? "−" : "+";
    const flipM = minusHas3 ? mMinus : mPlus;
    const flipDoor: "+" | "−" = minusHas3 ? "+" : "−";
    const freeParts = factorParts(freeM);
    if (!freeParts.includes(5)) continue;
    const flipParts = factorParts(flipM);
    const hireFacs = [
      ...new Set(flipParts.filter((q) => q !== 3)),
    ].sort((a, b) => a - b);
    out.push({
      p,
      avoidedM: freeM,
      usedM: flipM,
      avoidedNode: writingEl(
        freeDoor,
        freeParts,
        freeDoor === "+"
          ? `${fmtParts(freeParts)} + 1`
          : `${fmtParts(freeParts)} − 1`,
      ),
      usedNode: writingEl(
        flipDoor,
        flipParts,
        flipDoor === "+"
          ? `${fmtParts(flipParts)} + 1`
          : `${fmtParts(flipParts)} − 1`,
      ),
      hiredNote: hireFacs.length ? hireFacs.join(" · ") : "—",
    });
  }
  return out;
}

type DoorMode = "strict" | "plus1-no3factor";

/** Seat constant: appears only as +3, never as a prime factor of m, never in S. */
const SEAT = 3;

/**
 * Formal rule (strict):
 * 1. Walk odd primes p ≤ N in order.
 * 2. Write p = m + d with d ∈ {1, 3}. Prefer d = 3.
 * 3. m must NOT be divisible by 3 (3 is only the seat, never a factor).
 *    For p > 3, p−3 is automatically 3-free; p−1 is kept only when 3 ∤ (p−1).
 * 4. Seed: p = 3 uses 3 = 2 + 1 (only +1 that starts S with {2}).
 * 5. Any prime factor of m not already in S is added to S (a super prime / launcher).
 * 6. 3 is never added to S and never launches a spiral.
 */
function computeSuperPrimes(maxN: number, mode: DoorMode) {
  const odds = primesUpTo(maxN).filter((p) => p >= 3);
  const S = new Set<number>();

  const missingCost = (door: number, p: number) => {
    const m = p - door;
    if (m < 2) return null;
    const facs = uniquePrimeFactors(m);
    // Strict: refuse any m that has factor 3
    if (facs.includes(SEAT)) return null;
    const missing = facs.filter((f) => !S.has(f));
    const sum = missing.reduce((a, b) => a + b, 0);
    return { missing, key: [missing.length, sum, door === 3 ? 0 : 1] as const };
  };

  for (const p of odds) {
    if (mode === "plus1-no3factor") {
      const c1 = missingCost(1, p);
      if (c1) for (const f of c1.missing) S.add(f);
      continue;
    }
    // strict: prefer +3; allow +1 only when 3-free and cheaper
    const c3 = missingCost(3, p);
    const c1 = missingCost(1, p);
    let best = c3 ?? c1;
    if (c1 && c3) best = c3.key <= c1.key ? c3 : c1;
    if (best) for (const f of best.missing) S.add(f);
  }

  const sorted = [...S].sort((a, b) => a - b);
  const passengers = odds.filter((p) => p === SEAT || !S.has(p));
  return {
    S: sorted,
    oddPrimes: odds,
    passengers,
    maxS: sorted.length ? sorted[sorted.length - 1]! : 0,
  };
}

const DEFAULT_N = 200;
const MAX_N = 2000;

export function SuperPrimesPage() {
  const [maxN, setMaxN] = useState(DEFAULT_N);
  const [tightness, setTightness] = useState(0.12);
  const [mode, setMode] = useState<DoorMode>("strict");
  const [view3d, setView3d] = useState(false);

  const computed = useMemo(
    () => computeSuperPrimes(maxN, mode),
    [maxN, mode]
  );
  const pm1Rows = useMemo(() => pm1Table(100), []);
  const flipRows = useMemo(() => flipTable(100), []);


  const { data, layout } = useMemo(() => {
    const step = tightness;
    const traces: Data[] = [];

    // Spirals — only for super primes (launchers)
    for (const s of computed.S) {
      const xs: number[] = [];
      const ys: number[] = [];
      const zs: number[] = [];
      const ns: number[] = [];
      for (let k = 1; k * s <= maxN; k++) {
        const n = k * s;
        ns.push(n);
        if (view3d) {
          const p = xyz(n, step);
          xs.push(p.x);
          ys.push(p.y);
          zs.push(p.z);
        } else {
          const p = xy(n, step);
          xs.push(p.x);
          ys.push(p.y);
        }
      }
      if (view3d) {
        traces.push({
          type: "scatter3d",
          mode: "lines+markers",
          x: xs,
          y: ys,
          z: zs,
          line: { color: "rgba(31,78,121,0.35)", width: 2 },
          marker: { size: 3, color: "rgba(154,47,56,0.45)" },
          name: "s=" + s,
          hovertemplate: "n=%{customdata}<extra>s=" + s + "</extra>",
          customdata: ns,
          showlegend: false,
        });
      } else {
        traces.push({
          type: "scatter",
          mode: "lines+markers",
          x: xs,
          y: ys,
          line: { color: "rgba(31,78,121,0.35)", width: 1.4 },
          marker: { size: 5, color: "rgba(154,47,56,0.4)" },
          name: "s=" + s,
          hovertemplate: "n=%{customdata}<extra>s=" + s + "</extra>",
          customdata: ns,
          showlegend: false,
        });
      }
    }

    // Super-prime launch points (orange / navy)
    {
      const labels = computed.S.map(String);
      if (view3d) {
        const pts = computed.S.map((s) => xyz(s, step));
        traces.push({
          type: "scatter3d",
          mode: "text+markers",
          x: pts.map((p) => p.x),
          y: pts.map((p) => p.y),
          z: pts.map((p) => p.z),
          text: labels,
          textposition: "top center",
          textfont: { size: 10, color: NAVY, family: "Georgia, serif" },
          marker: {
            size: 8,
            color: ORANGE,
            symbol: "diamond",
            line: { color: NAVY, width: 1 },
          },
          name: "super primes",
          hovertemplate: "super %{text}<extra></extra>",
        });
      } else {
        const pts = computed.S.map((s) => xy(s, step));
        traces.push({
          type: "scatter",
          mode: "text+markers",
          x: pts.map((p) => p.x),
          y: pts.map((p) => p.y),
          text: labels,
          textposition: "top center",
          textfont: { size: 11, color: NAVY, family: "Georgia, serif" },
          marker: {
            size: 11,
            color: ORANGE,
            symbol: "diamond",
            line: { color: NAVY, width: 1.2 },
          },
          name: "super primes",
          hovertemplate: "super %{text}<extra></extra>",
        });
      }
    }

    // Lonely odd primes that do not launch (passengers)
    {
      const lonely = computed.passengers;
      const labels = lonely.map(String);
      if (view3d) {
        const pts = lonely.map((p) => xyz(p, step));
        traces.push({
          type: "scatter3d",
          mode: "markers",
          x: pts.map((p) => p.x),
          y: pts.map((p) => p.y),
          z: pts.map((p) => p.z),
          marker: {
            size: 3,
            color: MUTED,
            symbol: "diamond",
            opacity: 0.7,
          },
          name: "odd primes (no spiral)",
          text: labels,
          hovertemplate: "passenger %{text}<extra></extra>",
        });
      } else {
        const pts = lonely.map((p) => xy(p, step));
        traces.push({
          type: "scatter",
          mode: "markers",
          x: pts.map((p) => p.x),
          y: pts.map((p) => p.y),
          marker: {
            size: 6,
            color: MUTED,
            symbol: "diamond-open",
            line: { width: 1, color: MUTED },
          },
          name: "odd primes (no spiral)",
          text: labels,
          hovertemplate: "passenger %{text}<extra></extra>",
        });
      }
    }

    const baseLayout: Partial<Layout> = {
      paper_bgcolor: CREAM,
      plot_bgcolor: PAPER,
      margin: { l: 40, r: 20, t: 28, b: 40 },
      showlegend: false,
      font: { family: "Georgia, Palatino, serif" },
      title: {
        text: view3d
          ? "Super-prime braids (3D) — only S launches"
          : "Super-prime braids (top view) — only S launches",
        font: { size: 13, family: "Georgia, serif", color: NAVY },
      },
    };

    if (view3d) {
      return {
        data: traces,
        layout: {
          ...baseLayout,
          scene: {
            xaxis: { title: { text: "x" }, zeroline: true },
            yaxis: { title: { text: "y" }, zeroline: true },
            zaxis: { title: { text: "n" }, zeroline: true },
            camera: { eye: { x: 1.6, y: 1.4, z: 0.9 } },
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
  }, [computed, maxN, tightness, view3d]);

  const expectNote =
    mode === "strict"
      ? "Rule: 3 only as +3 (never ×3). Example: 79 = 2·2·19 + 3 — not 2·3·13 + 1."
      : "+1 only, still forbid factor 3 in m";

  return (
    <main className="page">
      <h1>Super primes</h1>
      <p className="lede">
        Every prime ≤ 100 with its unique 3-free ±1 neighbour. Factors of that
        neighbour <strong>hire</strong> into S. Bold = in S after the walk through 100.
        2 is the seed; 3 = 2+1 and is never hired.
      </p>

      <h2 style={{ fontSize: "1.1rem", marginTop: "0.5rem" }}>
        π(100) — standard vs ±1
      </h2>
      <div className="panel" style={{ overflowX: "auto" }}>
        <table
          style={{
            width: "100%",
            borderCollapse: "collapse",
            fontSize: "0.88rem",
          }}
        >
          <thead>
            <tr style={{ textAlign: "left", borderBottom: "1px solid #e2d8c8" }}>
              <th>p (standard)</th>
              <th>banned neighbour</th>
              <th>legal m</th>
              <th>door</th>
              <th>±1 writing</th>
              <th>hired</th>
            </tr>
          </thead>
          <tbody>
            {pm1Rows.map((r) => {
              const bold = r.hired;
              const weight = bold ? 700 : 400;
              const color = r.p === 3 ? MAROON : bold ? NAVY : undefined;
              return (
                <tr
                  key={r.p}
                  style={{
                    borderBottom: "1px solid #f0e6d8",
                    background:
                      r.p === 97
                        ? "rgba(196,92,38,0.10)"
                        : bold
                          ? "rgba(31,78,121,0.06)"
                          : undefined,
                  }}
                >
                  <td style={{ fontWeight: weight, color }}>{r.p}</td>
                  <td
                    style={{
                      color: MUTED,
                      textDecoration: r.banned ? "line-through" : undefined,
                    }}
                  >
                    {r.banned || "—"}
                  </td>
                  <td style={{ color: r.m ? GREEN : MUTED, fontWeight: 600 }}>
                    {r.m || "—"}
                  </td>
                  <td>{r.door}</td>
                  <td>
                    <code className="pow">{r.writingNode}</code>
                  </td>
                  <td
                    style={{
                      color: r.hireNote !== "—" ? GREEN : MUTED,
                      fontWeight: r.hireNote !== "—" ? 600 : 400,
                    }}
                  >
                    {r.hireNote}
                  </td>
                </tr>
              );
            })}
          </tbody>
        </table>
        <p className="hint" style={{ marginTop: "0.75rem" }}>
          Hired = new primes that join S from this row’s neighbour. Covering ≠
          hiring (a prime can be covered long before it itself joins S). At 97 the
          neighbour is 2 · 7² — first time an odd hire appears squared (earlier
          squares are only powers of 2).
        </p>
      </div>

      <h2 style={{ fontSize: "1.1rem", marginTop: "1.4rem" }}>
        Sack-5 flips (≤ 100)
      </h2>
      <p className="hint" style={{ marginTop: 0 }}>
        Only primes where the 3-free door carries 5. Flip to the ×3 neighbour;
        do not hire 3 or 5.
      </p>
      <div className="panel" style={{ overflowX: "auto" }}>
        <table
          style={{
            width: "100%",
            borderCollapse: "collapse",
            fontSize: "0.88rem",
          }}
        >
          <thead>
            <tr style={{ textAlign: "left", borderBottom: "1px solid #e2d8c8" }}>
              <th>p</th>
              <th>avoided (3-free, ×5)</th>
              <th>used (×3 flip)</th>
              <th>non-3 factors</th>
            </tr>
          </thead>
          <tbody>
            {flipRows.map((r) => (
              <tr
                key={r.p}
                style={{ borderBottom: "1px solid #f0e6d8" }}
              >
                <td style={{ fontWeight: 700, color: NAVY }}>{r.p}</td>
                <td style={{ color: MUTED, opacity: 0.7 }}>
                  <code className="pow">{r.avoidedNode}</code>
                  <span style={{ marginLeft: 6, fontSize: "0.75em" }}>
                    m={r.avoidedM}
                  </span>
                </td>
                <td style={{ color: GREEN, fontWeight: 600 }}>
                  <code className="pow">{r.usedNode}</code>
                  <span style={{ marginLeft: 6, fontSize: "0.75em", color: MUTED }}>
                    m={r.usedM}
                  </span>
                </td>
                <td style={{ color: r.hiredNote !== "—" ? GREEN : MUTED }}>
                  {r.hiredNote}
                </td>
              </tr>
            ))}
          </tbody>
        </table>
      </div>

      <h2 style={{ fontSize: "1.1rem", marginTop: "1.4rem" }}>
        Spirals
      </h2>
      <p className="lede" style={{ fontSize: "0.95rem" }}>
        Launchers in S under door mode. Spirals only for members of S; other
        odd primes are passengers.
      </p>

      <div className="split-readout">
        <div>
          <div className="kv-label">|S| super primes</div>
          <div className="kv-value">{computed.S.length}</div>
        </div>
        <div>
          <div className="kv-label">odd primes ≤ N</div>
          <div className="kv-value">{computed.oddPrimes.length}</div>
        </div>
        <div>
          <div className="kv-label">passengers (no launch)</div>
          <div className="kv-value">{computed.passengers.length}</div>
        </div>
        <div>
          <div className="kv-label">max(S)</div>
          <div className="kv-value">{computed.maxS || "—"}</div>
        </div>
      </div>
      <p className="hint" style={{ marginTop: 0 }}>
        {expectNote}. Mode:{" "}
        {mode === "strict"
          ? "strict (+3 seat, no ×3)"
          : "+1 only (still no ×3)"}.
      </p>

      <div className={view3d ? "graph3d" : "graph2d"} style={{ height: 480 }}>
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
          <span>N max (odd primes ≤ N)</span>
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
          <span>spiral tightness (step)</span>
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
          <span>door mode</span>
          <select
            value={mode}
            onChange={(e) => setMode(e.target.value as DoorMode)}
          >
            <option value="strict">strict: +3 seat, forbid ×3</option>
            <option value="plus1-no3factor">+1 only (still forbid ×3)</option>
          </select>
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
          Orange diamonds launch; light lines mark their multiples (pass-throughs);
          muted open diamonds are odd primes that never open a spiral. Turn size
          follows the Archimedean rule th = n × step, same spirit as the Primes
          page.
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
          <strong style={{ color: MAROON }}>Rule (seat 3, no ×3).</strong>{" "}
          Write p = m + d with d = 1 or d = 3 (prefer 3). Require 3 does not
          divide m. New prime factors of m join S and launch. 3 is never in S.
          Seed: 3 = 2 + 1.
        </blockquote>
      </div>
    </main>
  );
}
