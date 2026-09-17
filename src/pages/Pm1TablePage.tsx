import { useMemo, useState, type ReactNode } from "react";
import { MAROON, NAVY, PAPER } from "../lib/plotTheme";

const GREEN = "#2f6b4f";
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

const SUP_DIGITS = "⁰¹²³⁴⁵⁶⁷⁸⁹";
function toSup(n: number): string {
  return String(n)
    .split("")
    .map((d) => SUP_DIGITS[Number(d)] ?? d)
    .join("");
}

function fmtParts(parts: number[]): string {
  if (parts.length === 0) return "—";
  // collapse runs: 2,2,2 -> 2³
  const counts = new Map<number, number>();
  for (const p of parts) counts.set(p, (counts.get(p) ?? 0) + 1);
  return [...counts.entries()]
    .map(([p, e]) => (e === 1 ? String(p) : `${p}${toSup(e)}`))
    .join(" · ");
}

function fmtPartsEl(parts: number[]): ReactNode {
  if (parts.length === 0) return "—";
  const counts = new Map<number, number>();
  for (const p of parts) counts.set(p, (counts.get(p) ?? 0) + 1);
  return [...counts.entries()].map(([base, e], i) => (
    <span key={`${base}-${e}-${i}`}>
      {i > 0 ? " · " : null}
      {e === 1 ? (
        base
      ) : (
        <>
          {base}
          <sup>{e}</sup>
        </>
      )}
    </span>
  ));
}

function writingEl(legal: "plus" | "minus" | "seed", parts: number[], fallback: string): ReactNode {
  if (legal === "seed") return fallback;
  return (
    <>
      {fmtPartsEl(parts)}
      {legal === "plus" ? " + 1" : " − 1"}
    </>
  );
}

type Row = {
  p: number;
  mMinus: number; // p-1
  mPlus: number; // p+1
  minusHas3: boolean;
  plusHas3: boolean;
  legal: "plus" | "minus" | "seed";
  m: number;
  parts: number[];
  writing: string;
  writingNode: ReactNode;
};

function buildRows(N: number): Row[] {
  const odds = primesUpTo(N).filter((p) => p >= 3);
  const rows: Row[] = [];
  for (const p of odds) {
    const mMinus = p - 1;
    const mPlus = p + 1;
    const minusHas3 = mMinus % 3 === 0;
    const plusHas3 = mPlus % 3 === 0;
    if (p === 3) {
      rows.push({
        p,
        mMinus,
        mPlus,
        minusHas3,
        plusHas3,
        legal: "seed",
        m: 2,
        parts: [2],
        writing: "2 + 1",
        writingNode: "2 + 1",
      });
      continue;
    }
    // unique legal door for p>3
    const legal: "plus" | "minus" = minusHas3 ? "minus" : "plus";
    const m = legal === "plus" ? mMinus : mPlus;
    const parts = factorParts(m);
    const prod = fmtParts(parts);
    const writing = legal === "plus" ? `${prod} + 1` : `${prod} − 1`;
    rows.push({
      p,
      mMinus,
      mPlus,
      minusHas3,
      plusHas3,
      legal,
      m,
      parts,
      writing,
      writingNode: writingEl(legal, parts, writing),
    });
  }
  return rows;
}

function compositesUpTo(N: number): { with3: number[]; without3: number[] } {
  const isP = new Set(primesUpTo(N));
  const with3: number[] = [];
  const without3: number[] = [];
  for (let n = 4; n <= N; n++) {
    if (isP.has(n)) continue;
    if (n % 3 === 0) with3.push(n);
    else without3.push(n);
  }
  return { with3, without3 };
}

const DEFAULT_N = 100;

export function Pm1TablePage() {
  const [N, setN] = useState(DEFAULT_N);
  const rows = useMemo(() => buildRows(N), [N]);
  const comps = useMemo(() => compositesUpTo(N), [N]);

  // legal midranges that actually seat a prime ≤ N
  const legalMs = useMemo(() => new Set(rows.map((r) => r.m)), [rows]);

  return (
    <main className="page">
      <h1>±1 table — fire 3, unique door</h1>
      <p className="lede">
        For each odd prime p≤N: both neighbours p−1 and p+1. Exactly one carries
        the factor 3 when p&gt;3 (three consecutive integers). That neighbour is
        banned; the other is the legal even midrange m. Writing is m±1 with 3
        fired. Below: composites ≤N split by whether 3 divides them — legal
        midranges live only in the without-3 column (and are even).
      </p>

      <div className="split-readout">
        <div>
          <div className="kv-label">N</div>
          <div className="kv-value">{N}</div>
        </div>
        <div>
          <div className="kv-label">odd primes</div>
          <div className="kv-value">{rows.length}</div>
        </div>
        <div>
          <div className="kv-label">composites with 3</div>
          <div className="kv-value" style={{ color: MAROON }}>
            {comps.with3.length}
          </div>
        </div>
        <div>
          <div className="kv-label">composites without 3</div>
          <div className="kv-value" style={{ color: GREEN }}>
            {comps.without3.length}
          </div>
        </div>
      </div>

      <div className="panel">
        <label className="row">
          <span>N</span>
          <span>{N}</span>
        </label>
        <input
          type="range"
          min={20}
          max={200}
          step={1}
          value={N}
          onChange={(e) => setN(parseInt(e.target.value, 10))}
        />
      </div>

      <h2 style={{ fontSize: "1.1rem", marginTop: "1.2rem" }}>
        Odd primes — both neighbours, legal ±1
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
              <th>p</th>
              <th>p−1</th>
              <th>has 3?</th>
              <th>p+1</th>
              <th>has 3?</th>
              <th>legal m</th>
              <th>door</th>
              <th>writing</th>
            </tr>
          </thead>
          <tbody>
            {rows.map((r) => (
              <tr key={r.p} style={{ borderBottom: "1px solid #f0e6d8" }}>
                <td style={{ fontWeight: 600 }}>{r.p}</td>
                <td
                  style={{
                    color: r.minusHas3 ? MAROON : NAVY,
                    textDecoration: r.minusHas3 ? "line-through" : undefined,
                    opacity: r.minusHas3 ? 0.55 : 1,
                  }}
                >
                  {r.mMinus}
                </td>
                <td style={{ color: r.minusHas3 ? MAROON : GREEN }}>
                  {r.minusHas3 ? "yes — ban" : "no"}
                </td>
                <td
                  style={{
                    color: r.plusHas3 ? MAROON : NAVY,
                    textDecoration: r.plusHas3 ? "line-through" : undefined,
                    opacity: r.plusHas3 ? 0.55 : 1,
                  }}
                >
                  {r.mPlus}
                </td>
                <td style={{ color: r.plusHas3 ? MAROON : GREEN }}>
                  {r.plusHas3 ? "yes — ban" : "no"}
                </td>
                <td style={{ color: GREEN, fontWeight: 600 }}>{r.m}</td>
                <td>{r.legal === "seed" ? "seed" : r.legal === "plus" ? "+1" : "−1"}</td>
                <td>
                  <code className="pow">{r.writingNode}</code>
                </td>
              </tr>
            ))}
          </tbody>
        </table>
      </div>

      <h2 style={{ fontSize: "1.1rem", marginTop: "1.4rem" }}>
        Composites ≤{N} — with 3 vs without 3
      </h2>
      <p className="lede" style={{ fontSize: "0.95rem" }}>
        Maroon list: 3 divides n (banned as midrange under fire-3). Green list:
        3 does not divide n. Bold green numbers are legal midranges that actually
        seat an odd prime ≤{N} via the ±1 rule.
      </p>
      <div
        style={{
          display: "grid",
          gridTemplateColumns: "1fr 1fr",
          gap: "1rem",
        }}
      >
        <div className="panel">
          <div className="kv-label" style={{ color: MAROON, marginBottom: "0.5rem" }}>
            with 3 (banned midranges)
          </div>
          <p style={{ margin: 0, lineHeight: 1.7, color: MUTED, fontSize: "0.9rem" }}>
            {comps.with3.map((n) => (
              <span key={n} style={{ marginRight: "0.45rem" }}>
                {n}
              </span>
            ))}
          </p>
        </div>
        <div className="panel" style={{ background: PAPER }}>
          <div className="kv-label" style={{ color: GREEN, marginBottom: "0.5rem" }}>
            without 3 (allowed midrange pool)
          </div>
          <p style={{ margin: 0, lineHeight: 1.7, fontSize: "0.9rem" }}>
            {comps.without3.map((n) => {
              const legal = legalMs.has(n);
              return (
                <span
                  key={n}
                  style={{
                    marginRight: "0.45rem",
                    fontWeight: legal ? 700 : 400,
                    color: legal ? GREEN : MUTED,
                  }}
                >
                  {n}
                </span>
              );
            })}
          </p>
        </div>
      </div>
    </main>
  );
}
