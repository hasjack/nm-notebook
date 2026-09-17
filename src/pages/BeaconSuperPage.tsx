import { useMemo, useState } from "react";
import Plot from "../components/Plot";
import { fmt } from "../lib/format";
import { layout3d, plotConfig, traces3d } from "../lib/plotTheme";
import { resultAt } from "../lib/walk";

const SEAT = 3;
const SPINE = [1, 3, 5, 7, 9] as const;
const MAROON = "#9a2f38";
const NAVY = "#1f4e79";
const PAPER = "#fffaf3";

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

function fmtFactors(m: number): string {
  if (m < 2) return String(m);
  const parts: string[] = [];
  let x = m;
  while (x % 2 === 0) {
    parts.push("2");
    x = Math.floor(x / 2);
  }
  for (let f = 3; f * f <= x; f += 2) {
    while (x % f === 0) {
      parts.push(String(f));
      x = Math.floor(x / f);
    }
  }
  if (x > 1) parts.push(String(x));
  return parts.join("·");
}

type Intro = {
  added: number[];
  p: number;
  door: 1 | 3;
  m: number;
  writing: string;
  suggestedOdd: 1 | 3 | 5 | 7 | 9;
};

/** Strict seat-3 introductions up to maxN. */
function strictIntros(maxN: number): Intro[] {
  const odds = primesUpTo(maxN).filter((p) => p >= 3);
  const S = new Set<number>();
  const rows: Intro[] = [];

  const missingCost = (door: 1 | 3, p: number) => {
    const m = p - door;
    if (m < 2) return null;
    const facs = uniquePrimeFactors(m);
    if (facs.includes(SEAT)) return null;
    const missing = facs.filter((f) => !S.has(f));
    const sum = missing.reduce((a, b) => a + b, 0);
    return { missing, m, key: [missing.length, sum, door === 3 ? 0 : 1] as const };
  };

  for (const p of odds) {
    const c3 = missingCost(3, p);
    const c1 = missingCost(1, p);
    let best = c3 ?? c1;
    if (c1 && c3) best = c3.key <= c1.key ? c3 : c1;
    if (!best || best.missing.length === 0) continue;
    for (const f of best.missing) S.add(f);
    const door = (c3 && best === c3 ? 3 : 1) as 1 | 3;
    // Map door → suggested beacon odd (1 or 3); keep in spine
    const suggestedOdd = (door === 3 ? 3 : 1) as 1 | 3;
    rows.push({
      added: [...best.missing].sort((a, b) => a - b),
      p,
      door,
      m: best.m,
      writing: `${p} = ${fmtFactors(best.m)} + ${door}`,
      suggestedOdd,
    });
  }
  return rows;
}

function powersOf3UpTo(n: number): number[] {
  const out: number[] = [];
  let x = 3;
  while (x <= n) {
    out.push(x);
    x *= 3;
  }
  return out;
}

export function BeaconSuperPage() {
  const [maxN, setMaxN] = useState(200);
  const [rowIdx, setRowIdx] = useState(0);
  const [which, setWhich] = useState<"beta" | "alpha">("beta");
  const [oddOverride, setOddOverride] = useState<number | null>(null);
  const [mode, setMode] = useState<"intros" | "pow3">("intros");

  const intros = useMemo(() => strictIntros(maxN), [maxN]);
  const pow3 = useMemo(() => powersOf3UpTo(maxN), [maxN]);

  const safeIdx = Math.min(rowIdx, Math.max(0, intros.length - 1));
  const row = intros[safeIdx];

  const odd =
    mode === "pow3"
      ? 3
      : oddOverride ?? row?.suggestedOdd ?? 1;
  const base = Math.exp(odd);
  const alpha = which === "alpha" ? 1 / odd : 1;
  const beta = which === "beta" ? 1 / odd : 1;
  const product = alpha * beta;
  const pegProduct = product * Math.log(base); // should be 1 on spine snaps

  const data3d = useMemo(() => traces3d(product, base), [product, base]);

  // Rotation seat: t = odd half-turns lands on -1 for odd integers
  const tHalfTurns = odd;
  const rotLabel =
    tHalfTurns % 2 === 0
      ? "return (+1 family)"
      : "peg (−1 family)";

  return (
    <main className="page">
      <h1>Beacon × Super — probe</h1>
      <p className="lede">
        Run each strict super-prime introduction through the beacon machine
        (e^(odd) with twin 1/odd) and read the Rotation seat t = odd half-turns.
        Door +3 suggests odd = 3; door +1 suggests odd = 1. Control: powers of 3
        (unclaimed forever under seat-3 / no ×3) park on the odd = 3 snap and
        ask whether the machine still looks honest.
      </p>

      <div className="value">−1</div>
      <div className="expr">
        {"e^" + odd} ^ ({fmt(alpha, 4)} · i · {fmt(beta, 4)} π) · value{" "}
        {resultAt(product, base)}
      </div>
      <div className="rule">
        α·β·ln(base) = {fmt(pegProduct, 4)} (want 1) · Rotation t = {tHalfTurns}{" "}
        half-turns → {rotLabel}
      </div>

      <div className="split-readout">
        <div>
          <div className="kv-label">beacon odd</div>
          <div className="kv-value">{odd}</div>
        </div>
        <div>
          <div className="kv-label">base</div>
          <div className="kv-value">{"e^" + odd}</div>
        </div>
        <div>
          <div className="kv-label">α</div>
          <div className="kv-value">{fmt(alpha, 5)}</div>
        </div>
        <div>
          <div className="kv-label">β</div>
          <div className="kv-value">{fmt(beta, 5)}</div>
        </div>
      </div>

      <div className="graph3d">
        <Plot
          data={data3d}
          layout={layout3d}
          config={plotConfig}
          style={{ width: "100%", height: "100%" }}
          useResizeHandler
        />
      </div>

      <div className="panel">
        <div className="modes" style={{ display: "flex", gap: "0.4rem", flexWrap: "wrap" }}>
          <button
            type="button"
            onClick={() => {
              setMode("intros");
              setOddOverride(null);
            }}
            style={{
              background: mode === "intros" ? NAVY : "#fffaf3",
              color: mode === "intros" ? "#fff" : "#1a1a1a",
              border: "1px solid #e2d8c8",
              borderRadius: 8,
              padding: "0.35rem 0.75rem",
              font: "inherit",
              cursor: "pointer",
            }}
          >
            Super introductions
          </button>
          <button
            type="button"
            onClick={() => {
              setMode("pow3");
              setOddOverride(3);
            }}
            style={{
              background: mode === "pow3" ? NAVY : "#fffaf3",
              color: mode === "pow3" ? "#fff" : "#1a1a1a",
              border: "1px solid #e2d8c8",
              borderRadius: 8,
              padding: "0.35rem 0.75rem",
              font: "inherit",
              cursor: "pointer",
            }}
          >
            Control: 3-powers
          </button>
        </div>

        {mode === "intros" && row && (
          <>
            <p className="hint" style={{ marginTop: "0.8rem" }}>
              Row {safeIdx + 1} / {intros.length}: added{" "}
              <strong>{row.added.join(", ")}</strong> · {row.writing} · suggested
              beacon odd = {row.suggestedOdd}
            </p>
            <div className="actions" style={{ display: "flex", gap: "0.4rem" }}>
              <button
                type="button"
                disabled={safeIdx <= 0}
                onClick={() => {
                  setRowIdx((i) => Math.max(0, i - 1));
                  setOddOverride(null);
                }}
              >
                Prev
              </button>
              <button
                type="button"
                disabled={safeIdx >= intros.length - 1}
                onClick={() => {
                  setRowIdx((i) => Math.min(intros.length - 1, i + 1));
                  setOddOverride(null);
                }}
              >
                Next
              </button>
            </div>
            <label className="row">
              <span>step intro</span>
              <span>
                {safeIdx + 1}/{intros.length}
              </span>
            </label>
            <input
              type="range"
              min={0}
              max={Math.max(0, intros.length - 1)}
              step={1}
              value={safeIdx}
              onChange={(e) => {
                setRowIdx(parseInt(e.target.value, 10));
                setOddOverride(null);
              }}
            />
          </>
        )}

        {mode === "pow3" && (
          <p className="hint" style={{ marginTop: "0.8rem" }}>
            Powers of 3 ≤ N: {pow3.join(", ") || "—"}. None are divisible by any
            super (3 never launches). Beacon sits on odd = 3 (e³ · 1/3) — peg
            still −1, but the Archimedean story has no ×3 helix. That tension is
            the probe.
          </p>
        )}

        <label className="row" style={{ marginTop: "0.8rem" }}>
          <span>N for strict S table</span>
          <span>{maxN}</span>
        </label>
        <input
          type="range"
          min={50}
          max={500}
          step={10}
          value={maxN}
          onChange={(e) => {
            setMaxN(parseInt(e.target.value, 10));
            setRowIdx(0);
            setOddOverride(null);
          }}
        />

        <div className="modes" style={{ display: "flex", gap: "0.4rem", flexWrap: "wrap", marginTop: "0.6rem" }}>
          {SPINE.map((o) => (
            <button
              key={o}
              type="button"
              onClick={() => setOddOverride(o)}
              style={{
                background: odd === o ? NAVY : "#fffaf3",
                color: odd === o ? "#fff" : "#1a1a1a",
                border: "1px solid #e2d8c8",
                borderRadius: 8,
                padding: "0.35rem 0.75rem",
                font: "inherit",
                cursor: "pointer",
              }}
            >
              {"e^" + o + " · 1/" + o}
            </button>
          ))}
        </div>

        <label className="row" style={{ marginTop: "0.9rem" }}>
          <span>who takes the 1/odd?</span>
          <select
            value={which}
            onChange={(e) => setWhich(e.target.value as "beta" | "alpha")}
          >
            <option value="beta">π-factor β</option>
            <option value="alpha">i-factor α</option>
          </select>
        </label>

        <p className="hint">
          Kinship, not identity: additive seat +3 on integers vs beacon product
          odd. This page parks each strict intro on the matching odd snap so you
          can feel whether the machine agrees. Reset override by Prev/Next on
          introductions.
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
          <strong style={{ color: MAROON }}>Probe.</strong> Door +3 → try odd =
          3. Door +1 → try odd = 1. Peg stays −1 on the spine. Rotation t = odd
          half-turns. 3-powers: same odd = 3 beacon, no ×3 spiral in Unclaimed —
          that is the suspect control.
        </blockquote>
      </div>
    </main>
  );
}
