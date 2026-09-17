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

/** Strict seat-3 S built while walking odd primes ≤ buildN. */
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

function sieveSurvivors(N: number, bases: number[]): {
  suspects: number[];
  claimed: number;
} {
  const hit = new Uint8Array(N + 1);
  for (const b of bases) {
    if (b < 2 || b > N) continue;
    for (let n = b; n <= N; n += b) hit[n] = 1;
  }
  const suspects: number[] = [];
  let claimed = 0;
  for (let n = 2; n <= N; n++) {
    if (hit[n]) claimed++;
    else suspects.push(n);
  }
  return { suspects, claimed };
}

function isPrime(n: number): boolean {
  if (n < 2) return false;
  if (n % 2 === 0) return n === 2;
  const lim = Math.floor(Math.sqrt(n));
  for (let d = 3; d <= lim; d += 2) if (n % d === 0) return false;
  return true;
}

function isPowerOf3(n: number): boolean {
  if (n < 3) return false;
  let x = n;
  while (x % 3 === 0) x = Math.floor(x / 3);
  return x === 1;
}

type Bench = {
  label: string;
  bases: number[];
  includes3: boolean;
  suspects: number[];
  claimed: number;
  truePrimes: number;
  falseSuspects: number;
  pow3: number;
  rejectPct: number;
  falseDensity: number;
};

function score(label: string, bases: number[], N: number): Bench {
  const { suspects, claimed } = sieveSurvivors(N, bases);
  let truePrimes = 0;
  let falseSuspects = 0;
  let pow3 = 0;
  for (const n of suspects) {
    if (isPowerOf3(n)) pow3++;
    if (isPrime(n)) truePrimes++;
    else falseSuspects++;
  }
  const total = Math.max(1, N - 1);
  return {
    label,
    bases,
    includes3: bases.includes(3),
    suspects,
    claimed,
    truePrimes,
    falseSuspects,
    pow3,
    rejectPct: (100 * claimed) / total,
    falseDensity: falseSuspects / total,
  };
}

/** First index where sorted S differs from primes except 3 (both capped at maxS). */
function divergence(S: number[]): {
  index: number;
  sVal: number | null;
  pVal: number | null;
  missing: number[];
  matchLen: number;
} {
  if (S.length === 0) {
    return { index: 0, sVal: null, pVal: null, missing: [], matchLen: 0 };
  }
  const maxS = S[S.length - 1];
  const P = primesUpTo(maxS).filter((p) => p !== 3);
  let i = 0;
  while (i < S.length && i < P.length && S[i] === P[i]) i++;
  const Sset = new Set(S);
  const missing = P.filter((x) => !Sset.has(x));
  return {
    index: i,
    sVal: S[i] ?? null,
    pVal: P[i] ?? null,
    missing: missing.slice(0, 24),
    matchLen: i,
  };
}

const DEFAULT_N = 500;
const DEFAULT_K = 8;

export function SuspectBenchPage() {
  const [N, setN] = useState(DEFAULT_N);
  const [k, setK] = useState(DEFAULT_K);

  const bench = useMemo(() => {
    /** Honest walk: build S from primes ≤ N only (no padding build). */
    const allPrimes = primesUpTo(N);
    const S = computeStrictS(N);
    const div = divergence(S);

    const strictK = S.slice(0, k);
    const firstK = allPrimes.slice(0, k);
    const classicalNo3 = allPrimes.filter((p) => p !== 3).slice(0, k);
    /** Cheat hybrid: first (k−1) of S, then force-add seat 3 as a frequency. */
    const hybrid = [
      ...new Set([...S.slice(0, Math.max(0, k - 1)), 3]),
    ].sort((a, b) => a - b);

    const A = score("strict S (first k)", strictK, N);
    const B = score("ordinary primes (first k)", firstK, N);
    const C = score("primes except 3 (first k)", classicalNo3, N);
    const H = score("hybrid: S(k−1) + force 3", hybrid, N);

    /** Full-spectrum arms: |S| budget, S built at N. */
    const m = S.length;
    const fullS = score("full strict S", S, N);
    const fullOrd = score("ordinary primes (|S|)", allPrimes.slice(0, m), N);
    const fullNo3 = score(
      "primes except 3 (|S|)",
      allPrimes.filter((p) => p !== 3).slice(0, m),
      N
    );

    return {
      A,
      B,
      C,
      H,
      fullS,
      fullOrd,
      fullNo3,
      S,
      strictK,
      firstK,
      classicalNo3,
      hybrid,
      div,
      m,
    };
  }, [N, k]);

  /** False-suspect density vs N for a few sample points (cheap sweep). */
  const densitySweep = useMemo(() => {
    const xs: number[] = [];
    for (let n = 100; n <= Math.min(N, 2000); n += 100) xs.push(n);
    if (!xs.includes(N) && N <= 5000) xs.push(N);
    const yS: number[] = [];
    const yOrd: number[] = [];
    const yNo3: number[] = [];
    const yHyb: number[] = [];
    for (const n of xs) {
      const Sn = computeStrictS(n);
      const Pk = primesUpTo(n);
      const sk = Sn.slice(0, k);
      const ok = Pk.slice(0, k);
      const nk = Pk.filter((p) => p !== 3).slice(0, k);
      const hy = [
        ...new Set([...Sn.slice(0, Math.max(0, k - 1)), 3]),
      ].sort((a, b) => a - b);
      yS.push(score("", sk, n).falseDensity);
      yOrd.push(score("", ok, n).falseDensity);
      yNo3.push(score("", nk, n).falseDensity);
      yHyb.push(score("", hy, n).falseDensity);
    }
    return { xs, yS, yOrd, yNo3, yHyb };
  }, [N, k]);

  const equalKRows = [bench.A, bench.B, bench.C, bench.H];
  const fullRows = [bench.fullS, bench.fullOrd, bench.fullNo3];

  const barData: Data[] = useMemo(
    () => [
      {
        type: "bar",
        name: "reject %",
        x: equalKRows.map((r) => r.label),
        y: equalKRows.map((r) => r.rejectPct),
        marker: { color: MAROON },
      },
      {
        type: "bar",
        name: "suspect count",
        x: equalKRows.map((r) => r.label),
        y: equalKRows.map((r) => r.suspects.length),
        marker: { color: NAVY },
        yaxis: "y2",
      },
    ],
    // eslint-disable-next-line react-hooks/exhaustive-deps
    [bench]
  );

  const fullBarData: Data[] = useMemo(
    () => [
      {
        type: "bar",
        name: "reject %",
        x: fullRows.map((r) => r.label),
        y: fullRows.map((r) => r.rejectPct),
        marker: { color: MAROON },
      },
      {
        type: "bar",
        name: "false suspects",
        x: fullRows.map((r) => r.label),
        y: fullRows.map((r) => r.falseSuspects),
        marker: { color: ORANGE },
        yaxis: "y2",
      },
    ],
    // eslint-disable-next-line react-hooks/exhaustive-deps
    [bench]
  );

  const densData: Data[] = useMemo(
    () => [
      {
        type: "scatter",
        mode: "lines+markers",
        name: "strict S (first k)",
        x: densitySweep.xs,
        y: densitySweep.yS,
        line: { color: NAVY },
      },
      {
        type: "scatter",
        mode: "lines+markers",
        name: "ordinary (first k)",
        x: densitySweep.xs,
        y: densitySweep.yOrd,
        line: { color: MAROON },
      },
      {
        type: "scatter",
        mode: "lines+markers",
        name: "primes except 3",
        x: densitySweep.xs,
        y: densitySweep.yNo3,
        line: { color: GREEN, dash: "dot" },
      },
      {
        type: "scatter",
        mode: "lines+markers",
        name: "hybrid + force 3",
        x: densitySweep.xs,
        y: densitySweep.yHyb,
        line: { color: ORANGE },
      },
    ],
    [densitySweep]
  );

  const barLayout: Partial<Layout> = {
    paper_bgcolor: CREAM,
    plot_bgcolor: PAPER,
    barmode: "group",
    margin: { l: 50, r: 55, t: 40, b: 100 },
    title: {
      text: "Equal budget k — honest S built from primes ≤ N",
      font: { size: 13, family: "Georgia, serif" },
    },
    yaxis: { title: { text: "reject %" }, rangemode: "tozero" },
    yaxis2: {
      title: { text: "suspects" },
      overlaying: "y",
      side: "right",
      rangemode: "tozero",
    },
    legend: { orientation: "h", y: -0.45 },
    font: { family: "Georgia, Palatino, serif" },
  };

  const fullLayout: Partial<Layout> = {
    ...barLayout,
    title: {
      text: `Full spectrum — budget |S|=${bench.m} (S from walk ≤ N)`,
      font: { size: 13, family: "Georgia, serif" },
    },
    yaxis2: {
      title: { text: "false suspects" },
      overlaying: "y",
      side: "right",
      rangemode: "tozero",
    },
  };

  const densLayout: Partial<Layout> = {
    paper_bgcolor: CREAM,
    plot_bgcolor: PAPER,
    margin: { l: 55, r: 20, t: 40, b: 50 },
    title: {
      text: "False-suspect density (false / (N−1)) vs N, fixed k",
      font: { size: 13, family: "Georgia, serif" },
    },
    xaxis: { title: { text: "N" } },
    yaxis: { title: { text: "false density" }, rangemode: "tozero" },
    legend: { orientation: "h", y: -0.25 },
    font: { family: "Georgia, Palatino, serif" },
  };

  const sameAsNo3 =
    bench.strictK.length === bench.classicalNo3.length &&
    bench.strictK.every((v, i) => v === bench.classicalNo3[i]);

  return (
    <main className="page">
      <h1>Suspect bench — cheap reject, then test</h1>
      <p className="lede">
        Base sieve of frequencies marks claimed composites; survivors are{" "}
        <strong>suspects</strong>. Under seat-3 / no ×3, <strong>3 never joins
        S</strong> (instrument news in RH “needed frequencies” costume — not an
        RH claim). S is a <em>proper subset</em> of the primes except 3: early
        lists can look identical, then S skips primes the walk never needed as
        launchers.
      </p>

      <div className="split-readout">
        <div>
          <div className="kv-label">N</div>
          <div className="kv-value">{N}</div>
        </div>
        <div>
          <div className="kv-label">budget k</div>
          <div className="kv-value">{k}</div>
        </div>
        <div>
          <div className="kv-label">|S| at N</div>
          <div className="kv-value">{bench.m}</div>
        </div>
        <div>
          <div className="kv-label">first-k S = primes∖3?</div>
          <div className="kv-value" style={{ color: sameAsNo3 ? GREEN : MAROON }}>
            {sameAsNo3 ? "yes" : "no"}
          </div>
        </div>
      </div>

      <div className="panel" style={{ marginBottom: "1rem" }}>
        <p className="hint" style={{ margin: 0 }}>
          <strong>Divergence.</strong> Sorted S matches primes-except-3 for the
          first {bench.div.matchLen} entries
          {bench.div.sVal != null ? (
            <>
              ; at index {bench.div.index} S has {bench.div.sVal} while
              primes∖3 has {bench.div.pVal}. Missed launchers (in primes∖3, not
              in S): {bench.div.missing.join(", ") || "—"}.
            </>
          ) : (
            <>.</>
          )}{" "}
          onlyInS stays empty: every super is an ordinary prime ≠ 3.
        </p>
      </div>

      <div className="graph2d" style={{ height: 380 }}>
        <Plot
          data={barData}
          layout={barLayout}
          config={plotConfig}
          style={{ width: "100%", height: "100%" }}
          useResizeHandler
        />
      </div>

      <div className="panel">
        <label className="row">
          <span>N (sieve + honest S walk ≤ N)</span>
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
          <span>budget k (equal-k arms)</span>
          <span>{k}</span>
        </label>
        <input
          type="range"
          min={2}
          max={40}
          step={1}
          value={k}
          onChange={(e) => setK(parseInt(e.target.value, 10))}
        />

        <table
          style={{
            width: "100%",
            borderCollapse: "collapse",
            marginTop: "0.8rem",
            fontSize: "0.9rem",
          }}
        >
          <thead>
            <tr style={{ textAlign: "left", borderBottom: "1px solid #e2d8c8" }}>
              <th>sieve</th>
              <th>reject %</th>
              <th>suspects</th>
              <th>true primes</th>
              <th>false</th>
              <th>3-powers</th>
              <th>has 3?</th>
            </tr>
          </thead>
          <tbody>
            {equalKRows.map((r) => (
              <tr key={r.label} style={{ borderBottom: "1px solid #f0e6d8" }}>
                <td>{r.label}</td>
                <td>{r.rejectPct.toFixed(1)}%</td>
                <td>{r.suspects.length}</td>
                <td>{r.truePrimes}</td>
                <td>{r.falseSuspects}</td>
                <td>{r.pow3}</td>
                <td style={{ color: r.includes3 ? MAROON : GREEN }}>
                  {r.includes3 ? "yes" : "no"}
                </td>
              </tr>
            ))}
          </tbody>
        </table>

        <p className="hint" style={{ marginTop: "0.9rem" }}>
          <strong>strict first k:</strong> {bench.strictK.join(", ") || "—"}
        </p>
        <p className="hint">
          <strong>ordinary first k:</strong> {bench.firstK.join(", ") || "—"}
        </p>
        <p className="hint">
          <strong>primes except 3:</strong>{" "}
          {bench.classicalNo3.join(", ") || "—"}
        </p>
        <p className="hint">
          <strong>hybrid (force 3):</strong> {bench.hybrid.join(", ") || "—"}
        </p>
      </div>

      <h2 style={{ marginTop: "1.4rem", fontSize: "1.15rem" }}>
        Full S spectrum (budget = |S|)
      </h2>
      <p className="lede" style={{ fontSize: "0.95rem" }}>
        Same walk’s complete launcher set versus the first |S| ordinary primes
        (with and without 3). This is where a sparse S can look different from
        “just drop 3.”
      </p>
      <div className="graph2d" style={{ height: 360 }}>
        <Plot
          data={fullBarData}
          layout={fullLayout}
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
              <th>sieve</th>
              <th>|bases|</th>
              <th>reject %</th>
              <th>suspects</th>
              <th>false</th>
              <th>has 3?</th>
            </tr>
          </thead>
          <tbody>
            {fullRows.map((r) => (
              <tr key={r.label} style={{ borderBottom: "1px solid #f0e6d8" }}>
                <td>{r.label}</td>
                <td>{r.bases.length}</td>
                <td>{r.rejectPct.toFixed(1)}%</td>
                <td>{r.suspects.length}</td>
                <td>{r.falseSuspects}</td>
                <td style={{ color: r.includes3 ? MAROON : GREEN }}>
                  {r.includes3 ? "yes" : "no"}
                </td>
              </tr>
            ))}
          </tbody>
        </table>
      </div>

      <h2 style={{ marginTop: "1.4rem", fontSize: "1.15rem" }}>
        False-suspect density vs N
      </h2>
      <div className="graph2d" style={{ height: 340 }}>
        <Plot
          data={densData}
          layout={densLayout}
          config={plotConfig}
          style={{ width: "100%", height: "100%" }}
          useResizeHandler
        />
      </div>

      <div className="panel">
        <p className="hint">
          Read: when first-k S matches primes∖3, the equal-k gap vs ordinary is
          just “no 3.” Hybrid asks whether forcing the seat back as a frequency
          buys the classical reject without putting 3 in S. Full-S rows ask
          whether the sparse launcher set (missed primes never needed for the
          covering walk) is a better or worse sieve than the densest |S|
          ordinary primes.
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
          <strong style={{ color: MAROON }}>News (instrument).</strong> 3 is
          never a needed launcher. S is always inside the primes except 3, and S is usually
          proper: the walk skips primes that never appear as missing factors.
          RH “frequencies” language is a metaphor for that spectrum.
        </blockquote>
      </div>
    </main>
  );
}
