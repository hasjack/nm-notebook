import { Link } from "react-router-dom";
import { ingredientTransitionData as data } from "../lib/ingredientTransitionData";
import "./DoorCoveragePage.css";

const fmt = (n: number) => n.toLocaleString("en-GB");

function fmtFactors(f: Record<string, number>): string {
  return Object.entries(f)
    .sort((a, b) => Number(a[0]) - Number(b[0]))
    .map(([p, e]) => (e === 1 ? p : `${p}^${e}`))
    .join(" · ");
}

/** Bar chart: share of consecutive doors that reuse an odd factor, by door gap. */
function GapFilterChart() {
  const rows = data.gaps.filter((g) => g.gap <= 40);
  const W = 680;
  const H = 260;
  const pad = { l: 44, r: 16, t: 28, b: 40 };
  const iw = W - pad.l - pad.r;
  const ih = H - pad.t - pad.b;
  const maxPct = 50;
  const barW = iw / rows.length;

  return (
    <figure className="power-firing-chart">
      <svg
        viewBox={`0 0 ${W} ${H}`}
        role="img"
        aria-label="Share of consecutive doors with a shared odd factor, by door gap"
      >
        <title>Reuse share by door gap Δ</title>
        <line
          x1={pad.l}
          y1={pad.t + ih}
          x2={pad.l + iw}
          y2={pad.t + ih}
          stroke="#8a7a68"
          strokeWidth="1"
        />
        <line
          x1={pad.l}
          y1={pad.t}
          x2={pad.l}
          y2={pad.t + ih}
          stroke="#8a7a68"
          strokeWidth="1"
        />
        {[0, 10, 20, 30, 40].map((v) => {
          const y = pad.t + ih * (1 - v / maxPct);
          return (
            <g key={v}>
              <line
                x1={pad.l}
                y1={y}
                x2={pad.l + iw}
                y2={y}
                stroke="#e6ddd0"
                strokeWidth="1"
              />
              <text
                x={pad.l - 6}
                y={y + 4}
                textAnchor="end"
                fontSize="11"
                fill="#6b5e4e"
              >
                {v}%
              </text>
            </g>
          );
        })}
        {rows.map((g, i) => {
          const h = (g.sharePct / maxPct) * ih;
          const x = pad.l + i * barW + barW * 0.15;
          const w = barW * 0.7;
          const y = pad.t + ih - h;
          const forced = g.sharePct === 0;
          return (
            <g key={g.gap}>
              <rect
                x={x}
                y={forced ? pad.t + ih - 2 : y}
                width={w}
                height={forced ? 2 : h}
                fill={forced ? "#c8bfb0" : "#1f5f8b"}
                rx="1"
              />
              {(g.gap <= 30 || g.gap % 10 === 0) && (
                <text
                  x={x + w / 2}
                  y={pad.t + ih + 14}
                  textAnchor="middle"
                  fontSize="10"
                  fill="#3d3428"
                >
                  {g.gap}
                </text>
              )}
            </g>
          );
        })}
        <text x={pad.l + iw / 2} y={H - 6} textAnchor="middle" fontSize="12" fill="#6b5e4e">
          Door gap Δ
        </text>
      </svg>
      <figcaption className="figure-caption">
        Share of consecutive doors that reuse an odd prime factor, by door gap.
        Flat zeros where Δ is only 2 and 3 — reuse is forbidden. Gap 10 may
        reuse 5 (~28%); gap 14 may reuse 7 (~16%). Permission, not a cycle.
      </figcaption>
    </figure>
  );
}

/** Lab: ingredient changes between consecutive prime doors. */
export function IngredientTransitionsPage() {
  return (
    <main className="page notes lab-note-page door-coverage-page">
      <h1>Ingredient transitions</h1>
      <p className="lede">
        How the whole door factorisation changes between consecutive primes —
        not how often one power fires. Related:{" "}
        <Link to="/power-firing">Power firing</Link>,{" "}
        <Link to="/door-waits">Door waits</Link>,{" "}
        <Link to="/two-class">Two-class coverage</Link>.
      </p>

      <h2>Why it feels abrupt</h2>
      <p>
        Exact census through {fmt(data.limit)}: {fmt(data.pairs)} consecutive
        prime pairs starting at 5. Exclude the universal factor 2. Then{" "}
        {data.disjointPct}% of neighbours share no odd prime factor at all;{" "}
        {data.forcedDisjointPct}% are forced to that by the door gap alone
        (Δ = 2<sup>a</sup>·3<sup>b</sup>). Largest odd factor jumps tenfold up
        in {data.largestUp10xPct}% of pairs and tenfold down in{" "}
        {data.largestDown10xPct}%.
      </p>
      <p>
        The punchline is arithmetic: if consecutive doors are <em>d</em> and{" "}
        <em>d</em>+Δ, then gcd(<em>d</em>, <em>d</em>+Δ) = gcd(<em>d</em>, Δ).
        Every shared odd ingredient must divide the gap. Since 3 never enters a
        door, a gap built only from 2 and 3 forces a full odd swap. Small gaps
        filter reuse; they do not beat a drum.
      </p>

      <GapFilterChart />

      <h2>Consecutive examples</h2>
      <div className="door-table-wrap">
        <table className="door-table">
          <thead>
            <tr>
              <th>Primes</th>
              <th>First door</th>
              <th>Next door</th>
              <th>Δ</th>
              <th>Largest ×</th>
            </tr>
          </thead>
          <tbody>
            {data.examples.map((e) => (
              <tr key={e.p}>
                <td>
                  {fmt(e.p)} → {fmt(e.next)}
                </td>
                <td>
                  {fmt(e.door)} = {fmtFactors(e.factors)}
                </td>
                <td>
                  {fmt(e.nextDoor)} = {fmtFactors(e.nextFactors)}
                </td>
                <td>{e.gap}</td>
                <td>{e.ratio.toFixed(2)}</td>
              </tr>
            ))}
          </tbody>
        </table>
      </div>

      <h2>By door gap</h2>
      <p>
        Gap 2–8, 12, 16, 18, … never share an odd factor. Gap 10 shares in
        27.98% of those pairs (only 5 is allowed); gap 14 shares in 15.87%
        (only 7). Larger gaps that admit several odd primes still share only
        when the next door actually sits on that residue.
      </p>
      <div className="door-table-wrap">
        <table className="door-table">
          <thead>
            <tr>
              <th>Δ</th>
              <th>Pairs</th>
              <th>Shared odd</th>
              <th>Share</th>
            </tr>
          </thead>
          <tbody>
            {data.gaps
              .filter((g) => g.gap <= 30)
              .map((g) => (
                <tr key={g.gap}>
                  <td>{g.gap}</td>
                  <td>{fmt(g.pairs)}</td>
                  <td>{fmt(g.shared)}</td>
                  <td>{g.sharePct.toFixed(2)}%</td>
                </tr>
              ))}
          </tbody>
        </table>
      </div>

      <details>
        <summary>Gaps through 100, and lag returns</summary>
        <div className="door-table-wrap">
          <table className="door-table">
            <thead>
              <tr>
                <th>Δ</th>
                <th>Pairs</th>
                <th>Shared</th>
                <th>Share</th>
              </tr>
            </thead>
            <tbody>
              {data.gaps.map((g) => (
                <tr key={`all-${g.gap}`}>
                  <td>{g.gap}</td>
                  <td>{fmt(g.pairs)}</td>
                  <td>{fmt(g.shared)}</td>
                  <td>{g.sharePct.toFixed(2)}%</td>
                </tr>
              ))}
            </tbody>
          </table>
        </div>
        <p>
          Overlap at fixed lag in the prime sequence (not integer distance).
          Immediate neighbours are the strictest seat; longer lags rise toward
          ~12% and flatten. That is a filter strength, not a repeating cycle.
        </p>
        <div className="door-table-wrap">
          <table className="door-table">
            <thead>
              <tr>
                <th>Lag</th>
                <th>Pairs</th>
                <th>Share with common odd factor</th>
              </tr>
            </thead>
            <tbody>
              {data.lags.map((r) => (
                <tr key={r.lag}>
                  <td>{r.lag}</td>
                  <td>{fmt(r.pairs)}</td>
                  <td>{r.sharePct.toFixed(2)}%</td>
                </tr>
              ))}
            </tbody>
          </table>
        </div>
      </details>

      <p className="lab-footnote">
        Exact sieve; every adjacent pair checked against the gcd identity.
        Findings only. Source: <code>analysis/ingredient-transitions/</code>.
      </p>
    </main>
  );
}
