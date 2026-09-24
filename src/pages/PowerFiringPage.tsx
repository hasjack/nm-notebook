import { Link } from "react-router-dom";
import { powerFiringData as data } from "../lib/powerFiringData";
import "./DoorCoveragePage.css";

const fmt = (n: number | null | undefined) =>
  n == null ? "—" : n.toLocaleString("en-GB");

const fmtPct = (n: number | null | undefined) =>
  n == null ? "—" : `${n.toFixed(2)}%`;

type Row = (typeof data.rows)[number];

function rowsFor(q: number): Row[] {
  return data.rows.filter((r) => r.q === q);
}

/** Chart lanes with enough hits for a stable mean. */
function chartRows(q: number): Row[] {
  return rowsFor(q).filter((r) => r.meanGap != null && r.meanMisses != null && !r.sparse);
}

function PowerPeelChart({ q }: { q: number }) {
  const rows = chartRows(q);
  if (rows.length < 2) return null;

  const W = 640;
  const H = 280;
  const pad = { l: 58, r: 58, t: 28, b: 42 };
  const iw = W - pad.l - pad.r;
  const ih = H - pad.t - pad.b;

  const gaps = rows.map((r) => r.meanGap as number);
  const misses = rows.map((r) => r.meanMisses as number);
  const logMin = Math.log10(Math.min(...gaps) * 0.8);
  const logMax = Math.log10(Math.max(...gaps) * 1.15);
  const missMin = 0;
  const missMax = Math.max(4.5, Math.max(...misses) * 1.15);

  const xAt = (i: number) =>
    pad.l + (rows.length === 1 ? iw / 2 : (i / (rows.length - 1)) * iw);
  const yGap = (g: number) =>
    pad.t + ih * (1 - (Math.log10(g) - logMin) / (logMax - logMin));
  const yMiss = (m: number) =>
    pad.t + ih * (1 - (m - missMin) / (missMax - missMin));

  const gapPath = rows
    .map((r, i) => `${i ? "L" : "M"} ${xAt(i).toFixed(1)} ${yGap(r.meanGap as number).toFixed(1)}`)
    .join(" ");
  const missPath = rows
    .map(
      (r, i) =>
        `${i ? "L" : "M"} ${xAt(i).toFixed(1)} ${yMiss(r.meanMisses as number).toFixed(1)}`,
    )
    .join(" ");

  const logTicks = [];
  for (let e = Math.ceil(logMin); e <= Math.floor(logMax); e++) {
    logTicks.push(10 ** e);
  }
  const missTicks = [0, 1, 2, 3, 4];

  return (
    <figure className="power-firing-chart">
      <svg viewBox={`0 0 ${W} ${H}`} role="img" aria-label={`Number-line gap and eligible misses vs power of ${q}`}>
        <title>
          Mean number-line gap (log) and mean eligible misses vs power of {q}
        </title>
        {/* axes */}
        <line x1={pad.l} y1={pad.t} x2={pad.l} y2={pad.t + ih} stroke="#8a7a68" strokeWidth="1" />
        <line x1={pad.l + iw} y1={pad.t} x2={pad.l + iw} y2={pad.t + ih} stroke="#8a7a68" strokeWidth="1" />
        <line x1={pad.l} y1={pad.t + ih} x2={pad.l + iw} y2={pad.t + ih} stroke="#8a7a68" strokeWidth="1" />

        {logTicks.map((g) => (
          <g key={`g-${g}`}>
            <line
              x1={pad.l}
              y1={yGap(g)}
              x2={pad.l + iw}
              y2={yGap(g)}
              stroke="#e6ddd0"
              strokeWidth="1"
            />
            <text x={pad.l - 8} y={yGap(g) + 4} textAnchor="end" fontSize="11" fill="#6b5e4e">
              {g >= 1000 ? `${g / 1000}k` : g}
            </text>
          </g>
        ))}
        {missTicks.map((m) => (
          <text
            key={`m-${m}`}
            x={pad.l + iw + 8}
            y={yMiss(m) + 4}
            textAnchor="start"
            fontSize="11"
            fill="#6b5e4e"
          >
            {m}
          </text>
        ))}

        <path d={gapPath} fill="none" stroke="#1f5f8b" strokeWidth="2.25" />
        <path d={missPath} fill="none" stroke="#b85c38" strokeWidth="2.25" />

        {rows.map((r, i) => (
          <g key={r.power}>
            <circle cx={xAt(i)} cy={yGap(r.meanGap as number)} r="4" fill="#1f5f8b" />
            <circle cx={xAt(i)} cy={yMiss(r.meanMisses as number)} r="4" fill="#b85c38" />
            <text
              x={xAt(i)}
              y={pad.t + ih + 18}
              textAnchor="middle"
              fontSize="12"
              fill="#3d3428"
            >
              {q}
              <tspan baselineShift="super" fontSize="9">
                {r.exponent}
              </tspan>
            </text>
          </g>
        ))}

        <text x={pad.l} y={16} fontSize="12" fill="#1f5f8b">
          Mean number-line gap (log)
        </text>
        <text x={pad.l + iw} y={16} textAnchor="end" fontSize="12" fill="#b85c38">
          Mean eligible misses
        </text>
      </svg>
      <figcaption className="figure-caption">
        Sevens through {q}
        <sup>4</sup>: number-line gaps climb roughly ×{q} each power; opportunity
        waits sit flat near 3.3. Sparse higher powers omitted from the chart.
      </figcaption>
    </figure>
  );
}

function SuccessFlatChart({ q }: { q: number }) {
  const rows = chartRows(q);
  if (rows.length < 2) return null;
  const W = 640;
  const H = 160;
  const pad = { l: 48, r: 24, t: 24, b: 36 };
  const iw = W - pad.l - pad.r;
  const ih = H - pad.t - pad.b;
  const vals = rows.map((r) => r.successPct as number);
  const yMin = 20;
  const yMax = 26;
  const xAt = (i: number) =>
    pad.l + (rows.length === 1 ? iw / 2 : (i / (rows.length - 1)) * iw);
  const yAt = (v: number) => pad.t + ih * (1 - (v - yMin) / (yMax - yMin));
  const path = rows
    .map((r, i) => `${i ? "L" : "M"} ${xAt(i).toFixed(1)} ${yAt(r.successPct as number).toFixed(1)}`)
    .join(" ");

  return (
    <figure className="power-firing-chart thin">
      <svg viewBox={`0 0 ${W} ${H}`} role="img" aria-label={`Success percent vs power of ${q}`}>
        <title>Success per eligible position vs power of {q}</title>
        <line x1={pad.l} y1={pad.t + ih} x2={pad.l + iw} y2={pad.t + ih} stroke="#8a7a68" strokeWidth="1" />
        <line x1={pad.l} y1={pad.t} x2={pad.l} y2={pad.t + ih} stroke="#8a7a68" strokeWidth="1" />
        {[21, 23, 25].map((v) => (
          <g key={v}>
            <line x1={pad.l} y1={yAt(v)} x2={pad.l + iw} y2={yAt(v)} stroke="#e6ddd0" strokeWidth="1" />
            <text x={pad.l - 6} y={yAt(v) + 4} textAnchor="end" fontSize="11" fill="#6b5e4e">
              {v}%
            </text>
          </g>
        ))}
        <path d={path} fill="none" stroke="#2f6b4f" strokeWidth="2.25" />
        {rows.map((r, i) => (
          <g key={r.power}>
            <circle cx={xAt(i)} cy={yAt(r.successPct as number)} r="4" fill="#2f6b4f" />
            <text x={xAt(i)} y={pad.t + ih + 16} textAnchor="middle" fontSize="12" fill="#3d3428">
              {q}
              <tspan baselineShift="super" fontSize="9">
                {r.exponent}
              </tspan>
            </text>
          </g>
        ))}
      </svg>
      <figcaption className="figure-caption">
        Success per eligible seat stays near 23% across those powers — no extra
        cubic tax at the seats that can fire.
      </figcaption>
    </figure>
  );
}

function LaneTable({ q }: { q: number }) {
  const rows = rowsFor(q);
  return (
    <div className="door-table-wrap">
      <table className="door-table">
        <thead>
          <tr>
            <th>Power</th>
            <th>First prime</th>
            <th>Prior misses</th>
            <th>Hits</th>
            <th>Exact hits</th>
            <th>Success</th>
            <th>Mean gap</th>
            <th>Mean misses</th>
            <th>Next-power share</th>
          </tr>
        </thead>
        <tbody>
          {rows.map((r) => (
            <tr key={r.power} className={r.sparse ? "sparse-row" : undefined}>
              <td>
                {r.q}
                <sup>{r.exponent}</sup>
                {r.sparse ? " · thin" : ""}
              </td>
              <td>{r.firstPrime == null ? "not seen" : fmt(r.firstPrime)}</td>
              <td>{r.firstMisses == null ? "—" : fmt(r.firstMisses)}</td>
              <td>{fmt(r.hits)}</td>
              <td>{fmt(r.exactHits)}</td>
              <td>{fmtPct(r.successPct)}</td>
              <td>{r.meanGap == null ? "—" : fmt(r.meanGap)}</td>
              <td>{r.meanMisses == null ? "—" : r.meanMisses.toFixed(3)}</td>
              <td>{fmtPct(r.nextPowerPct)}</td>
            </tr>
          ))}
        </tbody>
      </table>
    </div>
  );
}

/** Lab: prime-power firing census next to door waits. */
export function PowerFiringPage() {

  return (
    <main className="page notes lab-note-page door-coverage-page">
      <h1>Power firing</h1>
      <p className="lede">
        First appearance, frequency, waiting, and company for powers{" "}
        <em>
          q, q<sup>2</sup>, q<sup>3</sup>, …
        </em>{" "}
        inside 3-free doors. Related: <Link to="/door-waits">Door waits</Link>,{" "}
        <Link to="/two-class">Two-class coverage</Link>,{" "}
        <Link to="/coverage-lattice">Coverage lattice</Link>,{" "}
        <Link to="/ingredient-transitions">Ingredient transitions</Link>.
      </p>

      <h2>What the census measures</h2>
      <p>
        Exact sieve through {fmt(data.limit)} ({fmt(data.totalPrimesGt3)} primes
        &gt; 3). Bases {data.bases.join(", ")}. A cumulative firing means{" "}
        <em>
          q<sup>e</sup>
        </em>{" "}
        divides <em>m₀(p)</em>; an exact firing excludes a further factor of{" "}
        <em>q</em>. Eligible seats use the two residues modulo 6<em>Q</em>.
        Success is prime hits over eligible seats, not over all integers.
        Finite-window findings only — sparse top powers are marked thin.
      </p>

      <h2>The peel</h2>
      <p>
        Number-line gaps stretch roughly <em>q</em>-fold with each power;
        opportunity waits stay flat. Hit rate per eligible seat barely moves.
        That is nest thinning, not a new cubic tax.
      </p>
      <PowerPeelChart q={7} />
      <SuccessFlatChart q={7} />
      <p>
        Company stays similar across those lanes: another factor of 5 appears in
        about 25% of the 7, 49, and 343 firings (25.04%, 24.98%, 24.69%).
        Next-power share among those sevens sits near 1/7 (14.24% / 14.28% /
        14.12%).
      </p>
      <p>
        First appearances are not forced: 13<sup>3</sup> misses four eligible
        seats before hiring 30,757; 17<sup>3</sup> misses five before 78,607.
      </p>

      <h2>Sevens</h2>
      <LaneTable q={7} />

      <details>
        <summary>Other bases (5, 11, 13, 17, 19)</summary>
        {[5, 11, 13, 17, 19].map((q) => (
          <div key={q}>
            <h3>Base {q}</h3>
            <LaneTable q={q} />
          </div>
        ))}
      </details>

      <p className="lab-footnote">
        {data.verification}. Source:{" "}
        <code>analysis/power-firing/</code>.
      </p>
    </main>
  );
}
