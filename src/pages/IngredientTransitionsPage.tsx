import { Link } from "react-router-dom";
import { ingredientTransitionData as data } from "../lib/ingredientTransitionData";
import { doorContinuityData as cont } from "../lib/doorContinuityData";
import { fullPowerContinuityData as power } from "../lib/fullPowerContinuityData";
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


      <h2>How far vs what arrives</h2>
      <p>
        Retention has an exact floor: an odd factor <em>q</em> cannot stay unless
        the door gap is at least 2<em>q</em>. Arrival size is another story. In the
        1–10 million band, the share of transitions where the largest odd factor
        grows at least tenfold sits near 30% across every gap bin — tiny leaps
        bring huge newcomers about as often as larger ones. Partial correlation
        of log gap with log arriving size (controlling for door size) is only{" "}
        {cont.gapArrival.partialCorr}. “How far?” is a weak guide; “where that
        leap lands?” is sharper.
      </p>
      <div className="door-table-wrap">
        <table className="door-table">
          <thead>
            <tr>
              <th>Door gap</th>
              <th>Transitions</th>
              <th>Largest odd grows ≥10×</th>
            </tr>
          </thead>
          <tbody>
            {cont.gapArrival.bins.map((b) => (
              <tr key={b.gapBin}>
                <td>{b.gapBin}</td>
                <td>{fmt(b.pairs)}</td>
                <td>{b.tenfoldPct.toFixed(2)}%</td>
              </tr>
            ))}
          </tbody>
        </table>
      </div>

      <h2>One level deeper</h2>
      <p>
        Immediate factor lists miss short hire paths. Among{" "}
        {fmt(cont.deeper.disjoint)} consecutive pairs with disjoint odd support,{" "}
        {cont.deeper.deeperPct}% still reconnect one step deeper: a departing
        odd prime divides the door of an arriving odd prime (
        <em>
          p<sub>old</sub> → q
        </em>
        ,{" "}
        <em>
          p<sub>new</sub> → r → q
        </em>
        ). Non-5 continuity is {cont.deeper.deeperNon5Pct}%; when the old door
        lacks 5, the rate is still {cont.deeper.oldWithout5DeeperPct}%.
      </p>
      <p>
        Prototype: {cont.deeper.example.p} → {cont.deeper.example.next}. Surface
        swap {cont.deeper.example.oldDoor} → {cont.deeper.example.newDoor}, but
        gold still holds {cont.deeper.example.path}. {cont.deeper.example.note}
      </p>
      <p>
        Neighbours are not special once gap, location, and ingredient profile are
        held. Against nonconsecutive controls matched on those (covering ~80% of
        the disjoint pairs), continuity is {cont.matched.rows[0].observedPct}% vs{" "}
        {cont.matched.rows[0].controlPct}% — the earlier excess over crude
        re-pairs does not survive. Gaps 2 and 4 sit outside this test.
      </p>
      <div className="door-table-wrap">
        <table className="door-table">
          <thead>
            <tr>
              <th>Min controls / stratum</th>
              <th>Neighbours matched</th>
              <th>Coverage</th>
              <th>Actual continuity</th>
              <th>Matched control</th>
            </tr>
          </thead>
          <tbody>
            {cont.matched.rows.map((r) => (
              <tr key={r.minControls}>
                <td>{r.minControls}</td>
                <td>{fmt(r.matched)}</td>
                <td>{r.coveragePct.toFixed(2)}%</td>
                <td>{r.observedPct.toFixed(3)}%</td>
                <td>{r.controlPct.toFixed(3)}%</td>
              </tr>
            ))}
          </tbody>
        </table>
      </div>
      <h2>Full-power continuity</h2>
      <p>
        Deeper continuity counts whether a departing odd prime base reconnects.
        Ask the sharper question: among consecutive pairs with disjoint odd
        support and at least one departing odd factor of exponent ≥2 (
        {fmt(power.eligible)} eligible through {fmt(power.limit)}), how often
        does the full power — or the whole previous odd part — land in one
        arriving door?
      </p>
      <div className="door-table-wrap">
        <table className="door-table">
          <thead>
            <tr>
              <th>Measure</th>
              <th>Count</th>
              <th>Share of eligible</th>
            </tr>
          </thead>
          <tbody>
            {power.rates.map((r) => (
              <tr key={r.label}>
                <td>{r.label}</td>
                <td>{fmt(r.count)}</td>
                <td>{r.pct.toFixed(2)}%</td>
              </tr>
            ))}
          </tbody>
        </table>
      </div>

      <h3>Examples</h3>
      <div className="door-table-wrap">
        <table className="door-table">
          <thead>
            <tr>
              <th>Primes</th>
              <th>Doors</th>
              <th>Arriving path</th>
              <th>Note</th>
            </tr>
          </thead>
          <tbody>
            {power.examples.map((e) => (
              <tr key={e.p}>
                <td>
                  {fmt(e.p)} → {fmt(e.next)}
                </td>
                <td>
                  <code>
                    {fmt(e.oldDoor)} = {e.oldFactors}
                  </code>
                  <br />
                  <code>
                    {fmt(e.newDoor)} = {e.newFactors}
                  </code>
                </td>
                <td>
                  <code>{e.path}</code>
                </td>
                <td>{e.note}</td>
              </tr>
            ))}
          </tbody>
        </table>
      </div>

      <details>
        <summary>By departing exponent</summary>
        <p>
          Opportunity-level rows (transition × departing repeated prime); a
          transition can contribute to more than one row.
        </p>
        <div className="door-table-wrap">
          <table className="door-table">
            <thead>
              <tr>
                <th>Exponent</th>
                <th>Opportunities</th>
                <th>Prime reconnects</th>
                <th>Full power</th>
              </tr>
            </thead>
            <tbody>
              {power.byExponent.map((r) => (
                <tr key={r.exp}>
                  <td>{r.exp}</td>
                  <td>{fmt(r.opportunities)}</td>
                  <td>{fmt(r.linked)}</td>
                  <td>{fmt(r.full)}</td>
                </tr>
              ))}
            </tbody>
          </table>
        </div>
      </details>

      <h3>Matched comparison</h3>
      <p>
        Against nonconsecutive controls matched on gap, location, and a
        stricter ingredient profile (exact exponents of 5 and 7, repeated-factor
        count, max odd exponent, …), full-power rate is{" "}
        {power.matched.fullPowerObservedPct.toFixed(2)}% observed vs{" "}
        {power.matched.fullPowerControlPct.toFixed(2)}% controls at
        min_controls ≥ {power.matched.minControls} (~
        {power.matched.coveragePct.toFixed(0)}% coverage of eligible pairs). No
        neighbour advantage on the matched subset. {power.matched.note}
      </p>
      <p>
        Phenomenon is real and rare. Adjacency is not adding a law here. Stop.
      </p>

      <h2>Swallow shapes</h2>
      <p>
        Jack&apos;s tighter classification of the {fmt(power.swallowShapes.n)}{" "}
        whole-odd-part preservations through {fmt(power.limit)}. Every case in
        this cohort fits one normal form. Exactly one preserving{" "}
        <code>r</code> per transition; <code>B = 1</code> always (no extra odd
        multiplier). Findings only — exact classification of this census, not a
        theorem for all such transitions.
      </p>
      <aside className="lab-theorem" aria-label="Whole-odd-part normal form">
        <p className="lab-theorem-implies">
          d<sub>old</sub> = 2<sup>v+k</sup> A
          <br />
          d<sub>new</sub> = 2<sup>v</sup> (2<sup>k</sup> A + 1)
          <br />
          r = 2<sup>k</sup> A + 1 &nbsp;(prime, ≡ 2 mod 3)
          <br />
          m₀(r) = 2<sup>k</sup> A
          <br />
          gap = d<sub>new</sub> − d<sub>old</sub> = 2<sup>v</sup>
        </p>
        <p>
          with k, v ≥ 1. All {fmt(power.swallowShapes.normalForm.matching)} of{" "}
          {fmt(power.swallowShapes.n)} match.
        </p>
      </aside>

      <h3>Preserving door shares</h3>
      <div className="door-table-wrap">
        <table className="door-table">
          <thead>
            <tr>
              <th>m₀(r)</th>
              <th>Count</th>
              <th>Share</th>
            </tr>
          </thead>
          <tbody>
            {power.swallowShapes.doorShares.map((r) => (
              <tr key={r.label}>
                <td>
                  <code>{r.label}</code>
                </td>
                <td>{fmt(r.count)}</td>
                <td>{r.pct.toFixed(2)}%</td>
              </tr>
            ))}
          </tbody>
        </table>
      </div>

      <h3>Normal-form door gaps</h3>
      <p>
        Gap is always a pure power of two (exactly 2<sup>v</sup>):{" "}
        {power.swallowShapes.normalForm.doorGaps
          .map((g) => `${g.gap}: ${fmt(g.count)}`)
          .join("; ")}
        .
      </p>

      <h3>Prototypes</h3>
      <div className="door-table-wrap">
        <table className="door-table">
          <thead>
            <tr>
              <th>A</th>
              <th>k, v</th>
              <th>Doors</th>
              <th>Arriving</th>
            </tr>
          </thead>
          <tbody>
            {power.swallowShapes.normalForm.prototypes.map((e) => (
              <tr key={e.A}>
                <td>{fmt(e.A)}</td>
                <td>
                  k = {e.k}, v = {e.v}
                </td>
                <td>
                  <code>
                    {fmt(e.dOld)} → {fmt(e.dNew)}
                  </code>
                </td>
                <td>
                  <code>
                    r = {fmt(e.r)}, m₀ = {fmt(e.m0r)}
                  </code>
                  <br />
                  {e.note}
                </td>
              </tr>
            ))}
          </tbody>
        </table>
      </div>
      <p>
        {power.swallowShapes.normalForm.note} No adjacency law claimed. Stop.
      </p>

      <p className="lab-footnote">
        Exact sieve; gcd identity on every adjacent pair; deeper census tracks
        prime ingredients; full-power census tracks exact exponents on the
        eligible repeated-factor slice. Matched controls are real
        nonconsecutive pairs standardized to the neighbour distribution.
        Findings only. Sources:{" "}
        <code>analysis/ingredient-transitions/</code>,{" "}
        <code>analysis/gap-ingredients/</code>,{" "}
        <code>analysis/deeper-door-continuity/</code>,{" "}
        <code>analysis/matched-door-continuity/</code>,{" "}
        <code>analysis/full-power-door-continuity/</code>{" "}
        (plus <code>analysis/whole-odd-block-shapes/</code>).
      </p>
    </main>
  );
}
