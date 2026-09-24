import { Link } from "react-router-dom";
import { doorWaitData as waits } from "../lib/doorWaitData";
import "./DoorCoveragePage.css";

const fmt = (n: number) => n.toLocaleString("en-GB");

/** Lab: opportunity waits inside the door lattice. */
export function DoorWaitsPage() {
  return (
    <main className="page notes lab-note-page door-coverage-page">
      <h1>Door waits</h1>
      <p className="lede">
        Opportunity waits and small-prime blockers inside the two-class lattice.
        Related: <Link to="/two-class">Two-class coverage</Link>,{" "}
        <Link to="/coverage-lattice">Coverage lattice</Link>,{" "}
        <Link to="/cube-doors">Cube doors</Link>,{" "}
        <Link to="/power-firing">Power firing</Link>,{" "}
        <Link to="/ingredient-transitions">Ingredient transitions</Link>.
      </p>

      <h2>Waiting inside the lattice</h2>
      <p>
        Exact sieve through {fmt(waits.limit)}. A miss is an eligible composite
        between consecutive prime hires. After the ≤{waits.smallFactorBound}{" "}
        sieve, a miss is a composite not eliminated by those small primes. First
        hires stay separate from subsequent waits.
      </p>
      <div className="door-table-wrap">
        <table className="door-table">
          <thead>
            <tr>
              <th>Q</th>
              <th>Prime hires</th>
              <th>Mean misses</th>
              <th>90th percentile</th>
              <th>Maximum misses</th>
              <th>After ≤100 sieve: mean misses</th>
            </tr>
          </thead>
          <tbody>
            {waits.overall.map((r) => (
              <tr key={r.q}>
                <td>{r.q}</td>
                <td>{fmt(r.primeHits)}</td>
                <td>{r.meanMisses}</td>
                <td>{r.p90Misses}</td>
                <td>{r.maxMisses}</td>
                <td>{r.meanMissesAfterSieve}</td>
              </tr>
            ))}
          </tbody>
        </table>
      </div>
      <p>
        First hires:{" "}
        {waits.overall.map((r, i) => (
          <span key={r.q}>
            {i ? "; " : ""}
            Q={r.q}: {r.firstHire}
          </span>
        ))}
        . Each of these four succeeds at its first eligible position.
      </p>
      <p>
        Lanes 7 and 49 have nearly equal mean opportunity waits. Higher powers
        thin both candidate positions and prime hits; number-line gaps grow.
        Primes ≤100 remove most composites; residual mean waits sit near 0.81.
      </p>
      <details>
        <summary>Band means and residue switches</summary>
        <div className="door-table-wrap">
          <table className="door-table">
            <thead>
              <tr>
                <th>Q</th>
                <th>Band</th>
                <th>Mean misses</th>
                <th>After sieve</th>
                <th>Next survivor prime</th>
                <th>Fitted baseline</th>
              </tr>
            </thead>
            <tbody>
              {waits.bands.map((r) => (
                <tr key={`${r.q}-${r.upperInclusive}`}>
                  <td>{r.q}</td>
                  <td>
                    ({fmt(r.lowerExclusive)}, {fmt(r.upperInclusive)}]
                  </td>
                  <td>{r.meanMisses}</td>
                  <td>{r.meanMissesAfterSieve}</td>
                  <td>{r.immediateNextSurvivorPrime}%</td>
                  <td>{r.fittedIndependentBaseline}%</td>
                </tr>
              ))}
            </tbody>
          </table>
        </div>
        <div className="door-table-wrap">
          <table className="door-table">
            <thead>
              <tr>
                <th>Q</th>
                <th>Band</th>
                <th>Observed switch share</th>
                <th>Raw independent model</th>
                <th>Sieve-aware independent model</th>
              </tr>
            </thead>
            <tbody>
              {waits.switchBandMillion.map((r) => (
                <tr key={`sw-${r.q}`}>
                  <td>{r.q}</td>
                  <td>
                    ({fmt(r.lowerExclusive)}, {fmt(r.upperInclusive)}]
                  </td>
                  <td>{r.observedSwitchShare}%</td>
                  <td>{r.rawIndependent}%</td>
                  <td>{r.sieveAware}%</td>
                </tr>
              ))}
            </tbody>
          </table>
        </div>
      </details>
      <details>
        <summary>Longest complete waits and blockers</summary>
        <div className="door-table-wrap">
          <table className="door-table">
            <thead>
              <tr>
                <th>Q</th>
                <th>Prime endpoints</th>
                <th>Missed opportunities</th>
                <th>Surviving after sieve</th>
                <th>Number-line gap</th>
              </tr>
            </thead>
            <tbody>
              {waits.overall.map((r) => (
                <tr key={`long-${r.q}`}>
                  <td>{r.q}</td>
                  <td>
                    {fmt(r.longest.start)} → {fmt(r.longest.end)}
                  </td>
                  <td>{r.longest.misses}</td>
                  <td>{r.longest.survivingMisses}</td>
                  <td>{fmt(r.longest.numericGap)}</td>
                </tr>
              ))}
            </tbody>
          </table>
        </div>
        <div className="door-table-wrap">
          <table className="door-table">
            <thead>
              <tr>
                <th>Q</th>
                <th>Composites</th>
                <th>Blocked by primes ≤100</th>
                <th>Share removed</th>
                <th>Most frequent smallest blockers</th>
              </tr>
            </thead>
            <tbody>
              {waits.overall.map((r) => (
                <tr key={`blk-${r.q}`}>
                  <td>{r.q}</td>
                  <td>{fmt(r.composites)}</td>
                  <td>{fmt(r.blockedByLeq100)}</td>
                  <td>{r.shareRemoved}%</td>
                  <td>
                    {r.topBlockers
                      .map(([p, n]) => `${p}: ${fmt(n)}`)
                      .join("; ")}
                  </td>
                </tr>
              ))}
            </tbody>
          </table>
        </div>
      </details>
      <p>
        Reproduce:{" "}
        <code>python3 analysis/door-coverage/waits.py --limit 10000000</code>.
        Full histograms in{" "}
        <code>analysis/door-coverage/waits-results.json</code>.
      </p>
    </main>
  );
}
