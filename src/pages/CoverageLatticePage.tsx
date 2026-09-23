import { Link } from "react-router-dom";
import { doorCoverageData as data } from "../lib/doorCoverageData";
import "./DoorCoveragePage.css";

const fmt = (n: number) => n.toLocaleString("en-GB");
const pct = (n: number, total: number) => `${((100 * n) / total).toFixed(2)}%`;

/** Lab: nest and lcm of coverage sets. */
export function CoverageLatticePage() {
  const nest = [
    { power: 343, parent: 49, count: data.coverage.find((c) => c.power === 343)?.count ?? 0 },
    { power: 49, parent: 7, count: data.coverage.find((c) => c.power === 49)?.count ?? 0 },
    { power: 7, parent: null, count: data.coverage.find((c) => c.power === 7)?.count ?? 0 },
  ];

  return (
    <main className="page notes lab-note-page door-coverage-page">
      <h1>Coverage nest and lcm</h1>
      <p className="lede">
        How coverage sets for fixed odd ingredients nest under powers and meet
        under least common multiples. Related:{" "}
        <Link to="/two-class">Two-class coverage</Link>.
      </p>

      <h2>Nesting of powers</h2>
      <p>
        Write C_Q for the set of primes p &gt; 3 with Q ∣ m₀(p). For odd q ∤ 3
        and a ≥ 1,
      </p>
      <aside className="lab-theorem" aria-label="Power nest">
        <p className="lab-theorem-implies">
          C<sub>q<sup>a+1</sup></sub> ⊆ C<sub>q<sup>a</sup></sub> ⊆ C<sub>q</sub>.
        </p>
      </aside>
      <p>
        In particular C_343 ⊆ C_49 ⊆ C_7. Counts in the window 3 &lt; p ≤{" "}
        {fmt(data.window)}:
      </p>
      <div className="door-table-wrap">
        <table className="door-table">
          <thead>
            <tr>
              <th>Power</th>
              <th>Covered primes</th>
            </tr>
          </thead>
          <tbody>
            {nest.map((r) => (
              <tr key={r.power}>
                <td>{r.power}</td>
                <td>
                  {r.count} / {fmt(data.totalSmall)}
                </td>
              </tr>
            ))}
          </tbody>
        </table>
      </div>

      <h2>Overlaps are lcms</h2>
      <aside className="lab-theorem" aria-label="Lcm overlap">
        <p className="lab-theorem-implies">
          C_A ∩ C_B = C_lcm(A,B).
        </p>
      </aside>
      <p>
        Pairwise overlaps in the same windows (and the limiting density
        1/φ(lcm(A,B))):
      </p>
      <div className="door-table-wrap">
        <table className="door-table">
          <thead>
            <tr>
              <th>Pair</th>
              <th>Through {fmt(data.window)}</th>
              <th>Share</th>
              <th>Through {fmt(data.searchLimit)}</th>
              <th>Limiting 1/φ</th>
            </tr>
          </thead>
          <tbody>
            {data.overlaps.map((r) => (
              <tr key={`${r.a}-${r.b}`}>
                <td>
                  {r.a} and {r.b}
                </td>
                <td>{r.countSmall}</td>
                <td>{pct(r.countSmall, data.totalSmall)}</td>
                <td>{pct(r.countLarge, data.totalLarge)}</td>
                <td>{pct(1, r.limitingDenominator)}</td>
              </tr>
            ))}
          </tbody>
        </table>
      </div>
      <p>
        Formalised in <code>lean/Hire/CoverageLattice.lean</code>.
      </p>
    </main>
  );
}
