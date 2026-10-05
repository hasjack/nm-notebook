import { Fragment } from "react";
import { REPO_URL } from "../lib/meta";

const SCRIPT_FILE = `${REPO_URL}/blob/master/analysis/hire_residue_torus/hire_torus_mod5.py`;
const RESULT_FILE = `${REPO_URL}/blob/master/analysis/hire_residue_torus/results_mod5_1000000.json`;
const LEAN_FILE = `${REPO_URL}/blob/master/lean/Hire/ResidueTorus.lean`;

const PLUS_GRID = [
  [0, 4040, 5181, 4141, 3427],
  [0, 0, 5037, 3971, 3275],
  [0, 5154, 6378, 0, 4577],
  [0, 4125, 0, 4176, 3447],
  [0, 4656, 5841, 4772, 0],
];

const MINUS_GRID = [
  [0, 4083, 5223, 4147, 3378],
  [0, 3884, 5082, 3985, 0],
  [0, 5206, 0, 5341, 4589],
  [0, 4036, 5277, 0, 3461],
  [0, 0, 5845, 4731, 4040],
];

const WINDOW_ROWS = [
  { x: "10^4", plus: 852, minus: 861, plusCells: 16, minusCells: 16 },
  { x: "10^5", plus: 7822, minus: 7860, plusCells: 16, minusCells: 16 },
  { x: "10^6", plus: 72198, minus: 72308, plusCells: 16, minusCells: 16 },
];

function ResidueGrid({ title, grid, forbidden }: { title: string; grid: number[][]; forbidden: number }) {
  return (
    <article className="residue-grid-card">
      <h2>{title}</h2>
      <p>
        Rows are <code>a mod 5</code>; columns are <code>q mod 5</code>. Dark
        cells are the proved forbidden product residue.
      </p>
      <div className="residue-grid" role="table" aria-label={title}>
        <div className="residue-corner" />
        {[0, 1, 2, 3, 4].map((q) => (
          <div key={`q-${q}`} className="residue-head">
            q={q}
          </div>
        ))}
        {grid.map((row, a) => (
          <Fragment key={`row-${a}`}>
            <div className="residue-head residue-row-head">
              a={a}
            </div>
            {row.map((value, q) => {
              const isForbidden = (a * q) % 5 === forbidden;
              return (
                <div
                  key={`${a}-${q}`}
                  className={isForbidden ? "residue-cell forbidden" : "residue-cell"}
                  title={`a=${a}, q=${q}`}
                >
                  {value || "—"}
                </div>
              );
            })}
          </Fragment>
        ))}
      </div>
    </article>
  );
}

export function HireResidueTorusPage() {
  return (
    <main className="page notes lab-note-page hire-residue-page">
      <h1>Hire residue torus mod 5</h1>
      <p className="lede">
        Each gold arc <code>p → q</code> is placed by{" "}
        <code>(q mod 5, a mod 5)</code>, where <code>a = m₀(p) / q</code>. The
        torus view is just the two residues wrapped in both directions; the grids
        below show exact counts from the reusable experiment.
      </p>

      <section>
        <h2>What Lean proves</h2>
        <p>
          <a href={LEAN_FILE}>
            <code>lean/Hire/ResidueTorus.lean</code>
          </a>{" "}
          proves the two forbidden product cells. For prime owners{" "}
          <code>p ≠ 5</code>, the plus door <code>a*q = p + 1</code> forbids{" "}
          <code>a*q ≡ 1 mod 5</code>, and the minus door{" "}
          <code>a*q + 1 = p</code> forbids <code>a*q ≡ 4 mod 5</code>.
        </p>
        <p>
          The integration lemmas use the repo definition <code>m₀ p</code>: from{" "}
          <code>a*q = m₀ p</code>, together with the branch{" "}
          <code>p % 3 = 1</code> or <code>p % 3 = 2</code>, they derive the
          matching residue exclusion.
        </p>
      </section>

      <section>
        <h2>Experiment through p ≤ 1,000,000</h2>
        <p>
          Scope: excluded owners <code>p ≤ 5</code>, hub <code>q = 2</code>, and
          exceptional <code>q = 5</code>. Distinct prime divisors are counted
          once. The run included 144,506 arcs: 72,198 plus-door and 72,308
          minus-door. There were zero forbidden-cell violations.
        </p>
        <div className="residue-grid-pair">
          <ResidueGrid title="Plus door: m₀(p) = p + 1" grid={PLUS_GRID} forbidden={1} />
          <ResidueGrid title="Minus door: m₀(p) = p - 1" grid={MINUS_GRID} forbidden={4} />
        </div>
      </section>

      <section>
        <h2>Occupation snapshots</h2>
        <div className="door-table-wrap">
          <table className="door-table">
            <thead>
              <tr>
                <th>window</th>
                <th>plus arcs</th>
                <th>minus arcs</th>
                <th>plus occupied cells</th>
                <th>minus occupied cells</th>
              </tr>
            </thead>
            <tbody>
              {WINDOW_ROWS.map((row) => (
                <tr key={row.x}>
                  <td>{row.x}</td>
                  <td>{row.plus.toLocaleString()}</td>
                  <td>{row.minus.toLocaleString()}</td>
                  <td>{row.plusCells}/16 permitted</td>
                  <td>{row.minusCells}/16 permitted</td>
                </tr>
              ))}
            </tbody>
          </table>
        </div>
        <p>
          The exclusions are proved. Full occupation of the permitted cells is an
          observation in the tested windows. The unequal cell counts have not
          been tested against a prime-pair baseline.
        </p>
        <p>
          Reproducible source:{" "}
          <a href={SCRIPT_FILE}>
            <code>analysis/hire_residue_torus/hire_torus_mod5.py</code>
          </a>
          . Recorded JSON:{" "}
          <a href={RESULT_FILE}>
            <code>results_mod5_1000000.json</code>
          </a>
          .
        </p>
      </section>
    </main>
  );
}
