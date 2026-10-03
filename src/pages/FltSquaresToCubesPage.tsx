import { Link } from "react-router-dom";
import { REPO_URL } from "../lib/meta";

const EXPERIMENTS_FILE = `${REPO_URL}/blob/master/lean/Hire/FLT/Experiments.lean`;

export function FltSquaresToCubesPage() {
  return (
    <main className="page notes lab-note-page">
      <h1>From squares to cubes</h1>
      <p className="lede">
        This is the old scratchpad question, now kept beside the checked FLT
        proofs: what happens when a Pythagorean pattern is pushed into cubes,
        fourth powers, and fifth powers?
      </p>

      <section>
        <h2>The visible mismatch</h2>
        <p>
          Start with the familiar triple <code>3² + 4² = 5²</code>. Raising the
          same bases to higher powers immediately overshoots or undershoots the
          target. For cubes:
        </p>
        <aside className="lab-theorem" aria-label="Cube mismatch">
          <p className="lab-theorem-implies">
            3³ + 4³ = 91,  5³ = 125.
          </p>
        </aside>
        <p>
          The spillover identities in Lean package that kind of mismatch more
          generally. A hypothetical cube solution would force{" "}
          <code>a² + b² &gt; c²</code>. That is useful information, but it is not
          a proof of impossibility: it rules out the naive lift from a square
          triple, not every possible cube triple.
        </p>
        <p>
          One normalized scratch calculation shows up as{" "}
          <code>18 + 48 ≠ 100</code>: a useful warning sign, not a contradiction
          by itself.
        </p>
      </section>

      <section>
        <h2>What it explains</h2>
        <p>
          The lab is good at explaining why Pythagorean triples do not simply
          keep working at larger exponents. It shows a necessary geometric
          shortfall or overshoot, and gives a bridge from the original visual
          intuition to the checked descents.
        </p>
        <p>
          The checked FLT proofs take a stronger route. Instead of showing that
          one inherited triple fails, they show that any hypothetical solution
          would produce a smaller solution of the same kind.
        </p>
      </section>

      <section>
        <h2>Where it lives</h2>
        <p>
          The experimental identities are intentionally outside the main proof
          barrel. They live in{" "}
          <a href={EXPERIMENTS_FILE}>
            <code>lean/Hire/FLT/Experiments.lean</code>
          </a>
          . The formal checkpoint is back on <Link to="/flt">FLT</Link>.
        </p>
      </section>
    </main>
  );
}
