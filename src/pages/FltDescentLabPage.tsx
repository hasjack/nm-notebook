import { Link } from "react-router-dom";
import { REPO_URL } from "../lib/meta";

const README_FILE = `${REPO_URL}/blob/master/lean/Hire/FLT/README.md`;
const FIVE_AUDIT_FILE = `${REPO_URL}/blob/master/lean/Hire/FLT/FiveAudit.md`;

export function FltDescentLabPage() {
  return (
    <main className="page notes lab-note-page">
      <h1>What makes descent work?</h1>
      <p className="lede">
        Infinite descent is not just “make something smaller”. The smaller
        object has to satisfy the same assumptions, so the construction can run
        again. This page is the reviewer&apos;s checklist.
      </p>

      <section>
        <h2>The pattern</h2>
        <ol className="lab-note-hierarchy-list">
          <li>
            <strong>Entry</strong>: assume a least counterexample of the right
            kind.
          </li>
          <li>
            <strong>Construction</strong>: factor or normalize it into a new
            object.
          </li>
          <li>
            <strong>Preservation</strong>: prove the new object has all the
            hypotheses needed to repeat the argument.
          </li>
          <li>
            <strong>Decrease</strong>: prove the chosen natural-number measure
            is strictly smaller.
          </li>
          <li>
            <strong>Closure</strong>: strong induction rejects the original
            least counterexample.
          </li>
        </ol>
      </section>

      <section>
        <h2>The measures</h2>
        <p>
          The current checkpoint uses four named decreases. Exponent 3 descends
          on the output&apos;s <code>natAbs</code>. Exponent 4 descends on the
          hypotenuse <code>natAbs</code> of the square solution. Exponent 5 has
          two auxiliary norm descents, one measured by <code>B.natAbs</code> and
          the other by <code>Q.natAbs</code>.
        </p>
        <p>
          That is the heart of the audit: every branch must land in the same
          structure with the measure smaller than before.
        </p>
      </section>

      <section>
        <h2>The n = 5 checklist</h2>
        <p>
          The exponent-5 proof is the dense one. Its audit names the branch,
          the defining equations, positivity, coprimality/five-freeness, the
          smaller measure, and the strong-induction closure.
        </p>
        <p>
          Read the proof map in{" "}
          <a href={README_FILE}>
            <code>lean/Hire/FLT/README.md</code>
          </a>{" "}
          and the detailed audit in{" "}
          <a href={FIVE_AUDIT_FILE}>
            <code>lean/Hire/FLT/FiveAudit.md</code>
          </a>
          . The shelf entrance is <Link to="/flt">FLT</Link>.
        </p>
      </section>
    </main>
  );
}
