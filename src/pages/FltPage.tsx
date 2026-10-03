import { REPO_URL } from "../lib/meta";

const FLT_BASE = `${REPO_URL}/tree/master/lean/Hire/FLT`;

export function FltPage() {
  return (
    <main className="page notes lab-note-page">
      <h1>Fermat descents in Lean</h1>
      <p className="lede">
        A readable Lean checkpoint for Fermat&apos;s Last Theorem at exponents
        3, 4, and 5. It is a small formal shelf where the descents, audits,
        and limits of the approach can be opened and followed.
      </p>

      <section>
        <h2>What is checked</h2>
        <p>
          The public barrel is <code>Hire.FLT</code>. It imports the three final
          proof modules and prints the axiom footprint for:
        </p>
        <ul>
          <li>
            <code>Hire.EisensteinBridge.fermatLastTheoremThree_via_descent</code>
          </li>
          <li>
            <code>Hire.fermatLastTheoremFour_via_descent</code>
          </li>
          <li>
            <code>Hire.GoldenBridge.fermatLastTheoremFive_via_descent</code>
          </li>
        </ul>
        <p>
          The build reports the expected Mathlib baseline:
          <code> propext</code>, <code> Classical.choice</code>, and{" "}
          <code> Quot.sound</code>.
        </p>
      </section>

      <section>
        <h2>Descent map</h2>
        <p>
          Exponent 3 uses the Eisenstein integers and descends on the output
          <code> natAbs</code>. Exponent 4 is the classical Pythagorean descent
          on the square solution&apos;s hypotenuse <code>natAbs</code>. Exponent 5
          uses the golden ring and two auxiliary descents, on{" "}
          <code>B.natAbs</code> and <code>Q.natAbs</code>.
        </p>
        <p>
          The proof map is in{" "}
          <a href={`${FLT_BASE}/README.md`}>
            <code>lean/Hire/FLT/README.md</code>
          </a>
          .
        </p>
      </section>

      <section>
        <h2>Exponent 5 audit</h2>
        <p>
          The n = 5 audit traces the two auxiliary norm solutions through entry,
          preservation, decrease, and closure. Its central question is whether
          the smaller solution satisfies every assumption needed to run the same
          construction again.
        </p>
        <p>
          The checklist is in{" "}
          <a href={`${FLT_BASE}/FiveAudit.md`}>
            <code>lean/Hire/FLT/FiveAudit.md</code>
          </a>
          .
        </p>
      </section>

      <section>
        <h2>Experiments</h2>
        <p>
          The mismatch identities are kept, but not imported by the proof
          barrel. They show real constraints on hypothetical higher-exponent
          solutions, such as forced overshoot at the previous exponent, but they
          do not produce a descent map.
        </p>
        <p>
          Those identities live in{" "}
          <a href={`${FLT_BASE}/Experiments.lean`}>
            <code>lean/Hire/FLT/Experiments.lean</code>
          </a>
          .
        </p>
      </section>

      <section>
        <h2>Road to all n</h2>
        <p>
          The reduction by divisibility means exponent 4 plus all odd prime
          exponents would imply the full statement. These files cover only the
          readable descents for 3, 4, and 5. Regular primes belong to Kummer-type
          formalizations; the full theorem belongs to the Frey/Ribet/Wiles
          modularity route.
        </p>
        <p>
          So this shelf is intentionally modest: a formal, reviewable layer
          underneath the larger FLT story.
        </p>
      </section>
    </main>
  );
}
