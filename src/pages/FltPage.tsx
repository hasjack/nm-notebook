import { Link } from "react-router-dom";
import { REPO_URL } from "../lib/meta";

const FLT_BASE = `${REPO_URL}/tree/master/lean/Hire/FLT`;
const FLT_FILE = `${REPO_URL}/blob/master/lean/Hire/FLT.lean`;
const SEVEN_FILE = `${REPO_URL}/blob/master/lean/Hire/FLT/Seven.lean`;

export function FltPage() {
  return (
    <main className="page notes lab-note-page">
      <h1>Fermat descents in Lean</h1>
      <p className="lede">
        These files formalise classical proofs that no positive integers satisfy{" "}
        <code>a^n + b^n = c^n</code> for <code>n = 3, 4, 5</code>. Each proof
        uses infinite descent: a hypothetical solution would produce a smaller
        solution of the same kind, which cannot continue forever.
      </p>

      <section>
        <h2>What is checked</h2>
        <p>
          The public barrel is <code>Hire.FLT</code>. It imports the three final
          proof modules and checks these theorem statements:
        </p>
        <ul>
          <li>
            <a href={`${FLT_BASE}/Three.lean`}>
              Exponent 3
            </a>
            : Eisenstein-integer descent on the output&apos;s <code>natAbs</code>.
          </li>
          <li>
            <a href={`${FLT_BASE}/Four.lean`}>
              Exponent 4
            </a>
            : Pythagorean descent on the square solution&apos;s hypotenuse.
          </li>
          <li>
            <a href={`${FLT_BASE}/Five.lean`}>
              Exponent 5
            </a>
            : golden-ring descent through two auxiliary norm equations.
          </li>
        </ul>
        <p>
          The theorem names and axiom report are in{" "}
          <a href={FLT_FILE}>
            <code>lean/Hire/FLT.lean</code>
          </a>
          . The reported axioms are the expected Mathlib foundations:
          <code> propext</code>, <code> Classical.choice</code>, and{" "}
          <code> Quot.sound</code>. This report is a dependency check; the
          mathematical statements and proof structure still deserve human
          review.
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
          barrel. A hypothetical cube solution, for example, would satisfy{" "}
          <code>a^2 + b^2 &gt; c^2</code>. That identifies a necessary mismatch,
          but it does not itself establish impossibility or produce a smaller
          solution.
        </p>
        <p>
          Those identities live in{" "}
          <a href={`${FLT_BASE}/Experiments.lean`}>
            <code>lean/Hire/FLT/Experiments.lean</code>
          </a>
          .
        </p>
        <p>
          There is also exploratory exponent-seven arithmetic in{" "}
          <a href={SEVEN_FILE}>
            <code>lean/Hire/FLT/Seven.lean</code>
          </a>
          . It establishes the seventh-power factorisation, common-divisor
          control, the forced extraction{" "}
          <code>a+b = 7^6 u^7</code>, <code>F_7(a,b) = 7 v^7</code>, and{" "}
          <code>c = 7uv</code>, plus related prime-divisor restrictions and a
          three-factor cancellation identity. It does not construct a smaller
          solution or prove FLT for exponent 7.
        </p>
      </section>

      <section>
        <h2>Lab pages</h2>
        <p>
          The shelf also keeps a few working notes near the proof checkpoint:
          <Link to="/flt/from-squares-to-cubes"> squares to cubes</Link>,{" "}
          <Link to="/flt/descent-lab">what makes descent work</Link>, and{" "}
          <Link to="/flt/hire-ascent">climbing the hire graph</Link>. There is
          also an exploratory note on{" "}
          <Link to="/flt/cyclotomic-ratios">cyclotomic ratios</Link>. The first
          two are guides to the existing proof material; the latter pages are
          lab benches rather than completed-proof narrative.
        </p>
      </section>

      <section>
        <h2>Road to all n</h2>
        <p>
          The reduction by divisibility means exponent 4 plus all odd prime
          exponents would imply the full statement. These files cover only the
          readable descents for 3, 4, and 5. Regular primes belong to Kummer-type
          formalizations; the established general proof uses the Frey/Ribet/Wiles
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
