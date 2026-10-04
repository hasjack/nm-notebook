import { Link } from "react-router-dom";
import { REPO_URL } from "../lib/meta";

const CLASS_FILE = `${REPO_URL}/blob/master/lean/Hire/FLT/ClassObstruction.lean`;
const SEARCH_FILE = `${REPO_URL}/blob/master/analysis/flt_class_obstruction/cyclotomic_ratio_search.py`;

export function FltCyclotomicRatiosPage() {
  return (
    <main className="page notes lab-note-page">
      <h1>Cyclotomic ratios: locating the principality gap</h1>
      <p className="lede">
        This lab note records an exploratory check around the shared cyclotomic
        form <code>L_j = a + ζ^j b</code>. The Lean file is separate from the
        completed FLT proof modules: it formalises a class-group obstruction and
        a conditional element-power calculation, but it gives no new descent.
      </p>

      <section>
        <h2>One parameter</h2>
        <p>
          After normalising by <code>a + b</code>, the whole family is governed
          by one rational parameter:
        </p>
        <p className="lab-inline-formula">
          T = b/(a+b), <span> </span> R_j = 1 + T(ζ^j − 1).
        </p>
        <p>
          The recurrence relations between the <code>R_j</code> are algebraic
          identities in this one parameter. They organise the family, but they
          are not extra Fermat restrictions by themselves.
        </p>
      </section>

      <section>
        <h2>The gap</h2>
        <p>
          The descent wants element powers. The ideal factorisation gives only
          ideal powers:
        </p>
        <p className="lab-inline-formula">(L_j) = (λ)^m_j A_j^p.</p>
        <p>
          That does not supply <code>L_j = u λ^m α^p</code> unless the ideal
          root <code>A_j</code> is principal. This is the principality gap.
        </p>
        <p>
          Conjugating makes the obstruction visible. In the minus component,
          the quotient class is doubled:
        </p>
        <p className="lab-inline-formula">[A / Ā] = 2[A].</p>
        <p>
          For 37-torsion, the checked abstract calculation says this vanishes
          exactly when the original class vanishes.
        </p>
      </section>

      <section>
        <h2>Checked Lean</h2>
        <p>
          The exploratory module{" "}
          <a href={CLASS_FILE}>
            <code>lean/Hire/FLT/ClassObstruction.lean</code>
          </a>{" "}
          compiles on its own. It is not imported by <code>Hire.FLT</code>.
        </p>
        <ul>
          <li>
            <code>sub_conjugate_eq_two_smul</code>: in the minus part,
            subtracting the conjugate doubles the class.
          </li>
          <li>
            <code>eq_zero_of_thirty_seven_smul_eq_zero_of_two_smul_eq_zero</code>
            : a class killed by both 37 and 2 is zero.
          </li>
          <li>
            <code>sub_conjugate_eq_zero_iff</code>: for 37-torsion in the minus
            part, <code>c - conj c = 0</code> iff <code>c = 0</code>.
          </li>
          <li>
            <code>conjugate_ratio_of_element_power</code> and{" "}
            <code>conjugate_ratio_eq_root_mul_power</code>: if an
            element-power representation is available, the conjugate ratio has
            the expected root-of-unity times p-th-power shape.
          </li>
        </ul>
        <p>
          The root-of-unity hypotheses are still hypotheses. They have not been
          instantiated for the cyclotomic FLT setting here.
        </p>
      </section>

      <section>
        <h2>Bounded screen</h2>
        <p>
          A small reproducible script reruns the finite-field checks for all 255
          ordered coprime positive pairs <code>a,b ≤ 20</code>. The fields were
          tested together: <code>29,43</code> for exponent 7 and{" "}
          <code>149,223</code> for exponent 37.
        </p>
        <div className="door-table-wrap">
          <table className="door-table">
            <thead>
              <tr>
                <th>Test</th>
                <th>p = 7</th>
                <th>p = 37</th>
              </tr>
            </thead>
            <tbody>
              <tr>
                <td>
                  Both <code>a+b</code> and <code>F_p(a,b)</code> are p-th
                  powers away from p
                </td>
                <td>0</td>
                <td>0</td>
              </tr>
              <tr>
                <td>Rejected by conditional linked conjugate-ratio test</td>
                <td>242</td>
                <td>244</td>
              </tr>
              <tr>
                <td>Undecided because a tested reduction vanished</td>
                <td>12</td>
                <td>10</td>
              </tr>
              <tr>
                <td>Passed linked test</td>
                <td>1</td>
                <td>1</td>
              </tr>
            </tbody>
          </table>
        </div>
        <p>
          The sole linked-test survivor is <code>(1,1)</code>, where{" "}
          <code>(1+ζ)/(1+ζ⁻¹) = ζ</code>. The script is{" "}
          <a href={SEARCH_FILE}>
            <code>analysis/flt_class_obstruction/cyclotomic_ratio_search.py</code>
          </a>
          .
        </p>
      </section>

      <section>
        <h2>What this says</h2>
        <p>
          At <code>p = 37</code>, the irregular Bernoulli index <code>32</code>
          corresponds to character exponent <code>1 - 32 ≡ 5 mod 36</code>.
          Hire edges capture some relevant prime congruences, but there is no
          established relation transporting ideal classes along graph edges.
        </p>
        <aside className="lab-note-caveats" aria-label="Caveats">
          <p>
            The valuation test does not assume principality. The linked unit
            test does assume an element-power representation. These searches do
            not prove FLT, eliminate irregular torsion, or bridge hire-graph
            connectivity to principality.
          </p>
        </aside>
      </section>

      <section>
        <h2>Where it sits</h2>
        <p>
          Treat this as a lab bench beside the checked proofs, not as part of
          the proof narrative. The completed checkpoint remains on{" "}
          <Link to="/flt">FLT</Link>; this page records why this route currently
          stops at principality.
        </p>
      </section>
    </main>
  );
}
