import { Link } from "react-router-dom";

export function HeckeLFunctionNotePage() {
  return (
    <main className="page paper-page">
      <h1>From the 3-free door to a Hecke L-function</h1>
      <p className="lede paper-abstract">
        This note follows the door character from the Hire graph into the
        Eisenstein integers. The character is lifted by absolute norm to an
        ideal character, descends through the ray relation modulo{" "}
        <span className="math">15𝒪<sub>K</sub></span>, and its ideal series is
        identified with the paired Dirichlet L-functions already checked in
        Lean.
      </p>
      <p className="paper-abstract">
        The endpoint is a concrete factorisation and continuation result:
        the Eisenstein ideal character series agrees with{" "}
        <span className="math">L(s,C)L(s,companion15)</span>, with the companion
        differing from the quartic character by the explicit Euler correction at
        3. The note keeps the boundary honest: the construction uses known
        zero-free regions for the finite-order factors and does not claim an
        improvement of those exponents.
      </p>

      <div className="paper-viewer">
        <iframe
          className="paper-frame"
          title="from-the-3-free-door-to-a-hecke-l-function.pdf"
          src="/paper/from-the-3-free-door-to-a-hecke-l-function.pdf?v=1791543720#view=FitH"
        />
      </div>

      <h2>Checked Lean</h2>
      <ul className="paper-lean">
        <li>
          <code>Hire/EisensteinNormLift15.lean</code> and{" "}
          <code>Hire/FractionalNormLift15.lean</code>: norm-lift character,
          principal-ray invariance, fourth-order values, and descent through
          the ray relation.
        </li>
        <li>
          <code>Hire/HeckeSeries15.lean</code>: absolute convergence of the
          Eisenstein ideal character series for{" "}
          <span className="math">Re(s) &gt; 1</span>.
        </li>
        <li>
          <code>Hire/HeckeFactorization15.lean</code> and{" "}
          <code>Hire/IdealCountMultiplicative15.lean</code>: norm-fibre counts
          and the divisor-sum coefficient identity.
        </li>
        <li>
          <code>Hire/HeckeDirichletProduct15.lean</code>: factorisation into the
          paired Dirichlet L-functions.
        </li>
        <li>
          <code>Hire/HeckeContinuation15.lean</code>: entire continuation,
          uniqueness, zero correspondence, and the zero-free boundary.
        </li>
      </ul>

      <p className="paper-abstract">
        For the broader Hire context, see{" "}
        <Link to="/notes/hire-graph">the hire graph note</Link> and the{" "}
        <Link to="/hire/residue-torus">residue torus lab</Link>.
      </p>
    </main>
  );
}
