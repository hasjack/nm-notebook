import { Link } from "react-router-dom";
import "./DoorCoveragePage.css";

/** Lab: why two doors — Eisenstein split/inert names the sluice. */
export function TorusPage() {
  return (
    <main className="page notes lab-note-page door-coverage-page">
      <h1>Torus</h1>
      <p className="lede">
        Why two doors. Over ℚ(√−3) (Eisenstein integers) an odd prime{" "}
        <em>p</em> ≠ 3 either splits or stays inert. Related:{" "}
        <Link to="/hire">Introduction</Link>,{" "}
        <Link to="/signed-doors">±Doors</Link>.
      </p>

      <aside className="lab-theorem" aria-label="chi3 as Kronecker">
        <p className="lab-theorem-implies">
          χ₃(<em>p</em>) = (−3/<em>p</em>) ={" "}
          <span className="cases-inline">
            +1 if <em>p</em> splits; −1 if <em>p</em> is inert
          </span>
          .
        </p>
      </aside>

      <p>
        Williams’ <em>p</em>+1 test for discriminant <em>D</em> = −3 uses the
        group order of the nonsplit torus,
      </p>
      <aside className="lab-theorem" aria-label="Williams nonsplit order">
        <p className="lab-theorem-implies">
          <em>p</em> − (−3/<em>p</em>) = <em>p</em> − χ₃(<em>p</em>) ={" "}
          <em>m</em>
          <sub>1</sub>(<em>p</em>).
        </p>
      </aside>
      <p>
        That is the neighbour you sack. The door you keep is the complementary
        order
      </p>
      <aside className="lab-theorem" aria-label="hire door">
        <p className="lab-theorem-implies">
          <em>m</em>
          <sub>0</sub>(<em>p</em>) = <em>p</em> + χ₃(<em>p</em>).
        </p>
      </aside>

      <p>
        Split primes (<em>p</em> ≡ 1 mod 3) keep <em>p</em>+1. Inert primes (
        <em>p</em> ≡ 2 mod 3) keep <em>p</em>−1. Same sluice you have been
        writing by hand, now named as the two circle-groups attached to{" "}
        <em>p</em> in ℤ[ω].
      </p>
    </main>
  );
}
