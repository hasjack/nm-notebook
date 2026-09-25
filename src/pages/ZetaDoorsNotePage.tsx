import { Link } from "react-router-dom";

/** Computational note — PDF in public/paper/zeta-doors.pdf. */
export function ZetaDoorsNotePage() {
  return (
    <main className="page paper-page">
      <h1>Prime neighbours of zeta denominators</h1>
      <p className="lede paper-abstract">
        For even k with 3 ∤ k, D = 3·2<sup>1+v<sub>2</sub>(k)</sup> T. Extra
        primes are 2 (mod 3);
        11 (mod 12) when 4 ∤ k, else 5 or 11 (mod 12). Plus-side candidates have
        a factored Q−1. Lean records the selection rule, not von Staudt–Clausen.
        Lab snapshot, not an infinite family. 25 September 2026: lions71
        18365, 16213, and 16165-digit candidates certified and independently
        verified. Live hunt:{" "}
        <Link to="/zeta-doors">Zeta doors</Link>.
      </p>

      <div className="paper-viewer">
        <iframe
          className="paper-frame"
          title="zeta-doors.pdf"
          src="/paper/zeta-doors.pdf?v=1758800000#view=FitH"
        />
      </div>

      <h2>Checked Lean</h2>
      <ul className="paper-lean">
        <li>
          <code>Hire/ZetaDoors.lean</code>
          <ul>
            <li>
              <code>prime_mod_three_of_pred_dvd_even</code>
            </li>
            <li>
              <code>m0_dvd_of_pred_dvd_even</code>
            </li>
            <li>
              <code>prime_mod_twelve_of_pred_dvd_not_four</code>
            </li>
            <li>
              <code>prime_mod_twelve_of_pred_dvd_four</code>
            </li>
            <li>
              <code>prime_mod_twelve_of_pred_dvd_index</code>
            </li>
          </ul>
        </li>
      </ul>
    </main>
  );
}
