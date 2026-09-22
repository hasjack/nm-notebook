import { Link } from "react-router-dom";

/** Computational note — PDF in public/paper/zeta-doors.pdf. */
export function ZetaDoorsNotePage() {
  return (
    <main className="page paper-page">
      <h1>Prime neighbours of zeta denominators</h1>
      <p className="lede paper-abstract">
        For k ≡ 2 (mod 12), the reduced denominator of ζ(1−k) is 12T, and
        every prime factor of T is 11 (mod 12). The unique 3-free neighbour of
        D/3 is the zeta-door candidate; the plus branch has a factored Q−1 and
        admits a Pocklington certificate. Lean records the selection rule, not
        von Staudt–Clausen. Lab snapshot, not an infinite family. Working
        draft, 22 September 2026. Live hunt:{" "}
        <Link to="/zeta-doors">Zeta doors</Link>.
      </p>

      <div className="paper-viewer">
        <iframe
          className="paper-frame"
          title="zeta-doors.pdf"
          src="/paper/zeta-doors.pdf?v=1758568200#view=FitH"
        />
      </div>

      <h2>Checked Lean</h2>
      <ul className="paper-lean">
        <li>
          <code>Hire/ZetaDoors.lean</code>
          <ul>
            <li>
              <code>prime_mod_twelve_of_pred_dvd_index</code>
            </li>
            <li>
              <code>m0_dvd_of_pred_dvd_index</code>
            </li>
            <li>
              <code>m0_eq_pred_iff</code>
            </li>
          </ul>
        </li>
      </ul>
    </main>
  );
}
