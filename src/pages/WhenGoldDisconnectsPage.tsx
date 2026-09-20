import { Link } from "react-router-dom";

/** Sequel note — PDF in public/paper/when-gold-disconnects.pdf. */
export function WhenGoldDisconnectsPage() {
  return (
    <main className="page paper-page">
      <h1>When gold disconnects</h1>
      <p className="lede paper-abstract">
        First-owner windows of 2-power doors are gold-disconnected, and
        downward gold chains terminate only at those doors. So gold is
        disconnected for infinitely many finite windows if and only if there
        are infinitely many Mersenne or Fermat primes. Paper 1 stays the hire
        graph and the Dirichlet bridge into{" "}
        <Link to="/notes/hire-graph">comp(5)</Link>; this note is the equivalence for the
        leftover question, plus the thin M₃₁ bridge-owner appointment.
      </p>

      <div className="paper-viewer">
        <iframe
          className="paper-frame"
          title="when-gold-disconnects.pdf"
          src="/paper/when-gold-disconnects.pdf?v=1789856592#view=FitH"
        />
      </div>

      <h2>Checked Lean</h2>
      <ul className="paper-lean">
        <li>
          <code>Hire/GoldDisconnects.lean</code>
          <ul>
            <li>
              <code>goldIsolated_of_firstOwner_twoPowerDoor</code>
            </li>
            <li>
              <code>goldDisconnected_of_firstOwner_twoPowerDoor</code>
            </li>
            <li>
              <code>goldDisconnected_firstOwner_of_twoPowerDoor_ge_twelve</code>
            </li>
            <li>
              <code>exists_twoPowerDoor_of_finite_closed</code>
            </li>
            <li>
              <code>GoldArc_tgt_lt</code>
            </li>
            <li>
              <code>infinite_goldDisconnected_of_infinite_twoPowerDoors</code>
            </li>
            <li>
              <code>
                infinite_goldDisconnected_of_infinite_mersenne_or_fermat_doors
              </code>
            </li>
          </ul>
        </li>
      </ul>

      <h2>Thin numbers (Lab)</h2>
      <p className="lede" style={{ maxWidth: "42rem" }}>
        M₃₁ first owner r₀ = 98,784,247,763; first direct 5–M₃₁ bridge{" "}
        <em>owner</em> v = 300,647,710,579 (m₀ = 2²·5·7·M₃₁, ratio ≈ 3.04).
        First owner of v is τ(v) = 24,051,816,846,319. Earlier mixed
        connector p* = 313,532,612,461 seats at τ(p*) = 627,065,224,921 ≈
        6.27·10¹¹ — current corridor upper marker (τ(v)/τ(p*) ≈ 38). Thin
        only — fat not run. See <Link to="/islands">Islands</Link>.
      </p>
    </main>
  );
}
