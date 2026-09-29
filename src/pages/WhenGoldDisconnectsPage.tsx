import { Link } from "react-router-dom";

/** Sequel note — PDF in public/paper/when-gold-disconnects.pdf. */
export function WhenGoldDisconnectsPage() {
  return (
    <main className="page paper-page">
      <h1>When gold disconnects</h1>
      <p className="lede paper-abstract">
        If an odd prime <em>q</em> divides the door of a prime <em>p</em>, then{" "}
        <em>p</em> ≥ 2<em>q</em> − 1, so every gold arc runs from a larger prime
        to a smaller one. Every gold component of a finite window contains a
        2-power door, so connectivity is whether those doors are joined. Gold
        is disconnected for arbitrarily large integer windows if and only if
        there are infinitely many Mersenne or Fermat primes, and each 2-power
        door <em>M</em> ≥ 7 forces the octave [<em>ω</em>(<em>M</em>), 2<em>ω</em>(<em>M</em>) − 2].
        For <em>M</em><sub>31</sub>, assuming connectivity at <em>X</em><sup>*</sup> = 92,274,421
        from the <Link to="/notes/hire-graph">hire-graph note</Link>, gold is
        disconnected for <em>X</em><sup>*</sup> ≤ <em>X</em> ≤ 2<em>M</em><sub>61</sub> − 2
        precisely when 98,784,247,763 ≤ <em>X</em> ≤ 627,065,224,920.
      </p>

      <div className="paper-viewer">
        <iframe
          className="paper-frame"
          title="when-gold-disconnects.pdf"
          src="/paper/when-gold-disconnects.pdf?v=1790679213#view=FitH"
        />
      </div>

      <h2>Lean</h2>
      <p className="lede" style={{ maxWidth: "42rem" }}>
        <code>Hire/GoldDisconnects.lean</code> checks the size bound{" "}
        <code>2q ≤ p + 1</code>, door closure, descent to a 2-power door, and
        the sink reduction: the sinks are the prime 2-power doors hired in the
        window, and gold is connected exactly when those sinks lie in one
        component. Monotonicity of windows is checked, and{" "}
        <code>gold_bridge_of_finset</code> gives one threshold for a finite set:
        above that threshold every listed prime is joined to 5. Then{" "}
        <code>goldConnected_of_finite_twoPowerDoors</code> joins the sinks
        through 5, allowing several sinks already to lie in one component. It
        also checks the earlier single-window isolation lemmas and both
        directions for prime 2-power doors: gold is disconnected for arbitrarily
        large windows if and only if there are infinitely many prime 2-power
        doors. The proof has no <code>sorry</code>, <code>admit</code>, or{" "}
        <code>axiom</code>. The octave, the stretch, the <em>M</em><sub>31</sub>{" "}
        theorem, and the identification of those doors with Mersenne and Fermat
        primes are not formalised. The tables and <em>X</em><sub>1</sub> are
        the script in the note, not Lean theorems.
      </p>
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
              <code>goldArc_tgt_le_div_two</code>
            </li>
            <li>
              <code>hired_of_dvd_m0</code>
            </li>
            <li>
              <code>gold_descent</code>
            </li>
            <li>
              <code>sinks_eq_twoPowerDoors</code>
            </li>
            <li>
              <code>gold_path_to_sink</code>
            </li>
            <li>
              <code>goldConnected_iff_sinks_reachable</code>
            </li>
            <li>
              <code>componentsEquivSinkClasses</code>
            </li>
            <li>
              <code>owners_mono</code>
            </li>
            <li>
              <code>goldReachable_mono</code>
            </li>
            <li>
              <code>gold_bridge</code>
            </li>
            <li>
              <code>gold_bridge_of_finset</code>
            </li>
            <li>
              <code>goldConnected_of_finite_twoPowerDoors</code>
            </li>
            <li>
              <code>goldDisconnected_arbitrarily_large_iff</code>
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

      <h2>The <em>M</em><sub>31</sub> window</h2>
      <p className="lede" style={{ maxWidth: "42rem" }}>
        <em>r</em><sub>0</sub> = <em>ω</em>(<em>M</em><sub>31</sub>) = 98,784,247,763,
        with door 2·23·<em>M</em><sub>31</sub>. Its hire time is <em>ω</em>(<em>r</em><sub>0</sub>) = 1,382,979,468,683.
        The reconnection is <em>X</em><sub>1</sub> = 627,065,224,921, through <em>w</em> = 313,532,612,461
        (door 2·73·<em>M</em><sub>31</sub>) and the chain 73 → 37 → 19 → 5. The earlier bridge
        owner <em>v</em> = 300,647,710,579 has door 2<sup>2</sup>·5·7·<em>M</em><sub>31</sub> and
        no owner up to <em>ω</em>(<em>r</em><sub>0</sub>).
      </p>
    </main>
  );
}
