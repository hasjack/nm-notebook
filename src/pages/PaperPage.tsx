export function PaperPage() {
  return (
    <main className="page paper-page">
      <h1>Paper</h1>
      <p className="lede paper-abstract">
        Of the two even neighbours of an odd prime <em>p</em>≠3, exactly one is
        divisible by 3. The other, the 3-free door <em>m</em>₀(<em>p</em>)=
        <em>p</em>+χ₃(<em>p</em>), is a canonical even integer attached to{" "}
        <em>p</em> whose odd prime factors never include 3. Ownership{" "}
        <em>q</em>|<em>m</em>₀(<em>p</em>) places a directed graph on the primes
        other than 3; adjoining a hub at 2, which divides every door, produces
        the hire graph. On a finite window the graph is the cone on its gold
        subgraph, so the Laplacian spectrum is the standard cone formula and
        the algebraic connectivity equals 1 precisely when gold is
        disconnected. Gold is a DAG: arcs run from larger primes to smaller
        ones, so the relation is never symmetric. Machine checks find gold
        disconnected through <em>X</em>=10<sup>7</sup>, with satellites on
        2-power doors. The first connecting window is the first owner of
        46,137,211: <em>X</em>*=92,274,421, with{" "}
        <em>m</em>₀(<em>X</em>*)=2·46,137,211 and{" "}
        <em>m</em>₀(46,137,211)=2²·11·1,048,573, so two new gold arcs join the
        mainland at 11 to the last island{" "}
        {`{524,287, 1,048,573, 8,388,593}`}. Gold stays connected through{" "}
        <em>X</em>=2.2·10<sup>9</sup>. Thus λ<sub>2</sub>(<em>H</em>
        <sub>
          <em>X</em>
        </sub>
        )=1 fails for some finite <em>X</em>. Every odd prime other than 3 lies in the infinite gold
        component of 5: a Dirichlet bridge in one of two classes modulo{" "}
        15<em>q</em> yields a common owner of 5 and <em>q</em>. Whether gold
        is disconnected for infinitely many finite windows remains open.
      </p>

      <div className="paper-viewer">
        <iframe
          className="paper-frame"
          title="hire-graph-of-the-3-free-door.pdf"
          src="/paper/hire-graph-of-the-3-free-door.pdf?v=1789857354#view=FitH"
        />
      </div>

      <h2>Checked Lean</h2>
      <ul className="paper-lean">
        <li>
          <code>Hire/Cone.lean</code>
          <ul>
            <li>
              <code>lapMatrix_GX_reindex_eq_fromBlocks</code>
            </li>
            <li>
              <code>spectrum_lapMatrix_GX</code>
            </li>
            <li>
              <code>lambda2_eq_one_iff_GoldLeavesDisconnected</code>
            </li>
          </ul>
        </li>
        <li>
          <code>Hire/Lemma8.lean</code>
          <ul>
            <li>
              <code>lemma8_converse_card_three</code>
            </li>
          </ul>
        </li>
        <li>
          <code>Hire/WitnessXstar.lean</code>
          <ul>
            <li>
              <code>m0_Xstar</code>
            </li>
            <li>
              <code>m0_bridgePrime</code>
            </li>
            <li>
              <code>bridgePrime_dvd_arc_mainland</code>
            </li>
            <li>
              <code>bridgePrime_dvd_arc_island</code>
            </li>
            <li>
              <code>bridgePrime_dvd_m0_Xstar</code>
            </li>
            <li>
              <code>m0_islandM19</code> / <code>m0_islandSat</code> /{" "}
              <code>m0_islandSatBig</code>
            </li>
          </ul>
        </li>
        <li>
          <code>Hire/GoldBridge.lean</code>
          <ul>
            <li>
              <code>strong_Q2</code>
            </li>
            <li>
              <code>odd_prime_ne_three_in_gold_component_of_5</code>
            </li>
            <li>
              <code>exists_gold_bridge_prime</code>
            </li>
            <li>
              <code>finite_window_gold_path_of_bridge</code>
            </li>
            <li>
              <code>mersenne_two_power_door_in_gold_component_of_5</code>
            </li>
            <li>
              <code>fermat_prime_in_gold_component_of_5</code>
            </li>
          </ul>
        </li>
      </ul>
    </main>
  );
}
