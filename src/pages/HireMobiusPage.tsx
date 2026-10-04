import { REPO_URL } from "../lib/meta";

const MOBIUS_FILE = `${REPO_URL}/blob/master/lean/Hire/Mobius.lean`;
const MOBIUS_DOOR_FILE = `${REPO_URL}/blob/master/lean/Hire/MobiusDoor.lean`;

export function HireMobiusPage() {
  return (
    <main className="page notes lab-note-page">
      <h1>Möbius cancellation and Hire sinks</h1>
      <p className="lede">
        This shelf records a formalized exact inclusion-exclusion identity for
        Hire. The Möbius weights do not estimate the sink count; after pairing
        odd divisors with their doubles, they count it exactly.
      </p>

      <section>
        <h2>The objects</h2>
        <p>
          For a finite set <code>T</code> of hired primes,{" "}
          <code>doorDivisorSet T</code> collects all divisors of the doors{" "}
          <code>m₀(p)</code>. For a divisor <code>e</code>,{" "}
          <code>doorDivisorCount T e</code> counts how many of those doors are
          divisible by <code>e</code>.
        </p>
        <p>
          The Lean files are{" "}
          <a href={MOBIUS_FILE}>
            <code>lean/Hire/Mobius.lean</code>
          </a>{" "}
          and{" "}
          <a href={MOBIUS_DOOR_FILE}>
            <code>lean/Hire/MobiusDoor.lean</code>
          </a>
          .
        </p>
      </section>

      <section>
        <h2>The identity</h2>
        <p>
          For non-hub hired vertices, the final theorem{" "}
          <code>odd_moebius_sum_eq_sink_count</code> proves:
        </p>
        <p className="lab-inline-formula">
          Σ e ∈ D_T, e odd, μ(e) A_T(e) = #{"{p ∈ T : IsSink X p}"}
        </p>
        <p>
          Here <code>D_T = doorDivisorSet T</code> and{" "}
          <code>A_T(e) = doorDivisorCount T e</code>. “Sink” means no outgoing
          gold arcs, with window membership and exclusion of the hub{" "}
          <code>2</code> explicit in the theorem hypotheses.
        </p>
      </section>

      <section>
        <h2>Why cancellation works</h2>
        <p>
          Mathlib supplies the logarithmic Möbius identity over divisors. The
          Hire door calculation first shows the weighted sum is nonzero exactly
          at two-power doors, hence exactly at gold sinks.
        </p>
        <p>
          The logarithms then disappear by pairing each odd divisor{" "}
          <code>e</code> with <code>2e</code>. Those two divisors hit the same
          doors, their Möbius signs are opposite, and their weighted
          contribution collapses to <code>-log 2 · μ(e) · A_T(e)</code>. Terms
          divisible by <code>4</code> vanish because their Möbius value is zero.
          Cancelling the nonzero factor <code>-log 2</code> leaves the exact
          odd-divisor count identity.
        </p>
      </section>

      <section>
        <h2>Scope</h2>
        <aside className="lab-note-caveats" aria-label="Scope">
          <p>
            This reformulates the existing two-power-door sink criterion as an
            exact finite identity. It does not give a new asymptotic estimate,
            progress on RH, or CRT-branch bounds; packaging the congruence
            branches into residue classes remains future work.
          </p>
        </aside>
      </section>
    </main>
  );
}
