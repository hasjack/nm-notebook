import { Link } from "react-router-dom";

/** Lab write-up: two-class coverage of primes hiring an odd 3-free Q. */
export function TwoClassCoveragePage() {
  return (
    <main className="page notes lab-note-page">
      <h1>Two-class coverage</h1>
      <p className="lede">
        Afternoon Lab: which primes hire a fixed odd ingredient Q not divisible
        by 3, and which gap sizes between successive such primes are allowed.
        Short supporting lemma: elementary modular arithmetic that pins the
        repeating lane picture. Related:{" "}
        <Link to="/basins">Basins</Link>, <Link to="/zeta-doors">Zeta doors</Link>
        .
      </p>

      <h2>Eligible doors</h2>
      <p>
        For odd Q &gt; 1 with 3 ∤ Q, a door divisible by Q is an even multiple of
        Q. Excluding multiples of 3 (those contain a factor of 3) leaves
        multipliers congruent to 2 or 4 modulo 6:
      </p>
      <p>
        2Q, 4Q, 8Q, 10Q, 14Q, 16Q, …
      </p>
      <p>
        The door rule then picks the neighbour that avoids 3. That produces two
        candidate positions in every interval of length 6Q.
      </p>

      <h2>Lane table</h2>
      <p>
        Repeating interval 6Q, with alternating candidate gaps inside each
        period:
      </p>
      <div className="door-table-wrap">
        <table className="door-table">
          <thead>
            <tr>
              <th>Lane Q</th>
              <th>Period 6Q</th>
              <th>Alternating gaps</th>
            </tr>
          </thead>
          <tbody>
            <tr>
              <td>5</td>
              <td>30</td>
              <td>8, 22</td>
            </tr>
            <tr>
              <td>7</td>
              <td>42</td>
              <td>16, 26</td>
            </tr>
            <tr>
              <td>
                7<sup>2</sup> = 49
              </td>
              <td>294</td>
              <td>100, 194</td>
            </tr>
            <tr>
              <td>11</td>
              <td>66</td>
              <td>20, 46</td>
            </tr>
          </tbody>
        </table>
      </div>
      <p className="figure-caption">
        Hollow and filled dots together mark the exact repeating candidate
        lattice; primality decides which candidates get filled. Longer waits
        between filled dots are sums of the basic spacings. For Q = 49: 588 =
        2·294, 488 = 194+100+194, 294 = 100+194.
      </p>

      <aside className="lab-theorem" aria-label="Two-class coverage lemma">
        <p>
          <strong>Two-class coverage.</strong> Let Q &gt; 1 be odd, 3 ∤ Q, and s =
          χ₃(Q) ∈ {"{"}−1, 1{"}"}. For every prime p &gt; 3,
        </p>
        <p className="lab-theorem-implies">
          Q | m₀(p) ⟺ p ≡ 2Q − s or 4Q + s (mod 6Q).
        </p>
      </aside>
      <p>
        Proof sketch: a door divisible by Q is an even multiple of Q. Excluding
        multiples of 3 leaves k ≡ 2 or 4 (mod 6). The sign follows from the door
        rule. Formalised in{" "}
        <code>lean/Hire/TwoClassCoverage.lean</code> as{" "}
        <code>two_class_coverage</code> (iff) and{" "}
        <code>hire_gap_mod</code> (gap corollary). Lab shelf only, not in the
        Hire barrel.
      </p>

      <aside className="lab-theorem" aria-label="Gap corollary">
        <p>
          <strong>Gap corollary.</strong> Any gap between two successive primes
          hiring Q satisfies
        </p>
        <p className="lab-theorem-implies">
          gap ≡ 0, ±(2Q + 2s) (mod 6Q).
        </p>
        <p>
          For Q = 49: exactly 0, 100, or 194 (mod 294).
        </p>
      </aside>
      <p>
        That is an exact restriction on allowed waits, not a bound on how long
        you wait until the next hire of Q. Shaded bands on the Lab figure mark
        prime-to-prime waits; alternating shading is visual separation only. The
        mathematical regularity is the candidate lattice and the three allowed
        gap classes. Which candidates survive, and how many fail in succession,
        is still open Lab investigation.
      </p>

      <aside className="lab-theorem" aria-label="Infinite hire corollary">
        <p>
          <strong>Corollary (infinite hire of a fixed ingredient).</strong> Let
          Q &gt; 1 be odd with 3 ∤ Q. Then infinitely many primes p satisfy Q |
          m₀(p).
        </p>
        <p className="lab-theorem-implies">
          Two-class coverage + Dirichlet on those APs.
        </p>
      </aside>
      <p>
        Formalised in <code>lean/Hire/InfiniteHire.lean</code> as{" "}
        <code>infinite_primes_hire</code> and{" "}
        <code>exists_prime_hire_gt</code>. Same Dirichlet fact as GoldBridge’s
        classes, named for a fixed Q. Lab shelf for now; Albert has a half-page
        Paper 1 insert draft if Jack thaws.
      </p>

      <aside className="lab-note-caveats" aria-label="Lab freeze">
        <p>
          <strong>Lab freeze.</strong> Two-class + infinite hire are
          supporting Lab arithmetic (Dirichlet on named classes). Hire-rate
          stays the analytic target. Papers frozen unless the Paper 1 corollary
          insert is thawed.
        </p>
      </aside>
    </main>
  );
}
