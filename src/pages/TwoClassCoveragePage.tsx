import { Link } from "react-router-dom";
import { DoorGapExplorer } from "../components/DoorGapExplorer";
import { doorCoverageData as data } from "../lib/doorCoverageData";
import { superscript } from "../lib/doorCoverage";
import "./DoorCoveragePage.css";

const fmt = (n: number) => n.toLocaleString("en-GB");
const pct = (n: number, total: number) => `${((100 * n) / total).toFixed(2)}%`;
const source =
  "https://github.com/hasjack/nm-notebook/tree/master/analysis/door-coverage";

/** Lab: two-class coverage + census tables + gap explorer. */
export function TwoClassCoveragePage() {
  return (
    <main className="page notes lab-note-page door-coverage-page">
      <h1>Two-class coverage</h1>
      <p className="lede">
        Which primes hire a fixed odd ingredient Q not divisible by 3, how the
        candidate lattice repeats, and which gap sizes between successive hires
        are allowed. Related: <Link to="/basins">Basins</Link>,{" "}
        <Link to="/zeta-doors">Zeta doors</Link>,{" "}
        <Link to="/notes/hire-graph">Paper 1</Link>.
      </p>
      <p>
        For an odd prime p &gt; 3, χ₃(p) = +1 when p ≡ 1 (mod 3) and −1 when
        p ≡ 2 (mod 3). Its 3-free door is m₀(p) = p + χ₃(p). “Q covers p” means
        Q ∣ m₀(p). Counts are distinct prime targets.
      </p>

      <h2>First appearances</h2>
      <p>
        Before 71, prime doors use 2 and at most one distinct odd prime. The
        smallest door with two distinct odd primes is 2·5·7 = 70; its eligible
        neighbour is prime: 71 = 70 + 1.
      </p>
      <div className="door-table-wrap">
        <table className="door-table">
          <thead>
            <tr>
              <th>Distinct ingredients, including 2</th>
              <th>First prime</th>
              <th>Door</th>
            </tr>
          </thead>
          <tbody>
            {data.thresholds.map((r) => (
              <tr key={r.ingredients}>
                <td>{r.ingredients}</td>
                <td>{fmt(r.prime)}</td>
                <td>
                  {r.factors
                    .map(([q, a]) => `${q}${a > 1 ? superscript(a) : ""}`)
                    .join(" · ")}
                </td>
              </tr>
            ))}
          </tbody>
        </table>
      </div>
      <p>
        First appearances, not permanent steps: 73 goes back to just 2 and 37.
        All rows were found by an exhaustive sieve through one million.
      </p>
      <details>
        <summary>How quickly do two odd ingredients become common?</summary>
        <div className="door-table-wrap">
          <table className="door-table">
            <thead>
              <tr>
                <th>Prime targets through X</th>
                <th>At least two distinct odd ingredients</th>
                <th>Percentage</th>
              </tr>
            </thead>
            <tbody>
              {data.ingredientCensus.map((r) => (
                <tr key={r.limit}>
                  <td>{fmt(r.limit)}</td>
                  <td>
                    {fmt(r.count)} / {fmt(r.total)}
                  </td>
                  <td>{pct(r.count, r.total)}</td>
                </tr>
              ))}
            </tbody>
          </table>
        </div>
      </details>

      <h2>First hires and powers</h2>
      <p>
        Ingredients do not arrive in size order. Nineteen is hired by 37 =
        2·19 − 1, before thirteen is hired by 53 = 4·13 + 1. The table uses all{" "}
        {data.totalSmall} primes with 3 &lt; p ≤ {fmt(data.window)}. First hires
        are searched through {fmt(data.searchLimit)}. A zero percentage means no
        coverage in the smaller window, not that the ingredient is never hired.
      </p>
      <details>
        <summary>All 36 coverage entries, with percentages</summary>
        <div className="door-table-wrap">
          <table className="door-table">
            <thead>
              <tr>
                <th>Door divisible by</th>
                <th>First hire ≤1,000,000</th>
                <th>Covered primes ≤5,000</th>
                <th>Percentage</th>
              </tr>
            </thead>
            <tbody>
              {data.coverage.map((r) => (
                <tr key={r.power}>
                  <td>
                    {r.q}
                    {r.exponent > 1 ? superscript(r.exponent) : ""}
                    {r.exponent > 1 ? ` = ${fmt(r.power)}` : ""}
                  </td>
                  <td>{r.first === null ? "Not seen" : fmt(r.first)}</td>
                  <td>{r.count}</td>
                  <td>{pct(r.count, data.totalSmall)}</td>
                </tr>
              ))}
            </tbody>
          </table>
        </div>
      </details>

      <h2>Layers and overlaps</h2>
      <p>
        Write C<sub>Q</sub> for the primes covered by Q. Powers nest: C₃₄₃ ⊆
        C₄₉ ⊆ C₇. Percentages overlap; they are not portions that should add to
        100%.
      </p>
      <aside className="lab-theorem">
        <p>
          C<sub>A</sub> ∩ C<sub>B</sub> = C<sub>lcm(A,B)</sub>.
        </p>
      </aside>
      <div className="door-table-wrap">
        <table className="door-table">
          <thead>
            <tr>
              <th>Ingredients together</th>
              <th>Count ≤5,000</th>
              <th>Share ≤5,000</th>
              <th>Share ≤1,000,000</th>
              <th>Limiting share</th>
            </tr>
          </thead>
          <tbody>
            {data.overlaps.map((r) => (
              <tr key={`${r.a}-${r.b}`}>
                <td>
                  {r.a} and {r.b}
                </td>
                <td>{r.countSmall}</td>
                <td>{pct(r.countSmall, data.totalSmall)}</td>
                <td>{pct(r.countLarge, data.totalLarge)}</td>
                <td>{pct(1, r.limitingDenominator)}</td>
              </tr>
            ))}
          </tbody>
        </table>
      </div>
      <p>
        For fixed odd Q coprime to 3, the share of prime doors divisible by Q
        tends to 1/φ(Q). In particular qᵃ has limiting coverage
        1/[qᵃ⁻¹(q−1)]. This is the prime-number theorem for arithmetic
        progressions on the two reduced classes below — fixed-Q density as the
        window grows, not a claim when Q grows with the window.
      </p>

      <h2>Where are the gaps?</h2>
      <p>
        The top lane shows ordinary consecutive-prime gaps. Each lower lane
        shows eligible candidates for its ingredient: filled dots are prime,
        hollow dots are composite. Shading separates consecutive successful
        hires. Click a point or use the inspection controls.
      </p>
      <DoorGapExplorer />
      <p>
        For Q = 49 the candidate residues are 97 and 197 modulo 294. Observed
        waits such as 588 = 2·294 and 488 = 194+100+194 obey the gap rule below.
      </p>

      <h2>Two-class coverage lemma</h2>
      <aside className="lab-theorem" aria-label="Two-class coverage lemma">
        <p>
          <strong>Two-class coverage.</strong> Let Q &gt; 1 be odd, 3 ∤ Q, and
          s = χ₃(Q) ∈ {"{"}−1, 1{"}"}. For every prime p &gt; 3,
        </p>
        <p className="lab-theorem-implies">
          Q ∣ m₀(p) ⟺ p ≡ 2Q − s or 4Q + s (mod 6Q).
        </p>
      </aside>
      <p>
        Formalised in <code>lean/Hire/TwoClassCoverage.lean</code> as{" "}
        <code>two_class_coverage</code> and <code>hire_gap_mod</code>. Also
        Lemma <code>lem:two-class</code> in Paper 1.
      </p>
      <aside className="lab-theorem" aria-label="Gap corollary">
        <p>
          <strong>Gap corollary.</strong> Any gap between two successive primes
          hiring Q satisfies
        </p>
        <p className="lab-theorem-implies">
          gap ≡ 0, ±(2Q + 2s) (mod 6Q).
        </p>
        <p>For Q = 49: exactly 0, 100, or 194 (mod 294).</p>
      </aside>
      <div className="door-table-wrap">
        <table className="door-table">
          <thead>
            <tr>
              <th>Q</th>
              <th>Period 6Q</th>
              <th>Alternating candidate gaps</th>
              <th>Possible hire-gap residues</th>
            </tr>
          </thead>
          <tbody>
            <tr>
              <td>5</td>
              <td>30</td>
              <td>8, 22</td>
              <td>0, 8, 22</td>
            </tr>
            <tr>
              <td>7</td>
              <td>42</td>
              <td>16, 26</td>
              <td>0, 16, 26</td>
            </tr>
            <tr>
              <td>49</td>
              <td>294</td>
              <td>100, 194</td>
              <td>0, 100, 194</td>
            </tr>
            <tr>
              <td>11</td>
              <td>66</td>
              <td>20, 46</td>
              <td>0, 20, 46</td>
            </tr>
          </tbody>
        </table>
      </div>

      <aside className="lab-theorem" aria-label="Infinite hire corollary">
        <p>
          <strong>Corollary (infinite hire of a fixed ingredient).</strong> Let
          Q &gt; 1 be odd with 3 ∤ Q. Then infinitely many primes p satisfy Q ∣
          m₀(p).
        </p>
        <p className="lab-theorem-implies">
          Two-class coverage + Dirichlet on those APs.
        </p>
      </aside>
      <p>
        Formalised in <code>lean/Hire/InfiniteHire.lean</code> as{" "}
        <code>infinite_primes_hire</code> and{" "}
        <code>exists_prime_hire_gt</code>. Paper 1 Corollary{" "}
        <code>cor:infinite-hire</code> after GoldBridge.
      </p>

      <h2>Blowing it up: a 181-digit prime</h2>
      <p>
        Choosing a factored door also gives a candidate generator. N =
        49·2⁵⁹⁴ + 1 is prime, with m₀(N) = 49·2⁵⁹⁴, so its 49 coverage is built
        in. The modular check satisfies Proth’s theorem (witness 3); the
        reproduction script also checks Pocklington witnesses for the prime
        factors of N−1.
      </p>
      <aside className="lab-theorem">
        <p>
          3<sup>(N−1)/2</sup> ≡ −1 (mod N), with 49 odd and 49 &lt; 2⁵⁹⁴.
        </p>
      </aside>
      <details>
        <summary>The prime in decimal</summary>
        <p className="coverage-decimal">{data.certificate.decimal}</p>
      </details>

      <p>
        Reproduction: <a href={source}>analysis/door-coverage</a>.{" "}
        <code>python3 analysis/door-coverage/experiment.py</code> regenerates
        every census table and verifies the Proth certificate.
      </p>
    </main>
  );
}
