import { Link } from "react-router-dom";

export function ZetaDoorsPage() {
  return (
    <main className="page notes lab-note-page">
      <h1>Zeta doors</h1>
      <p className="lede">
        Bernoulli denominators of ζ(1−k) for k ≡ 2 (mod 12) produce 3-free
        even doors. Same χ₃ neighbour as hire, different job: the door divides
        the index, rather than a prime dividing another prime’s door.
      </p>

      <aside className="lab-theorem" aria-label="Zeta-door selection rule">
        <p>
          k ≡ 2 (mod 12), p &gt; 3 prime, p − 1 | k
        </p>
        <p className="lab-theorem-implies">
          ⟹ p ≡ 11 (mod 12), m<sub>0</sub>(p) = p − 1 | k.
        </p>
      </aside>
      <p>
        That is the residue restriction on primes selected by the denominator
        construction. Formalised in{" "}
        <code>lean/Hire/ZetaDoors.lean</code> as{" "}
        <code>prime_mod_twelve_of_pred_dvd_index</code>. Von Staudt–Clausen is
        Mathlib’s <code>Bernoulli.vonStaudt_clausen</code>; that Lean file
        mentions it and does not invoke it.
      </p>

      <h2>Even k, 3 not dividing k</h2>
      <p>
        Removing the unique factor of 3 works for every positive even k with
        3 ∤ k, i.e. k ≡ 2, 4, 8, or 10 (mod 12). The exponent of 3 in D is
        1 + v<sub>3</sub>(k); when 3 ∤ k that is exactly one. What remains is
        even and 3-free. The power of 2 can now vary, so d need not be 4T.
      </p>
      <aside className="lab-theorem" aria-label="Relaxed selection rule">
        <p>
          2 | k, 3 ∤ k, p &gt; 3 prime, p − 1 | k
        </p>
        <p className="lab-theorem-implies">
          ⟹ p ≡ 2 (mod 3), m<sub>0</sub>(p) = p − 1 | k.
        </p>
      </aside>
      <p>
        If also 4 ∤ k (k ≡ 2 or 10 (mod 12)), the extra primes are still 11
        (mod 12). If 4 | k they may be 5 or 11 (mod 12). Lean:{" "}
        <code>prime_mod_three_of_pred_dvd_even</code>,{" "}
        <code>prime_mod_twelve_of_pred_dvd_four</code>.
      </p>
      <div className="door-table-wrap">
        <table className="door-table">
          <thead>
            <tr>
              <th>k</th>
              <th>ζ(1−k)</th>
              <th>d = D/3</th>
              <th>neighbour</th>
            </tr>
          </thead>
          <tbody>
            <tr>
              <td>2</td>
              <td>−1/12</td>
              <td>4</td>
              <td>5</td>
            </tr>
            <tr>
              <td>4</td>
              <td>1/120</td>
              <td>40</td>
              <td>41</td>
            </tr>
            <tr>
              <td>8</td>
              <td>1/240</td>
              <td>80</td>
              <td>79</td>
            </tr>
            <tr>
              <td>10</td>
              <td>−1/132</td>
              <td>44</td>
              <td>43</td>
            </tr>
          </tbody>
        </table>
      </div>
      <p>
        All four neighbours are prime here; that is not a law. k = 8 and k = 10
        land on the minus side (Q = d−1), so Q−1 is not the known door. Plus-side
        Pocklington still wants Q = d+1.
      </p>
      <p>
        Sequential census, even k ≤ 10,000 with 3 ∤ k, distinct denominators
        counted once:
      </p>
      <div className="door-table-wrap">
        <table className="door-table">
          <thead>
            <tr>
              <th></th>
              <th>k ≡ 2 (mod 12)</th>
              <th>k ≡ 4, 8, 10</th>
            </tr>
          </thead>
          <tbody>
            <tr>
              <td>indices</td>
              <td>834</td>
              <td>2,500</td>
            </tr>
            <tr>
              <td>distinct D</td>
              <td>171</td>
              <td>1,426</td>
            </tr>
            <tr>
              <td>repeat D</td>
              <td>663</td>
              <td>1,074</td>
            </tr>
            <tr>
              <td>distinct plus-side primes</td>
              <td>29</td>
              <td>160</td>
            </tr>
            <tr>
              <td>distinct χ₃-neighbour primes</td>
              <td>44</td>
              <td>320</td>
            </tr>
          </tbody>
        </table>
      </div>
      <p>
        The original family repeats denominators heavily. Extra residues
        (k ≡ 4, 8, 10) give more distinct D. Residue 10 still has v<sub>2</sub> = 1;
        4 and 8 need v<sub>2</sub> ≥ 2. Sign of Q is not automatic from “wide”: it
        depends on v<sub>2</sub> and Ω(T). Plus-side survivors keep the same
        Pocklington route. <code>--max-digits</code> is the digit cap;
        <code>--family wide</code> is a parallel experiment. Default hunt remains
        tight.
      </p>

      <h2>Route</h2>
      <p>
        ζ(−1) = ζ(−13) = −1/12. Inputs twelve apart, −1, −13, −25, −37, …, do
        not repeat as values. Their reduced denominators often do: 12, 12, 12,
        12, 132, 12, …, 33396, …
      </p>
      <p>
        Write the input as 1−k with k = 12r+2. Von Staudt–Clausen: a prime p
        divides the denominator of ζ(1−k) when p−1 | k. Neither 4 nor 3 divides
        such a k, so neither divides p−1. An odd prime p &gt; 3 with those
        restrictions is 3 (mod 4) and 2 (mod 3), hence 11 (mod 12), and its
        3-free door is exactly p−1.
      </p>
      <p>
        D carries exactly one factor of 3. d = D/3 is even and 3-free. χ₃ picks
        the legal neighbour of d. When that neighbour is Q = d+1, Q−1 = d is
        completely factored and Pocklington applies. The minus side is deferred.
      </p>

      <h2>Two relations</h2>
      <p>
        Extra denominator primes are selected by whether their 3-free doors
        divide the Bernoulli index. Gold asks whether a prime divides another
        prime’s door. Same objects, not the same relation. No claim on islands
        or on Comp(5).
      </p>

      <h2>Small doors</h2>
      <div className="door-table-wrap">
        <table className="door-table">
          <thead>
            <tr>
              <th>D</th>
              <th>d = D/3</th>
              <th></th>
            </tr>
          </thead>
          <tbody>
            <tr>
              <td>12</td>
              <td>4</td>
              <td>
                m<sub>0</sub>(5) = 4
              </td>
            </tr>
            <tr>
              <td>132</td>
              <td>44</td>
              <td>
                m<sub>0</sub>(43) = 44
              </td>
            </tr>
            <tr>
              <td>33,396</td>
              <td>11,132</td>
              <td>
                m<sub>0</sub>(11131) = 11132
              </td>
            </tr>
            <tr>
              <td>6,204</td>
              <td>2,068</td>
              <td>
                m<sub>0</sub>(2069) = 2068
              </td>
            </tr>
            <tr>
              <td>276</td>
              <td>92</td>
              <td>neither neighbour prime</td>
            </tr>
          </tbody>
        </table>
      </div>
      <p>
        Stripped denominators have the form 4T. The eligible neighbour is q =
        4T + (−1)<sup>Ω(T)</sup>. Small modular checks kill many composites.
        That is a sieve, not a primality law.
      </p>

      <h2>Sequential safari</h2>
      <p>
        One thousand terms: 206 distinct denominators; after dropping 3, 55
        were doors of primes and 151 were not. Counting repeats (771/1000)
        double-counts the same successful doors.
      </p>
      <p>
        One million inputs, duplicates removed: 20,356 proven primes, 310
        probable, 151,893 composite (172,559 distinct candidates). Largest
        sequential certified find, from ζ(−4,754,749), 74 digits:
      </p>
      <p>
        <code className="toy-readout">
          12831977569478911260230766030673774233497710762579288907341001842771647653
        </code>
      </p>
      <p>
        m<sub>0</sub>(q) = q−1 = d. All 12,260 plus-side certificates in that
        dump were checked by a separate Python verifier. Arithmetic
        certificates, not Lean. Previously catalogued or not: not checked.
      </p>

      <h2>Targeted kitchen</h2>
      <p>
        Construct k from a handful of small primes so D is large and Q−1 stays
        fully factored. Hunt logs PRP; <code>cert.py</code> proves the longest
        hit in a run; <code>verify.py</code> rebuilds the denominator and
        checks a partial-Pocklington certificate.
      </p>
      <ul>
        <li>
          Longest certified: <strong>18,365 digits</strong> (lions71;
          ζ(1−k) at k = 1522610689958516981964050). 1,598 factors of N−1
          below 2<sup>64</sup>, 19 listed cofactors, F<sup>2</sup> &gt; N.
          Pocklington wall <strong>9 h 2 min</strong> on the Studio (M2 Max,
          12 cores, 32 GB). Independent <code>verify.py</code> passed: F from
          1,598 primes below 2<sup>64</sup>, 19 cofactors proved from the
          index. <code>cert.py</code> writes <code>cert_seconds</code>.
          Same run: 16,213 and 16,165 digits also certified (5 h 19 min
          each). Independent <code>verify.py</code> on those two not yet run.
        </li>
        <li>
          Certified kitchen: <strong>5,522 digits</strong> (also 5,118 and
          4,443). Five listed factors of N−1 sit above 2<sup>64</sup>. The 510
          factors below 2<sup>64</sup> multiply to a 5,419-digit F with F
          <sup>2</sup> &gt; N. Cofactors proved from the factored index.
        </li>
        <li>Farm Boolean length: 3,361 digits (q = 31).</li>
      </ul>
      <p>
        Timing log: <code>analysis/lab-metrics.json</code>. Code:{" "}
        <code>analysis/zeta/zeta-door-safari/</code>,{" "}
        <code>analysis/zeta/zeta-targeted/</code>,{" "}
        <code>lean/Hire/ZetaDoors.lean</code>. Note:{" "}
        <Link to="/notes/zeta-doors">Prime neighbours of zeta denominators</Link>
        .
      </p>
      <p className="home-actions">
        <Link className="nav-link" to="/certificates">
          Certificates
        </Link>
        <Link className="nav-link" to="/rank100">
          Rank 100
        </Link>
        <Link className="nav-link" to="/hire">
          Introduction
        </Link>
      </p>
    </main>
  );
}
