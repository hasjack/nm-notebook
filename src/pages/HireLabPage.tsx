import { Link } from "react-router-dom";

export function HireLabPage() {
  return (
    <main className="page hire-lab-page lab-note-page">
      <h1>Hire rate</h1>
      <p className="lede">
        Odd hires through window <em>X</em> — thin rem-sieve lab table. Dial
        spectra live on <Link to="/hire-spectrum">Spectrum</Link>; the door
        handshake is on <Link to="/hire">Introduction</Link>. Record-scale
        seating is on <Link to="/microscope">Microscope</Link> /{" "}
        <Link to="/corridor">Corridor</Link>.
      </p>

      <p className="islands-bernard">
        At <em>X</em> = 2·10<sup>10</sup>: <em>R</em> ≈ 1.091, <em>R</em>
        <sub>Pois</sub> ≈ 1.014, <em>E</em>
        <sub>2</sub> ≈ 7.82. <em>C</em> unnamed.
      </p>

      <section className="hire-beat lab-note-hierarchy">
        <h2>Hierarchy (Lab freeze)</h2>
        <p>Map of this page — what the lab treats as known, in order:</p>
        <ol className="lab-note-hierarchy-list">
          <li>
            <strong>Leading law</strong> — <em>R</em>(<em>X</em>) from the
            thin rem-sieve count <em>H</em>(<em>X</em>).
          </li>
          <li>
            <strong>Poisson</strong> — <em>R</em>
            <sub>Pois</sub> = <em>H</em> / Σ (1 − e<sup>−Li(<em>X</em>)/q</sup>);
            residuals <em>E</em>
            <sub>1</sub>, <em>E</em>
            <sub>2</sub>.
          </li>
          <li>
            <strong>Bernoulli</strong> — owner indicators as heterogeneous
            coins; multiplicity / under-dispersion on the λ-frontier.
          </li>
          <li>
            <strong>Q / T</strong> — finite-Bernoulli scale{" "}
            <em>Q</em>
            <sub>X</sub>(λ) and <em>T</em>
            <sub>X</sub> = (<em>Q</em> − 1) log <em>X</em>; cubic predictor{" "}
            <em>Q</em>
            <sub>2nd</sub>.
          </li>
        </ol>
        <p className="figure-caption">
          <em>C</em> in the shape <em>R</em>
          <sub>Pois</sub> ≈ 1 + <em>C</em>/(log <em>X</em>)<sup>2</sup> stays
          unnamed. Papers 1–2 frozen; open notebook.
        </p>
      </section>

      <section className="hire-beat">
        <h2>Euler door checkpoint</h2>
        <aside className="lab-theorem" aria-label="Euler door checkpoint">
          <p className="lab-theorem-implies">
            The checked finite identity is exact: door divisibility, owner
            residue classes, prime-power multiplicity, and the weighted log
            reconstruction are the same bookkeeping seen from four angles.
          </p>
        </aside>
        <p>
          The new Lean file records the local algebra for a single Euler factor,
          then counts owners using the repository&apos;s actual <em>m</em>
          <sub>0</sub>. For every modulus <em>Q</em> &gt; 1, a kept door is
          divisible by <em>Q</em> exactly in the two residue cases{" "}
          <em>p</em> ≡ 1 mod 3 with <em>p</em> ≡ −1 mod <em>Q</em>, or{" "}
          <em>p</em> ≡ 2 mod 3 with <em>p</em> ≡ 1 mod <em>Q</em>.
        </p>
        <p>
          Multiplicity is counted by prime-power levels. For example,{" "}
          <em>m</em>
          <sub>0</sub>(31) = 32 = 2<sup>5</sup>, so the arc to 2 contributes{" "}
          5 log 2 to the total door logarithm. Grouping every selected door by
          destination prime reconstructs the same total as{" "}
          Σ multiplicity(<em>q</em>) log <em>q</em>.
        </p>
        <p>
          The truncation checkpoint makes that bookkeeping quantitative. A door
          containing 2<sup>5</sup> contributes five copies of 2; if the first two
          levels are retained, three copies remain in the tail. In Lean,{" "}
          <code>incomingMultiplicity_truncation_error_le</code> connects that
          exact error to a combined low/high tail bound.
        </p>
        <aside className="lab-theorem" aria-label="Euler door tail bound">
          <p className="lab-theorem-implies">
            truncation error ≤ C r<sup>K+1</sup> / (1 − r) + 2X r
            <sup>J+1</sup> / (1 − r) + 2 max(B − J − 1, 0), with r = 1/q.
          </p>
        </aside>
        <p>
          Here <em>K</em> is the last retained level, <em>J</em> splits lower
          omitted levels from the high tail, and <em>B</em> is the exclusive
          level bound chosen so every selected door is below q<sup>B</sup>. The
          coefficient <em>C</em> belongs to the assumed lower-level estimate{" "}
          <em>N</em>
          <sub>
            q<sup>k</sup>
          </sub>
          (<em>X</em>) ≤ <em>C</em>q<sup>−k</sup>.
        </p>
        <p>
          Proved in this file: <code>slot_sum_Ico_le_geometric</code>,{" "}
          <code>incomingMultiplicityHighTail_le_geometric</code>,{" "}
          <code>incomingMultiplicityLowTail_le_geometric</code>,{" "}
          <code>incomingMultiplicityTail_le_combined</code>, and the exact
          truncation-error bridge above. The high-level term follows from
          integer-slot estimates; the lower-level term is conditional on the
          explicit hypothesis <code>hLow</code>.
        </p>
        <p>
          The latest bridge replaces that abstract lower-level hypothesis by a
          prime-class input. The checked chain is: owner divisibility → two
          reduced CRT classes → <code>primeResidueCount</code> bounds → geometric
          level bounds → <code>truncation_error_le_of_prime_class_bounds</code>.
          For <em>q</em> = 5 and <em>k</em> = 1, the owner conditions pick the
          two reduced residues 4 and 11 modulo 15.
        </p>
        <p>
          The analytic input is now named <code>hAP</code>: it supplies bounds
          for prime counts in reduced classes at the lower omitted levels. Lean
          verifies that those bounds imply the stated Hire truncation-error
          estimate; it does not yet prove the prime-counting estimate itself.
          The next Lean bridge,{" "}
          <code>truncation_error_le_of_brun_titchmarsh</code>, makes the same
          transfer from an explicitly supplied Brun–Titchmarsh inequality under
          a square-root cutoff. The analytic inequality is still a hypothesis;
          the limiting average q/(q−1)<sup>2</sup> is the next mathematical
          target.
        </p>
        <aside className="lab-theorem" aria-label="Fixed hub coefficient">
          <p className="lab-theorem-implies">
            Σ<sub>k≥1</sub> 1/(q<sup>k−1</sup>(q−1)) = q/(q−1)<sup>2</sup>.
            For q = 13, the target limiting average is 13/144.
          </p>
        </aside>
        <p>
          The numerical mod-15 experiment takes the <em>q</em> = 5,{" "}
          <em>k</em> = 1 classes seriously as an explicit-formula observable:
          <em>S</em>(<em>x</em>) = Σ<sub>n≤x</sub> Λ(<em>n</em>)(<em>x</em> −{" "}
          <em>n</em>), restricted to residues 4 and 11 modulo 15. It includes
          logarithmic weights, prime powers, and smoothing, so translating it to
          ordinary prime-owner counts is a further step.
        </p>
        <p>
          Character orthogonality decomposes this observable into the principal
          character contribution, a quadratic character induced from conductor
          5, and a complex-conjugate pair of conductor-15 characters. The scripts
          account for the induced character&apos;s removed Euler factor and the
          explicit formula&apos;s correction terms; the coefficients are fixed by
          arithmetic, with no fitted frequencies.
        </p>
        <div className="door-table-wrap">
          <table className="door-table">
            <caption>
              Full corrected, normalised reconstruction over 10
              <sup>3</sup> ≤ <em>x</em> ≤ 10<sup>6</sup>
            </caption>
            <thead>
              <tr>
                <th>zero-height cutoff</th>
                <th>20</th>
                <th>40</th>
                <th>80</th>
              </tr>
            </thead>
            <tbody>
              <tr>
                <td>relative RMS error</td>
                <td>7.22%</td>
                <td>2.35%</td>
                <td>1.10%</td>
              </tr>
            </tbody>
          </table>
        </div>
        <p>
          The final nested critical-line scans, with steps 0.25 and 0.125,
          agreed on 40 positive-height roots for conductor 5 and 108 roots
          between heights −80 and 80 for the chosen complex conductor-15
          character. Refined root residuals were below 10<sup>−21</sup>. These
          are numerical checks, not certified complete zero lists.
        </p>
        <p>
          The RH connection is through the principal character: zeta zeros
          contribute there. The reconstruction uses computed critical-line
          zeros; RH asks whether every nontrivial zeta zero lies on that line.
          The next milestones are to reproduce the experiment locally, translate
          the smoothed prime-power observable to ordinary owner counts, test
          another hub with coefficients fixed before plotting, and resume the
          fixed-hub average proof using explicit analytic inputs.
        </p>
        <div className="door-table-wrap">
          <table className="door-table">
            <caption>
              Incoming multiplicities from the experiment at <em>X</em> = 10
              <sup>6</sup>
            </caption>
            <thead>
              <tr>
                <th>q</th>
                <th>2</th>
                <th>5</th>
                <th>7</th>
                <th>11</th>
                <th>13</th>
              </tr>
            </thead>
            <tbody>
              <tr>
                <td>multiplicity</td>
                <td>157,097</td>
                <td>24,489</td>
                <td>15,238</td>
                <td>8,645</td>
                <td>7,086</td>
              </tr>
            </tbody>
          </table>
        </div>
        <p className="figure-caption">
          This checkpoint is finite algebra and exact counting. The proposed
          fixed-<em>q</em> estimate <em>A</em>
          <sub>q</sub>(<em>X</em>) ~ <em>N</em>(<em>X</em>) q/(q−1)
          <sup>2</sup> for q ≠ 3 is not proved here. The Dedekind-zeta reading
          remains mathematical context, not a Lean identification; evaluating
          individual local factors at 1 does not justify an infinite Euler
          product at 1, and this proves no constraint on zeta zeros. One bridge
          also remains open: the generic Euler-factor statements have not yet
          been specialised to <code>Hire.chi3</code>, <code>Hire.m0</code>, and{" "}
          <code>Hire.m1</code>. The next milestone is to supply the lower-level
          Brun–Titchmarsh input, choose the cutoffs, and assemble the limiting
          average-multiplicity argument using prime densities in fixed arithmetic
          progressions. Experiments through <em>X</em> = 100,000,000 support the
          predicted average q/(q−1)<sup>2</sup> for each fixed prime q ≠ 3, but
          this Lean file does not prove that limit.
        </p>
      </section>

      <section className="hire-beat">
        <h2>Leading counts</h2>
        <aside className="lab-theorem" aria-label="H frozen">
          <p className="lab-theorem-implies">
            H(X) = #&#123;q prime : 5 ≤ q ≤ X, ∃ p ≤ X, p ≠ 3, q | m₀(p)&#125;
            with P = X (hire_rate_HX).
          </p>
        </aside>
        <p>
          Odd hires through window <em>X</em>: that count is also written{" "}
          <em>H</em>(<em>X</em>)=|
          <em>S</em>
          <sub>
            <em>X</em>
          </sub>
          |−1. Thin rem-sieve through 2·10<sup>10</sup>. <em>R</em> uses the
          leading law; <em>R</em>
          <sub>Pois</sub> divides by the Li/Poisson first-hire sum; <em>E</em>
          <sub>1</sub>=(<em>R</em>
          <sub>Pois</sub>−1) log <em>X</em> and <em>E</em>
          <sub>2</sub>=(<em>R</em>
          <sub>Pois</sub>−1)(log <em>X</em>)<sup>2</sup>. Keep this{" "}
          <em>H</em>(<em>X</em>) off the cube-doors polynomial <em>H</em>.
        </p>
        <div className="door-table-wrap hire-rate-wrap">
          <table className="door-table hire-rate-table">
            <thead>
              <tr>
                <th>
                  <em>X</em>
                </th>
                <th>
                  <em>H</em>
                </th>
                <th>π</th>
                <th>
                  <em>H</em>/π
                </th>
                <th>
                  <em>R</em>
                </th>
                <th>
                  <em>R</em>
                  <sub>Pois</sub>
                </th>
                <th>
                  <em>E</em>
                  <sub>1</sub>
                </th>
                <th>
                  <em>E</em>
                  <sub>2</sub>
                </th>
              </tr>
            </thead>
            <tbody>
              <tr>
                <td>10<sup>4</sup></td>
                <td>361</td>
                <td>1,229</td>
                <td>0.294</td>
                <td>1.379</td>
                <td>1.044</td>
                <td>0.408</td>
                <td>3.76</td>
              </tr>
              <tr>
                <td>10<sup>5</sup></td>
                <td>2,401</td>
                <td>9,592</td>
                <td>0.250</td>
                <td>1.302</td>
                <td>1.052</td>
                <td>0.604</td>
                <td>6.95</td>
              </tr>
              <tr>
                <td>5·10<sup>5</sup></td>
                <td>9,291</td>
                <td>41,538</td>
                <td>0.224</td>
                <td>1.243</td>
                <td>1.038</td>
                <td>—</td>
                <td>—</td>
              </tr>
              <tr>
                <td>10<sup>6</sup></td>
                <td>16,688</td>
                <td>78,498</td>
                <td>0.213</td>
                <td>1.213</td>
                <td>1.026</td>
                <td>0.357</td>
                <td>4.93</td>
              </tr>
              <tr>
                <td>10<sup>7</sup></td>
                <td>125,661</td>
                <td>664,579</td>
                <td>0.189</td>
                <td>1.174</td>
                <td>1.026</td>
                <td>0.423</td>
                <td>6.82</td>
              </tr>
              <tr>
                <td>10<sup>8</sup></td>
                <td>980,292</td>
                <td>5,761,455</td>
                <td>0.170</td>
                <td>1.142</td>
                <td>1.022</td>
                <td>0.413</td>
                <td>7.61</td>
              </tr>
              <tr>
                <td>10<sup>9</sup></td>
                <td>7,877,140</td>
                <td>50,847,534</td>
                <td>0.155</td>
                <td>1.116</td>
                <td>1.018</td>
                <td>0.379</td>
                <td>7.84</td>
              </tr>
              <tr>
                <td>2.2·10<sup>9</sup></td>
                <td>16,173,662</td>
                <td>107,540,122</td>
                <td>0.150</td>
                <td>1.109</td>
                <td>1.017</td>
                <td>0.367</td>
                <td>7.90</td>
              </tr>
              <tr>
                <td>5·10<sup>9</sup></td>
                <td>34,296,996</td>
                <td>234,954,223</td>
                <td>0.146</td>
                <td>1.101</td>
                <td>1.016</td>
                <td>0.352</td>
                <td>7.85</td>
              </tr>
              <tr>
                <td>10<sup>10</sup></td>
                <td>64,838,984</td>
                <td>455,052,511</td>
                <td>0.142</td>
                <td>1.096</td>
                <td>1.015</td>
                <td>0.342</td>
                <td>7.88</td>
              </tr>
              <tr>
                <td>1.5·10<sup>10</sup></td>
                <td>94,178,863</td>
                <td>670,180,516</td>
                <td>0.141</td>
                <td>1.093</td>
                <td>1.014</td>
                <td>0.335</td>
                <td>7.86</td>
              </tr>
              <tr>
                <td>2·10<sup>10</sup></td>
                <td>122,776,796</td>
                <td>882,206,716</td>
                <td>0.139</td>
                <td>1.091</td>
                <td>1.014</td>
                <td>0.330</td>
                <td>7.82</td>
              </tr>
            </tbody>
          </table>
        </div>
        <p className="figure-caption">
          Tip: <em>R</em>≈1.091, <em>R</em>
          <sub>Pois</sub>≈1.014, <em>E</em>
          <sub>2</sub>≈7.8–7.9 from ~10<sup>8</sup> while <em>E</em>
          <sub>1</sub> drifts down — shape <em>R</em>
          <sub>Pois</sub>≈1+<em>C</em>/(log <em>X</em>)<sup>2</sup> with{" "}
          <em>C</em>≈8. Notes stay frozen.
        </p>
        <p className="figure-caption">
          Sparsity: <em>H</em>(<em>X</em>)/π(<em>X</em>)∼ log log <em>X</em>/log{" "}
          <em>X</em> — every odd prime ≠3 arrives eventually, but by window{" "}
          <em>X</em> only a vanishing fraction of π(<em>X</em>) is hired. That
          is why islands can breathe.
        </p>
        <h3>Easy moduli are all hired</h3>
        <p className="figure-caption">
          Easy moduli are all hired. Bombieri–Vinogradov does not give a baby{" "}
          <em>C</em>.
        </p>
        <p>
          Restrict hires to <em>q</em> ≤ √<em>X</em>. Through{" "}
          <em>X</em> = 2·10<sup>6</sup> every such <em>q</em> is already hired,
          so <em>H</em>
          <sub>√<em>X</em></sub> = π(√<em>X</em>) ∼ 2√<em>X</em>/log{" "}
          <em>X</em> — not <em>X</em> log log <em>X</em>/(log <em>X</em>)
          <sup>2</sup>. Plug that count into the full formula and{" "}
          <em>C</em>
          <sub>√</sub> → 0, as it must. The measured shape to 10<sup>10</sup>{" "}
          lives in the unsaturated tail √<em>X</em> &lt; <em>q</em> ≤{" "}
          <em>X</em>. Vertex <em>H</em>(<em>X</em>) is a large-moduli statement;
          the ~85% least-factor slot is where that tail lives. Small{" "}
          <em>q</em> saturate early.
        </p>
        <div className="door-table-wrap hire-rate-wrap">
          <table className="door-table hire-rate-table">
            <thead>
              <tr>
                <th>
                  <em>X</em>
                </th>
                <th>
                  <em>H</em>
                </th>
                <th>
                  <em>H</em>
                  <sub>√</sub>
                </th>
                <th>π(√)</th>
                <th>
                  <em>H</em>
                  <sub>√</sub>/π(√)
                </th>
                <th>
                  <em>C</em>
                  <sub>full</sub>
                </th>
                <th>
                  <em>C</em>
                  <sub>√</sub>
                </th>
              </tr>
            </thead>
            <tbody>
              <tr>
                <td>10<sup>3</sup></td>
                <td>60</td>
                <td>9</td>
                <td>9</td>
                <td>1.000</td>
                <td>1.48</td>
                <td>0.22</td>
              </tr>
              <tr>
                <td>10<sup>4</sup></td>
                <td>361</td>
                <td>23</td>
                <td>23</td>
                <td>1.000</td>
                <td>1.38</td>
                <td>0.09</td>
              </tr>
              <tr>
                <td>10<sup>5</sup></td>
                <td>2,401</td>
                <td>63</td>
                <td>63</td>
                <td>1.000</td>
                <td>1.30</td>
                <td>0.03</td>
              </tr>
              <tr>
                <td>10<sup>6</sup></td>
                <td>16,688</td>
                <td>166</td>
                <td>166</td>
                <td>1.000</td>
                <td>1.21</td>
                <td>0.01</td>
              </tr>
              <tr>
                <td>2·10<sup>6</sup></td>
                <td>30,539</td>
                <td>221</td>
                <td>221</td>
                <td>1.000</td>
                <td>1.20</td>
                <td>0.009</td>
              </tr>
            </tbody>
          </table>
        </div>
        <h3>The tail is the whole curve</h3>
        <p className="figure-caption">
          The tail is the whole curve. Almost all of <em>H</em> sits above{" "}
          <em>X</em>
          <sup>0.7</sup>.
        </p>
        <p>
          Band split through <em>X</em> = 3·10<sup>6</sup>: at the tip,{" "}
          39,808/43,459 ≈ 92% of hires have <em>q</em> &gt; <em>X</em>
          <sup>0.7</sup>, and <em>C</em>
          <sub>tail</sub> ≈ <em>C</em>
          <sub>full</sub>. The baby-BV slice is a rounding error on the vertex
          count. Edges grow like π(<em>X</em>) log log <em>X</em> — different
          object, different shape; useful as a check, not a twin of{" "}
          <em>H</em>. Σ 1/<em>q</em> is still climbing (1.15 → 1.97); if the
          heuristic is right it converges, but the remaining increment is ∼ log
          log <em>X</em>/log <em>X</em>, so it will not sit tonight. Proving{" "}
          <em>H</em> is proving that primes <em>q</em> ∈ (<em>X</em>
          <sup>0.7</sup>, <em>X</em>] keep appearing as factors of doors with{" "}
          <em>p</em> ≤ <em>X</em> — progressions mod <em>q</em> past √
          <em>X</em>. Reweighting (edges or Σ 1/<em>q</em>) does not dodge that
          band.
        </p>
        <div className="door-table-wrap hire-rate-wrap">
          <table className="door-table hire-rate-table">
            <thead>
              <tr>
                <th>
                  <em>X</em>
                </th>
                <th>
                  <em>H</em>
                </th>
                <th>
                  <em>q</em> ≤ √<em>X</em>
                </th>
                <th>
                  √<em>X</em> &lt; <em>q</em> ≤ <em>X</em>
                  <sup>0.7</sup>
                </th>
                <th>
                  <em>X</em>
                  <sup>0.7</sup> &lt; <em>q</em> ≤ <em>X</em>
                </th>
                <th>edges</th>
                <th>Σ 1/<em>q</em></th>
                <th>
                  <em>C</em>
                  <sub>full</sub>
                </th>
                <th>
                  <em>C</em>
                  <sub>tail</sub>
                </th>
              </tr>
            </thead>
            <tbody>
              <tr>
                <td>10<sup>3</sup></td>
                <td>60</td>
                <td>9</td>
                <td>18</td>
                <td>33</td>
                <td>216</td>
                <td>1.15</td>
                <td>1.48</td>
                <td>1.26</td>
              </tr>
              <tr>
                <td>10<sup>4</sup></td>
                <td>361</td>
                <td>23</td>
                <td>89</td>
                <td>249</td>
                <td>2,017</td>
                <td>1.45</td>
                <td>1.38</td>
                <td>1.29</td>
              </tr>
              <tr>
                <td>10<sup>5</sup></td>
                <td>2,401</td>
                <td>63</td>
                <td>381</td>
                <td>1,957</td>
                <td>18,072</td>
                <td>1.70</td>
                <td>1.30</td>
                <td>1.27</td>
              </tr>
              <tr>
                <td>10<sup>6</sup></td>
                <td>16,688</td>
                <td>166</td>
                <td>1,679</td>
                <td>14,843</td>
                <td>164,104</td>
                <td>1.89</td>
                <td>1.21</td>
                <td>1.20</td>
              </tr>
              <tr>
                <td>3·10<sup>6</sup></td>
                <td>43,459</td>
                <td>267</td>
                <td>3,384</td>
                <td>39,808</td>
                <td>471,040</td>
                <td>1.97</td>
                <td>1.19</td>
                <td>1.19</td>
              </tr>
            </tbody>
          </table>
        </div>
        <h3>The tail is the theorem</h3>
        <p className="figure-caption">
          The tail is the theorem. Small <em>q</em> saturate; only the tail is
          new.
        </p>
        <p>
          Write <em>H</em>(<em>X</em>) = π(√<em>X</em>) + Tail(<em>X</em>) and
          delete the cheap half. Below √<em>X</em> every <em>q</em> is already
          hired. The mass — where <em>C</em>(<em>X</em>) ≈ 1.09 lives — is{" "}
          <em>q</em> &gt; √<em>X</em>, especially <em>X</em>
          <sup>0.7</sup> &lt; <em>q</em> ≤ <em>X</em>. A large{" "}
          <em>q</em> | <em>m</em>
          <sub>0</sub>(<em>p</em>) means a prime <em>p</em> ≤ <em>X</em> in one
          of two progressions mod <em>q</em> (<em>p</em> ≡ ±1, class chosen by
          χ₃). For <em>q</em> &gt; <em>X</em>
          <sup>0.7</sup> that is one or two classes with modulus past the square
          root of the length — past Bombieri–Vinogradov. Elliott–Halberstam would
          buy mid-tail, not <em>q</em> ∼ <em>X</em>.
        </p>
        <aside className="lab-theorem" aria-label="Tail is the theorem">
          <p className="lab-theorem-implies">
            To prove H(X) ∼ C X log log X/(log X)² you must prove that
            &#123;q prime : X^θ &lt; q ≤ X, ∃ p ≤ X, q | m₀(p)&#125; has that
            order for some θ &gt; 1/2. Everything below √X is π(√X) and drops from
            the leading term.
          </p>
        </aside>
        <p>
          Chewable first slice — not “BV ⇒ baby <em>C</em>”: an upper bound of
          the right order. Each door has O(log <em>p</em>/log log <em>p</em>)
          distinct prime factors, so
        </p>
        <aside className="lab-theorem" aria-label="One log too fat">
          <p className="lab-theorem-implies">
            H(X) ≪ Σ<sub>p≤X</sub> ω(m₀(p)) ≪ π(X) log log X,
          </p>
        </aside>
        <p>
          which is one log too fat (<em>X</em> log log <em>X</em>/log <em>X</em>{" "}
          rather than <em>X</em> log log <em>X</em>/(log <em>X</em>)
          <sup>2</sup>). The missing log is “most factors are repeats of small{" "}
          <em>q</em>.” Turning that into a proof is exactly: small ones saturate,
          only the tail is new. The ~85% least-factor slot is the same sentence
          on a thinner vertex set.
        </p>
      </section>

      <section className="hire-beat">
        <h2>Signed door series</h2>
        <p>
          Partial sums through primes p &gt; 3 up to 10<sup>6</sup>. Red is the
          door twin Σ χ₃(p)/m₀(p); blue is Σ χ₃(p)/p on the same primes. Leave
          p = 2 out (m₀(2) = 1). Checkpoints for the door twin: already ≈ −0.239
          by 10<sup>3</sup>, then −0.241 and held through 10<sup>6</sup>. Blue
          sits near −0.142. Same sign pattern; the p ≡ 2 (mod 3) terms −1/(p − 1)
          outweigh +1/(p + 1), so red sits lower. Convergent-looking — not a slow
          log log, not a drunk walk. The limit is an unnamed Lab constant: not
          π/(3√3), not log L(1, χ₃). Those belong to other series.
        </p>
        <figure className="hire-lab-figure">
          <img
            src="/figures/hire/signed_door_series.png"
            alt="Partial sums of χ₃(p)/m₀(p) and χ₃(p)/p through primes from 5 to 10^6; both flatten, door twin near −0.241"
            width={960}
            height={540}
          />
          <figcaption className="figure-caption">
            Signed door series next to the <em>R</em>/<em>C</em> band — Lab only;
            no identity claimed for −0.241.
          </figcaption>
        </figure>
        <h3>Unsieved neighbours vs sluice</h3>
        <aside className="lab-theorem" aria-label="Door versus midpoint">
          <p className="lab-theorem-implies">
            1/m₀(p) − ½(1/(p − 1) + 1/(p + 1)) = −χ₃(p)/(p² − 1)
            for primes p &gt; 3.
          </p>
        </aside>
        <p>
          Checked Lean: <code>mid_gap_m0</code> in <code>Hire/Doors.lean</code>.
        </p>
        <p>
          Summing: D − mid = −Σ χ₃(p)/(p² − 1). Absolute convergence explains
          the early freeze. The constant ≈ 0.02598841679… is the value of that
          series — not a π/√3 form (wrong L-shape: primes, even powers). Also on{" "}
          <Link to="/cube-doors">Cube doors</Link> next to the peel. Three
          climbing curves through p &gt; 3 to 10<sup>6</sup> below: Σ 1/(p − 1),
          D(1) = Σ 1/m₀(p), Σ 1/(p + 1). Sluice nearer p − 1; signed −0.241 was
          cancellation, this is no cancellation plus a frozen offset.
        </p>
        <figure className="hire-lab-figure">
          <img
            src="/figures/hire/unsieved_neighbours_sluice.png"
            alt="Partial sums of 1/(p−1), 1/m₀(p), and 1/(p+1) through primes to 10^6, with midpoint dashed; sluice sits above the midpoint"
            width={960}
            height={540}
          />
          <figcaption className="figure-caption">
            Unsieved three-curve — frozen offset ≈ +0.026; same Lab folder as
            the signed pair.
          </figcaption>
        </figure>
        <h3>Why the sluice exists</h3>
        <p className="figure-caption">
          Why the sluice exists. Not an elliptic-curve method.
        </p>
        <p>
          For odd primes <em>p</em> ≠ 3, χ₃(<em>p</em>) = (−3/<em>p</em>).
          Williams’ <em>p</em>+1 test at discriminant <em>D</em> = −3 uses the
          torus order <em>p</em> − χ₃(<em>p</em>) = <em>m</em>
          <sub>1</sub>(<em>p</em>) — the neighbour we sack. The kept door{" "}
          <em>m</em>
          <sub>0</sub>(<em>p</em>) = <em>p</em> + χ₃(<em>p</em>) is the
          complementary order in ℚ(√−3). Split primes (<em>p</em> ≡ 1 mod 3)
          keep <em>p</em>+1; inert primes keep <em>p</em>−1. Same field as the
          Eisenstein integers and as the CM curve <em>y</em>² = <em>x</em>³ +{" "}
          <em>B</em>; different group. This explains the two doors — not gold
          connectivity, not hire-rate. One-screen:{" "}
          <Link to="/torus">Torus</Link>.
        </p>
      </section>

      <section className="hire-beat">
        <h2>Hiring frontier</h2>
        <p>
          Bin residual (tip <em>X</em>=2·10<sup>10</sup>): the ~1.4% excess lives
          at <em>u</em>=log <em>q</em>/log <em>X</em> in [0.8, 0.9) — the hiring
          frontier where λ=Li(<em>X</em>)/(<em>q</em>−1)∼1 (i.e.{" "}
          <em>q</em>∼<em>X</em>/log <em>X</em>). Those λ∼1 primes are hired a
          little more often than independent Dirichlet coins predict.
          Saturation (<em>u</em>≤0.7) shows residual ≈0; near <em>u</em>→1 the
          untruncated Poisson over-predicts. Keep naive <em>P</em>
          <sub>Pois</sub>; truncated Li fails.
        </p>
        <div className="door-table-wrap hire-rate-wrap">
          <table className="door-table hire-rate-table">
            <thead>
              <tr>
                <th>
                  <em>X</em>
                </th>
                <th>
                  <em>u</em>-bin
                </th>
                <th>
                  <em>H</em>
                  <sub>bin</sub>
                </th>
                <th>
                  <em>P</em>
                  <sub>bin</sub>
                </th>
                <th>residual</th>
                <th>rel</th>
              </tr>
            </thead>
            <tbody>
              <tr>
                <td>10<sup>10</sup></td>
                <td>[0.7, 0.8)</td>
                <td>5,093,359</td>
                <td>5,087,702</td>
                <td>+5,657</td>
                <td>+0.11%</td>
              </tr>
              <tr>
                <td>10<sup>10</sup></td>
                <td>[0.8, 0.9)</td>
                <td>28,844,630</td>
                <td>27,657,928</td>
                <td>+1,186,702</td>
                <td>+4.29%</td>
              </tr>
              <tr>
                <td>10<sup>10</sup></td>
                <td>[0.9, 1.0)</td>
                <td>30,236,418</td>
                <td>30,479,133</td>
                <td>−242,715</td>
                <td>−0.80%</td>
              </tr>
            </tbody>
          </table>
        </div>
        <p className="figure-caption">
          ≥95% of the positive residual at <em>X</em>≥10<sup>9</sup> sits in{" "}
          <em>u</em>∈[0.8, 0.9). <em>C</em> stays unnamed.
        </p>
      </section>

      <section className="hire-beat">
        <h2>Multiplicity</h2>
        <p>
          On the λ-frontier, count <em>N</em>
          <sub>q</sub> = #{"{"}owners that hire <em>q</em>{"}"}. Residual vs
          Poisson is <strong>under-dispersion of zeros</strong> (fewer{" "}
          <em>N</em>=0 than Poisson(μ)), not mean-bias μ&gt;λ. Shape{" "}
          <em>g</em>
          <sub>X</sub>(λ) collapses across <em>X</em> (cosine ≥0.94 for{" "}
          <em>X</em>≥10<sup>9</sup>).
        </p>
        <div className="door-table-wrap hire-rate-wrap">
          <table className="door-table hire-rate-table">
            <thead>
              <tr>
                <th>λ-band</th>
                <th>
                  <em>X</em>
                </th>
                <th>μ</th>
                <th>λ</th>
                <th>
                  <em>g</em>
                </th>
                <th>under</th>
              </tr>
            </thead>
            <tbody>
              <tr>
                <td>[1, 2)</td>
                <td>10<sup>10</sup></td>
                <td>1.298</td>
                <td>1.322</td>
                <td>+0.027</td>
                <td>+0.033</td>
              </tr>
              <tr>
                <td>[1, 2)</td>
                <td>2·10<sup>10</sup></td>
                <td>1.299</td>
                <td>1.321</td>
                <td>+0.026</td>
                <td>+0.032</td>
              </tr>
              <tr>
                <td>[2, 4)</td>
                <td>2·10<sup>10</sup></td>
                <td>—</td>
                <td>—</td>
                <td>under&gt;0</td>
                <td>bias≤0</td>
              </tr>
            </tbody>
          </table>
        </div>
      </section>

      <section className="hire-beat">
        <h2>
          <em>Q</em> · finite Bernoulli
        </h2>
        <p>
          Scale <em>Q</em>
          <sub>X</sub>(λ) = 2 e<sup>μ</sup> · under / (μ − Var). Leading
          Poisson-binomial identity wants <em>Q</em>→1; lab sits near 1 with a
          stable ~10% leftover at λ∼1.
        </p>
        <div className="door-table-wrap hire-rate-wrap">
          <table className="door-table hire-rate-table">
            <thead>
              <tr>
                <th>λ-bin</th>
                <th>
                  <em>Q</em>(10<sup>8</sup>)
                </th>
                <th>
                  <em>Q</em>(10<sup>10</sup>)
                </th>
                <th>
                  <em>Q</em>(2·10<sup>10</sup>)
                </th>
              </tr>
            </thead>
            <tbody>
              <tr>
                <td>[0.95, 1.13)</td>
                <td>1.151</td>
                <td>1.120</td>
                <td>1.117</td>
              </tr>
              <tr>
                <td>[1.13, 1.35)</td>
                <td>1.122</td>
                <td>1.111</td>
                <td>1.108</td>
              </tr>
              <tr>
                <td>[2.69, 3.20)</td>
                <td>1.055</td>
                <td>1.011</td>
                <td>1.002</td>
              </tr>
            </tbody>
          </table>
        </div>
        <p className="figure-caption">
          Cosine of the 12-bin <em>Q</em> vector vs tip <em>X</em> is ≥0.9998
          already at 10<sup>8</sup>. Shape locked; absolute values drift slowly
          toward 1.
        </p>
      </section>

      <section className="hire-beat">
        <h2>
          <em>T</em> / <em>Q</em>
          <sub>2nd</sub>
        </h2>
        <p>
          <em>T</em>
          <sub>X</sub>(λ) = (<em>Q</em>−1) log <em>X</em> — a scaling function,
          not a universal constant. Near λ∼1, <em>T</em>≈2.5–2.8 across decades;
          frontier-mean <em>T</em>≈1.7–1.9. Predictor{" "}
          <em>Q</em>
          <sub>2nd</sub> ≈ 1 + (2/3)(<em>S</em>
          <sub>3</sub>/<em>S</em>
          <sub>2</sub>) − <em>S</em>
          <sub>2</sub>/4 matches observed <em>Q</em> (frontier mean |Δ|≈0.011
          at tip).
        </p>
        <div className="door-table-wrap hire-rate-wrap">
          <table className="door-table hire-rate-table">
            <thead>
              <tr>
                <th>
                  <em>X</em>
                </th>
                <th>
                  mean <em>T</em> (λ∼1)
                </th>
                <th>
                  frontier mean <em>T</em>
                </th>
                <th>
                  cosine <em>T</em>
                </th>
              </tr>
            </thead>
            <tbody>
              <tr>
                <td>10<sup>8</sup></td>
                <td>2.52</td>
                <td>1.70</td>
                <td>0.953</td>
              </tr>
              <tr>
                <td>10<sup>9</sup></td>
                <td>2.83</td>
                <td>1.94</td>
                <td>0.997</td>
              </tr>
              <tr>
                <td>10<sup>10</sup></td>
                <td>2.78</td>
                <td>1.86</td>
                <td>0.997</td>
              </tr>
              <tr>
                <td>2·10<sup>10</sup></td>
                <td>2.78</td>
                <td>1.84</td>
                <td>1.000</td>
              </tr>
            </tbody>
          </table>
        </div>
        <p className="figure-caption">
          Sign fingerprint on every frontier bin: κ<sub>2</sub>&lt;0, κ
          <sub>3</sub>&gt;0, κ<sub>4</sub>&lt;0 — heterogeneous-Bernoulli, not
          equidispersed Poisson.
        </p>
      </section>

      <aside className="lab-note-caveats" aria-label="Lab freeze / caveats">
        <p>
          <strong>Lab freeze.</strong> <em>C</em> unnamed. Papers 1–2 frozen.
        </p>
      </aside>
    </main>
  );
}
