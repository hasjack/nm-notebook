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
        <h2>Leading counts</h2>
        <p>
          Odd hires through window <em>X</em>: <em>H</em>(<em>X</em>)=|
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
          <sub>Pois</sub>−1)(log <em>X</em>)<sup>2</sup>. Lab only — not a
          theorem.
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
          Open notebook — lab counts only, not a theorem.
        </p>
      </aside>
    </main>
  );
}
