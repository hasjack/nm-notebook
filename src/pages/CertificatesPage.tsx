import { Link } from "react-router-dom";
import { TOP100 } from "../lib/top100Certificates";

/** Lean Hire modular certificates for record sink q = M_136279841. */
type ReceiptRow = {
  k: number;
  eps: "−1" | "+1";
  r: string;
  hireOfR: string;
  terminals: string;
};

const RECEIPT: ReceiptRow[] = [
  { k: 2, eps: "−1", r: "375373", hireOfR: "187687", terminals: "{5,7}" },
  { k: 4, eps: "+1", r: "5", hireOfR: "∅", terminals: "{5}" },
  { k: 8, eps: "−1", r: "13", hireOfR: "7", terminals: "{7}" },
  { k: 10, eps: "+1", r: "11", hireOfR: "5", terminals: "{5}" },
  { k: 14, eps: "−1", r: "1181", hireOfR: "5, 59", terminals: "{5,7}" },
  { k: 16, eps: "+1", r: "7", hireOfR: "∅", terminals: "{7}" },
  { k: 20, eps: "−1", r: "79", hireOfR: "5", terminals: "{5}" },
  { k: 22, eps: "+1", r: "103", hireOfR: "13", terminals: "{7}" },
  { k: 26, eps: "−1", r: "5", hireOfR: "∅", terminals: "{5}" },
];

const M31_FIRST_OWNER = "98,784,247,763";

export function CertificatesPage() {
  return (
    <main className="page lab-note-page certificates-page certs-page">
      <h1>Certificates</h1>
      <p className="lede">
        Thin-sieve owner floors at B = 10<sup>7</sup> for the PrimePages top 100.
        Record Mersenne receipt, then the catalog. #82 (primorial) skipped.
      </p>

      <section className="hire-beat lab-note-hierarchy">
        <h2>What an owner-floor certificate is</h2>
        <ul className="lab-note-hierarchy-list">
          <li>
            For each killed admissible <em>k</em> &lt; <em>K</em>: store (
            <em>k</em>, ε, <em>r</em>) with <em>r</em> | <em>k</em>
            <em>q</em>+ε.
          </li>
          <li>
            Admissible: because <em>q</em> ≡ 1 (mod 3), candidates are 2
            <em>q</em>−1, 4<em>q</em>+1, … (ε = ±1 with the usual 3-free door
            parity).
          </li>
          <li>
            Verifier: compute 2<sup>
              <em>p</em>
            </sup>{" "}
            mod <em>r</em> only — never write <em>q</em>.
          </li>
          <li>
            <strong>
              K<sub>cert</sub>(q;B)
            </strong>{" "}
            is the first admissible multiplier not certified composite using
            factors ≤ B.{" "}
            <strong>
              K<sub>hire</sub>(q)
            </strong>{" "}
            = m<sub>0</sub>(τ(<em>q</em>))/<em>q</em> is the true first-owner
            multiplier. The receipt proves K<sub>hire</sub>(q) ≥ K
            <sub>cert</sub>(q;B).
          </li>
        </ul>
      </section>

      <section className="hire-beat">
        <h2>
          Receipt — M<sub>136279841</sub>
        </h2>
        <p>
          Nine modular certificates for admissible <em>k</em> &lt; 28. K
          <sub>cert</sub>(M<sub>136279841</sub>; 10<sup>7</sup>) = 28, so K
          <sub>hire</sub> ≥ 28 for this q.
        </p>
        <div className="door-table-wrap hire-rate-wrap certs-receipt-wrap">
          <table className="door-table hire-rate-table certs-receipt">
            <thead>
              <tr>
                <th>
                  <em>k</em>
                </th>
                <th>ε</th>
                <th>
                  <em>r</em>
                </th>
                <th>
                  hire of <em>r</em>
                </th>
                <th>terminals</th>
              </tr>
            </thead>
            <tbody>
              {RECEIPT.map((row) => (
                <tr key={row.k}>
                  <td>{row.k}</td>
                  <td>{row.eps}</td>
                  <td>{row.r}</td>
                  <td>{row.hireOfR}</td>
                  <td>{row.terminals}</td>
                </tr>
              ))}
            </tbody>
          </table>
        </div>
        <p className="figure-caption islands-caption">
          All nine check: <em>k</em>(2<sup>e</sup>−1)+ε ≡ 0 (mod <em>r</em>).
          Gold-basin labels land in {"{"}5{"}"}, {"{"}7{"}"}, or {"{"}5,7{"}"}.
          Same K<sub>cert</sub> at B = 10<sup>8</sup>.
        </p>
      </section>

      <section className="hire-beat">
        <h2>
          PrimePages top 100 — K<sub>cert</sub>(q; 10<sup>7</sup>)
        </h2>
        <p>
          Same sieve, ranked by size. Compression = digits / max(1, kills).
          Highest K<sub>cert</sub>: rank 42 = 134, rank 75 = 116, rank 18 = 110.
        </p>
        <div className="door-table-wrap hire-rate-wrap certs-receipt-wrap certs-catalog-wrap">
          <table className="door-table hire-rate-table certs-receipt certs-catalog">
            <thead>
              <tr>
                <th>rank</th>
                <th>form</th>
                <th>digits</th>
                <th>
                  K<sub>cert</sub>
                </th>
                <th>kills</th>
                <th>compression</th>
              </tr>
            </thead>
            <tbody>
              {TOP100.map((row) => (
                <tr key={row.rank} className={row.skipped ? "certs-skipped" : undefined}>
                  <td>{row.rank}</td>
                  <td>{row.form}</td>
                  <td>{row.digits}</td>
                  <td>{row.kCert ?? "skipped"}</td>
                  <td>{row.kills ?? "—"}</td>
                  <td>{row.compression}</td>
                </tr>
              ))}
            </tbody>
          </table>
        </div>
      </section>

      <section className="hire-beat">
        <h2>
          Sanity — M<sub>31</sub>
        </h2>
        <p>
          Same procedure stops at <em>k</em> = 46 → 46·M<sub>31</sub>+1 ={" "}
          {M31_FIRST_OWNER}, the known first owner.
        </p>
      </section>

      <aside className="lab-note-caveats" aria-label="Lab freeze / caveats">
        <p>
          <strong>Lab freeze.</strong> Papers frozen. Catalog frozen at B = 10
          <sup>7</sup>. A certificate is a lower bound on K<sub>hire</sub>, not
          a first owner. Rank 100, k = 98, is now composite (factor 162981019);
          see <Link to="/rank100">Rank 100 floor</Link>.
        </p>
      </aside>
    </main>
  );
}
