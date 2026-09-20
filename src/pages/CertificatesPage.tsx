import { Link } from "react-router-dom";

/** Lean Hire modular certificates for record sink q = M_136279841. Do not invent. */
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
        Owner-floor certificates for Mersenne sinks (and any odd prime{" "}
        <em>q</em>). Small witnesses replace a huge graph chase. Demo: record M
        <sub>136279841</sub>. Lifecycle seating is on{" "}
        <Link to="/microscope">Microscope</Link>; lab freeze counts on{" "}
        <Link to="/hire-lab">Hire rate</Link>. Papers frozen.
      </p>

      <p className="islands-bernard">
        For the record, K<sub>hire</sub>(q) ≥ 28. With sieve bound B, K
        <sub>cert</sub>(q;B) = 28 for B = 10<sup>7</sup> and 10<sup>8</sup> —
        not an intrinsic constant. M<sub>31</sub> sanity met at 46.
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
            Distinguish <strong>
              K<sub>cert</sub>(q;B)
            </strong>{" "}
            — first admissible multiplier not certified composite using factors
            ≤ B; depends on B, not intrinsic — from{" "}
            <strong>
              K<sub>hire</sub>(q)
            </strong>{" "}
            = m<sub>0</sub>(τ(<em>q</em>))/<em>q</em>, which is intrinsic. The
            receipt proves only K<sub>hire</sub>(q) ≥ K<sub>cert</sub>(q;B).
          </li>
        </ul>
      </section>

      <section className="hire-beat">
        <h2>
          Receipt table — record M<sub>136279841</sub>
        </h2>
        <p>
          Lean Hire numbers. Nine modular certificates for admissible{" "}
          <em>k</em> &lt; 28.
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
          All nine modular certificates check:{" "}
          <em>k</em>(2<sup>
            <em>e</em>
          </sup>
          −1)+ε ≡ 0 (mod <em>r</em>). Every gold-basin label lands in {"{"}5
          {"}"}, {"{"}7{"}"}, or {"{"}5,7{"}"} — ambient small-prime geography,
          not a link to the exponent shadow {"{"}131, 3407, 851749{"}"}. Those
          limbs never appear as killers. K<sub>cert</sub>(q;10
          <sup>7</sup>) = K<sub>cert</sub>(q;10<sup>8</sup>) = 28; the
          certificate says K<sub>hire</sub>(q) ≥ 28. No forced climb past 28
          without a better kill on 28<em>q</em>+1.
        </p>
      </section>

      <section className="hire-beat">
        <h2>
          Sanity — M<sub>31</sub>
        </h2>
        <p>
          Same procedure stops at <em>k</em> = 46 → 46·M<sub>31</sub>+1 ={" "}
          {M31_FIRST_OWNER}, the known first owner (so with enough B, K
          <sub>cert</sub> met K<sub>hire</sub> = 46 there).
        </p>
      </section>

      <section className="hire-beat">
        <h2>Plateau note</h2>
        <p>
          28<em>q</em>+1 has no factor ≤ 5·10<sup>9</sup>; crude conditional
          primality ~4×10<sup>−7</sup> — do not treat the plateau as evidence 28
          <em>q</em>+1 is prime. Certificate already did its job (2 → 28).
        </p>
      </section>

      <aside className="lab-note-caveats" aria-label="Lab freeze / caveats">
        <p>
          <strong>Lab freeze.</strong> <em>C</em> unnamed. Papers frozen. Open
          notebook. Claim is only K<sub>hire</sub>(q) ≥ 28 for the record —
          not that K<sub>cert</sub>(q;B) = K<sub>hire</sub>(q), and not that 28
          <em>q</em>+1 is prime.
        </p>
        <p>
          Owner hunt closed: finding τ(q) is not a GIMPS Lucas–Lehmer job.
          Heuristic K ∼ log q ≈ 9·10<sup>7</sup>; after a serious sieve, ~10
          <sup>6</sup> survivors remain. Each is a structured 41M-digit test
          (Pocklington/Lucas is kinder because N∓1 = kq already knows a factor
          &gt; √N) — still a world-scale GPU project, not a Mac run. The
          certificate microscope stays; chasing the owner does not.
        </p>
      </aside>
    </main>
  );
}
