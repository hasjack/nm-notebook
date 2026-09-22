import { Link } from "react-router-dom";

export function ZetaDoorsPage() {
  return (
    <main className="page notes">
      <h1>Zeta doors</h1>
      <p className="lede">
        Even index k ≡ 2 (mod 12). The Bernoulli / zeta(1−k) denominator D is
        3-free after dropping its one factor of 3. The legal neighbour of d = D/3
        is a 3-free door. When that neighbour is Q = d+1, Q−1 is completely
        factored and Pocklington applies.
      </p>
      <p>
        Kitchen record: <strong>5,522 digits</strong>, certified. Zeta input
        −111695474196999960960049. Farm Boolean length is 3,361 digits (q = 31).
      </p>
      <p>
        Hunt first, prove later. Search logs PRP hits;{" "}
        <code>cert.py</code> builds the n−1 certificate;{" "}
        <code>verify.py</code> rebuilds the denominator. Code:{" "}
        <code>analysis/zeta/zeta-targeted/</code>.
      </p>
      <p className="home-actions">
        <Link className="nav-link" to="/certificates">
          Certificates
        </Link>
        <Link className="nav-link" to="/hire">
          Introduction
        </Link>
      </p>
    </main>
  );
}
