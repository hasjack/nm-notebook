import { Link } from "react-router-dom";

export function Rank100Page() {
  return (
    <main className="page notes lab-note-page">
      <h1>Rank 100 floor</h1>
      <p className="lede">
        PrimePages rank 100 is the Riesel q = 2293·2<sup>12918431</sup>−1
        (3,888,839 digits). Thin sieve at B = 10<sup>7</sup> left K
        <sub>cert</sub> = 98: first un-killed admissible multiplier. That
        candidate is N = 98q−1 = 224714·2<sup>12918431</sup>−99.
      </p>
      <p>
        PFGW 4.1.8 on an x86 Xeon, 22 Sep 2026, trial factoring to ~1.66×10
        <sup>9</sup>:
      </p>
      <p>
        <code>224714*2^12918431-99 has factors: 162981019</code>
      </p>
      <p>
        162981019 is prime, nine digits, larger than B, so the thin sieve never
        saw it. N ≡ 0 (mod 162981019). Wall clock 21 minutes. The FFT PRP never
        started. A 40-hour gmpy2 Fermat on the Studio was the same check without
        the trial-factor gate.
      </p>
      <p>
        k = 98 is composite. Next admissible k = 100 (ε = +1), then 104, 106,
        skip multiples of 3. Walker:{" "}
        <code>analysis/rank100_pfgw_floors.py</code>.
      </p>
      <p className="home-actions">
        <Link className="nav-link" to="/certificates">
          Certificates
        </Link>
        <Link className="nav-link" to="/zeta-doors">
          Zeta doors
        </Link>
      </p>
    </main>
  );
}
