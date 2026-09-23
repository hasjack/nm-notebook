import { Link } from "react-router-dom";

const FLOORS: {
  k: number;
  eps: string;
  expr: string;
  factor: string;
  seconds: string;
}[] = [
  { k: 98, eps: "−1", expr: "224714·2^n−99", factor: "162981019", seconds: "21 min" },
  { k: 100, eps: "+1", expr: "229300·2^n−99", factor: "393061223", seconds: "2,896" },
  { k: 104, eps: "−1", expr: "238472·2^n−105", factor: "(none stored)", seconds: "0.28" },
  { k: 106, eps: "+1", expr: "243058·2^n−105", factor: "212669", seconds: "2.96" },
  { k: 110, eps: "−1", expr: "252230·2^n−111", factor: "17", seconds: "0.31" },
  { k: 112, eps: "+1", expr: "256816·2^n−111", factor: "13", seconds: "0.27" },
  { k: 116, eps: "−1", expr: "265988·2^n−117", factor: "43242769", seconds: "360" },
  { k: 118, eps: "+1", expr: "270574·2^n−117", factor: "5", seconds: "0.27" },
  { k: 122, eps: "−1", expr: "279746·2^n−123", factor: "5", seconds: "0.27" },
  { k: 124, eps: "+1", expr: "284332·2^n−123", factor: "Fermat composite", seconds: "92,474" },
  { k: 128, eps: "−1", expr: "293504·2^n−129", factor: "67", seconds: "0.28" },
  { k: 130, eps: "+1", expr: "298090·2^n−129", factor: "23", seconds: "0.28" },
  { k: 134, eps: "−1", expr: "307262·2^n−135", factor: "7", seconds: "0.28" },
  { k: 136, eps: "+1", expr: "311848·2^n−135", factor: "439", seconds: "0.29" },
  { k: 140, eps: "−1", expr: "321020·2^n−141", factor: "37", seconds: "0.29" },
];

export function Rank100Page() {
  return (
    <main className="page notes lab-note-page">
      <h1>Rank 100 floor</h1>
      <p className="lede">
        PrimePages rank 100 is the Riesel q = 2293·2<sup>12918431</sup>−1
        (3,888,839 digits). Thin sieve at B = 10<sup>7</sup> left K
        <sub>cert</sub> = 98: first un-killed admissible multiplier. PFGW has
        since killed every admissible k through 140. No owner.
      </p>
      <p>
        PFGW 4.1.8 on has-ams3-01, Intel Xeon Platinum 8280 @ 2.70 GHz, 8
        cores, 16 GB. n = 12,918,431. Admissible k are even and not divisible
        by 3. Skip 102, 108, 114, 120, 126, 132, 138. Snapshot 23 Sep 2026.
      </p>
      <div className="door-table-wrap">
        <table className="door-table">
          <thead>
            <tr>
              <th>k</th>
              <th>ε</th>
              <th>N</th>
              <th>factor</th>
              <th>time</th>
            </tr>
          </thead>
          <tbody>
            {FLOORS.map((row) => (
              <tr key={row.k}>
                <td>{row.k}</td>
                <td>{row.eps}</td>
                <td>
                  <code>{row.expr}</code>
                </td>
                <td>{row.factor}</td>
                <td>{row.seconds}</td>
              </tr>
            ))}
          </tbody>
        </table>
      </div>
      <p>
        k = 98 took 21 minutes to a nine-digit factor larger than B, so the
        thin sieve never saw it. k = 100 took 48 minutes (factor 393061223).
        Several later k die in a fraction of a second on a tiny prime. k = 104
        returned composite in 0.28 s with no factor stored in the walker JSON.
        k = 124 was the first to survive trial factoring to 1.66×10
        <sup>9</sup>. A full Fermat PRP then ran 25.7 h (81,312 s PRP + 11,162
        s other) and returned composite, RES64 C639D96377D4F918. The walker
        first logged that as unknown: it did not parse <code>is composite</code>.
        k = 128–140 died in 0.28 s on tiny primes the thin sieve never saw,
        because it stopped at the first survivor (k = 98). Next admissible is
        142. A 40-hour gmpy2 Fermat on the Studio was the k = 98 check without
        the trial-factor gate.
      </p>
      <p>
        No owner yet. Walker: <code>analysis/rank100_pfgw_floors.py</code>.
        Timing: <code>analysis/lab-metrics.json</code>.
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
