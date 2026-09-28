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
  { k: 142, eps: "+1", expr: "325606·2^n−141", factor: "Fermat composite", seconds: "89,852" },
  { k: 146, eps: "−1", expr: "334778·2^n−147", factor: "23", seconds: "0.28" },
  { k: 148, eps: "+1", expr: "339364·2^n−147", factor: "(none stored)", seconds: "0.27" },
  { k: 152, eps: "−1", expr: "348536·2^n−153", factor: "(none stored)", seconds: "0.28" },
  { k: 154, eps: "+1", expr: "353122·2^n−153", factor: "79", seconds: "0.32" },
  { k: 158, eps: "−1", expr: "362294·2^n−159", factor: "61", seconds: "0.32" },
  { k: 160, eps: "+1", expr: "366880·2^n−159", factor: "7", seconds: "0.27" },
  { k: 164, eps: "−1", expr: "376052·2^n−165", factor: "59", seconds: "0.27" },
  { k: 166, eps: "+1", expr: "380638·2^n−165", factor: "19", seconds: "0.28" },
  { k: 170, eps: "−1", expr: "389810·2^n−171", factor: "11", seconds: "0.27" },
  { k: 172, eps: "+1", expr: "394396·2^n−171", factor: "41", seconds: "0.28" },
  { k: 176, eps: "−1", expr: "403568·2^n−177", factor: "7", seconds: "0.28" },
  { k: 178, eps: "+1", expr: "408154·2^n−177", factor: "5", seconds: "0.28" },
  { k: 182, eps: "−1", expr: "417326·2^n−183", factor: "5", seconds: "0.28" },
  { k: 184, eps: "+1", expr: "421912·2^n−183", factor: "373", seconds: "0.28" },
  { k: 188, eps: "−1", expr: "431084·2^n−189", factor: "Fermat composite", seconds: "90,080" },
  { k: 190, eps: "+1", expr: "435670·2^n−189", factor: "13", seconds: "0.28" },
  { k: 194, eps: "−1", expr: "444842·2^n−195", factor: "293", seconds: "0.29" },
  { k: 196, eps: "+1", expr: "449428·2^n−195", factor: "17", seconds: "0.28" },
  { k: 200, eps: "−1", expr: "458600·2^n−201", factor: "13", seconds: "0.27" },
  { k: 202, eps: "+1", expr: "463186·2^n−201", factor: "7", seconds: "0.28" },
  { k: 206, eps: "−1", expr: "472358·2^n−207", factor: "Fermat composite", seconds: "87,633" },
  { k: 208, eps: "+1", expr: "476944·2^n−207", factor: "5", seconds: "0.32" },
  { k: 212, eps: "−1", expr: "486116·2^n−213", factor: "5", seconds: "0.31" },
  { k: 214, eps: "+1", expr: "490702·2^n−213", factor: "Fermat composite", seconds: "88,767" },
  { k: 218, eps: "−1", expr: "499874·2^n−219", factor: "7", seconds: "0.27" },
  { k: 220, eps: "+1", expr: "504460·2^n−219", factor: "18481", seconds: "0.55" },
  { k: 224, eps: "−1", expr: "513632·2^n−225", factor: "641", seconds: "0.31" },
  { k: 226, eps: "+1", expr: "518218·2^n−225", factor: "11", seconds: "0.33" },
  { k: 230, eps: "−1", expr: "527390·2^n−231", factor: "127891349", seconds: "970" },
];

export function Rank100Page() {
  return (
    <main className="page notes lab-note-page">
      <h1>Rank 100 floor</h1>
      <p className="lede">
        PrimePages rank 100 is the Riesel q = 2293·2<sup>12918431</sup>−1
        (3,888,839 digits). Thin sieve at B = 10<sup>7</sup> left K
        <sub>cert</sub> = 98: first un-killed admissible multiplier. PFGW has
        since killed every admissible k through 322. No owner. k = 326 is in
        PFGW — last B=10<sup>8</sup> survivor through 400.
      </p>
      <p>
        PFGW 4.1.8 on has-ams3-01, Intel Xeon Platinum 8280 @ 2.70 GHz, 8
        cores, 16 GB. n = 12,918,431. Admissible k are even and not divisible
        by 3. Skip multiples of 3. Snapshot 28 Sep 2026.
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
        because it stopped at the first survivor (k = 98). k = 142 was the
        second Fermat exam: 24.96 h (78,715 s PRP + 11,137 s other), composite,
        RES64 AC5D60C90B54F88D. Then 146–184 were 0.28 s jokes again. k = 148
        and 152 returned composite with no factor stored. k = 188 was the
        third Fermat exam: 25.02 h (79,056 s PRP + 11,024 s other), composite,
        RES64 85DDFCE797224332. Then 190–202 were 0.28 s again. k = 206 was the
        fourth Fermat exam: 24.34 h (76,647 s PRP + 10,986 s other), composite,
        RES64 A911EA4A4320C250. Then 208 and 212 died on 5. k = 214 was the
        fifth Fermat exam: 24.66 h (77,766 s PRP + 11,002 s other), composite,
        RES64 58D5F4C09BC76650. Then 218–226 were cheap kills (7, 18481, 641,
        11). k = 230 was a discount miss: factor 127891349 in 16 min (above
        B=10<sup>8</sup>, so not a Fermat). Then 232–322 were cheap kills
        again (296 took 124 s, factor 14146369). k = 326 is in PFGW at 13.5 h
        — last B=10<sup>8</sup> survivor through 400, past the trial-factor
        bound. Five Fermat exams, five composites. Density, not the test. A
        40-hour gmpy2 Fermat on the Studio was the k = 98 check without the
        trial-factor gate.
      </p>
      <p>
        No owner yet. Walker: <code>analysis/rank100_pfgw_floors.py</code>
        (Xeon, k = 326 in PFGW — do not mix). Discount sieve:{" "}
        <code>analysis/rank100_discount.py</code> — special-form trial factor
        of every admissible k without building N, so 0.28 s jokes die before
        FFT. Survivors at B are the Fermat queue. Timing:{" "}
        <code>analysis/lab-metrics.json</code>.
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
