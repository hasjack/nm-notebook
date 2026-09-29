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
  { k: 232, eps: "+1", expr: "531976·2^n−231", factor: "269", seconds: "0.28" },
  { k: 236, eps: "−1", expr: "541148·2^n−237", factor: "11", seconds: "0.27" },
  { k: 238, eps: "+1", expr: "545734·2^n−237", factor: "5", seconds: "0.28" },
  { k: 242, eps: "−1", expr: "554906·2^n−243", factor: "5", seconds: "0.28" },
  { k: 244, eps: "+1", expr: "559492·2^n−243", factor: "7", seconds: "0.28" },
  { k: 248, eps: "−1", expr: "568664·2^n−249", factor: "479", seconds: "0.28" },
  { k: 250, eps: "+1", expr: "573250·2^n−249", factor: "43", seconds: "0.28" },
  { k: 254, eps: "−1", expr: "582422·2^n−255", factor: "28433", seconds: "0.7" },
  { k: 256, eps: "+1", expr: "587008·2^n−255", factor: "32003", seconds: "0.74" },
  { k: 260, eps: "−1", expr: "596180·2^n−261", factor: "(none stored)", seconds: "0.28" },
  { k: 262, eps: "+1", expr: "600766·2^n−261", factor: "105499", seconds: "1.57" },
  { k: 266, eps: "−1", expr: "609938·2^n−267", factor: "43", seconds: "0.27" },
  { k: 268, eps: "+1", expr: "614524·2^n−267", factor: "5", seconds: "0.28" },
  { k: 272, eps: "−1", expr: "623696·2^n−273", factor: "5", seconds: "0.27" },
  { k: 274, eps: "+1", expr: "628282·2^n−273", factor: "67", seconds: "0.28" },
  { k: 278, eps: "−1", expr: "637454·2^n−279", factor: "13", seconds: "0.27" },
  { k: 280, eps: "+1", expr: "642040·2^n−279", factor: "19", seconds: "0.27" },
  { k: 284, eps: "−1", expr: "651212·2^n−285", factor: "23", seconds: "0.28" },
  { k: 286, eps: "+1", expr: "655798·2^n−285", factor: "7", seconds: "0.27" },
  { k: 290, eps: "−1", expr: "664970·2^n−291", factor: "19", seconds: "0.27" },
  { k: 292, eps: "+1", expr: "669556·2^n−291", factor: "11", seconds: "0.27" },
  { k: 296, eps: "−1", expr: "678728·2^n−297", factor: "14146369", seconds: "124" },
  { k: 298, eps: "+1", expr: "683314·2^n−297", factor: "(none stored)", seconds: "0.27" },
  { k: 302, eps: "−1", expr: "692486·2^n−303", factor: "(none stored)", seconds: "0.27" },
  { k: 304, eps: "+1", expr: "697072·2^n−303", factor: "37", seconds: "0.27" },
  { k: 308, eps: "−1", expr: "706244·2^n−309", factor: "2437", seconds: "0.3" },
  { k: 310, eps: "+1", expr: "710830·2^n−309", factor: "3083", seconds: "0.33" },
  { k: 314, eps: "−1", expr: "720002·2^n−315", factor: "17", seconds: "0.27" },
  { k: 316, eps: "+1", expr: "724588·2^n−315", factor: "2161", seconds: "0.31" },
  { k: 320, eps: "−1", expr: "733760·2^n−321", factor: "31", seconds: "0.27" },
  { k: 322, eps: "+1", expr: "738346·2^n−321", factor: "4723", seconds: "0.34" },
  { k: 326, eps: "−1", expr: "747518·2^n−327", factor: "Fermat composite", seconds: "89,468" },
  { k: 328, eps: "+1", expr: "752104·2^n−327", factor: "5", seconds: "0.27" },
  { k: 332, eps: "−1", expr: "761276·2^n−333", factor: "5", seconds: "0.27" },
  { k: 334, eps: "+1", expr: "765862·2^n−333", factor: "103", seconds: "0.32" },
  { k: 338, eps: "−1", expr: "775034·2^n−339", factor: "53", seconds: "0.32" },
  { k: 340, eps: "+1", expr: "779620·2^n−339", factor: "643", seconds: "0.28" },
  { k: 344, eps: "−1", expr: "788792·2^n−345", factor: "7", seconds: "0.27" },
  { k: 346, eps: "+1", expr: "793378·2^n−345", factor: "13", seconds: "0.27" },
  { k: 350, eps: "−1", expr: "802550·2^n−351", factor: "83", seconds: "0.27" },
  { k: 352, eps: "+1", expr: "807136·2^n−351", factor: "251", seconds: "0.28" },
  { k: 356, eps: "−1", expr: "816308·2^n−357", factor: "13", seconds: "0.27" },
  { k: 358, eps: "+1", expr: "820894·2^n−357", factor: "5", seconds: "0.27" },
  { k: 362, eps: "−1", expr: "830066·2^n−363", factor: "5", seconds: "0.27" },
  { k: 364, eps: "+1", expr: "834652·2^n−363", factor: "8101", seconds: "0.4" },
  { k: 368, eps: "−1", expr: "843824·2^n−369", factor: "11", seconds: "0.28" },
  { k: 370, eps: "+1", expr: "848410·2^n−369", factor: "7", seconds: "0.35" },
  { k: 374, eps: "−1", expr: "857582·2^n−375", factor: "1373", seconds: "0.4" },
  { k: 376, eps: "+1", expr: "862168·2^n−375", factor: "941", seconds: "0.39" },
  { k: 380, eps: "−1", expr: "871340·2^n−381", factor: "337", seconds: "0.38" },
  { k: 382, eps: "+1", expr: "875926·2^n−381", factor: "5081", seconds: "0.44" },
  { k: 386, eps: "−1", expr: "885098·2^n−387", factor: "7", seconds: "0.33" },
  { k: 388, eps: "+1", expr: "889684·2^n−387", factor: "5", seconds: "0.38" },
  { k: 392, eps: "−1", expr: "898856·2^n−393", factor: "5", seconds: "0.35" },
  { k: 394, eps: "+1", expr: "903442·2^n−393", factor: "19", seconds: "0.34" },
  { k: 398, eps: "−1", expr: "912614·2^n−399", factor: "30773", seconds: "0.79" },
  { k: 400, eps: "+1", expr: "917200·2^n−399", factor: "17", seconds: "0.31" },
  { k: 404, eps: "−1", expr: "926372·2^n−405", factor: "19", seconds: "0.3" },
  { k: 406, eps: "+1", expr: "930958·2^n−405", factor: "23", seconds: "0.28" },
  { k: 410, eps: "−1", expr: "940130·2^n−411", factor: "6397", seconds: "0.37" },
  { k: 412, eps: "+1", expr: "944716·2^n−411", factor: "7", seconds: "0.27" },
  { k: 416, eps: "−1", expr: "953888·2^n−417", factor: "17", seconds: "0.27" },
  { k: 418, eps: "+1", expr: "958474·2^n−417", factor: "5", seconds: "0.26" },
  { k: 422, eps: "−1", expr: "967646·2^n−423", factor: "5", seconds: "0.26" },
  { k: 424, eps: "+1", expr: "972232·2^n−423", factor: "11", seconds: "0.27" },
  { k: 428, eps: "−1", expr: "981404·2^n−429", factor: "7", seconds: "0.27" },
  { k: 430, eps: "+1", expr: "985990·2^n−429", factor: "47", seconds: "0.27" },
  { k: 434, eps: "−1", expr: "995162·2^n−435", factor: "11", seconds: "0.26" },
  { k: 436, eps: "+1", expr: "999748·2^n−435", factor: "2969", seconds: "0.32" },
  { k: 440, eps: "−1", expr: "1008920·2^n−441", factor: "457", seconds: "0.28" },
];

export function Rank100Page() {
  return (
    <main className="page notes lab-note-page">
      <h1>Rank 100 floor</h1>
      <p className="lede">
        PrimePages rank 100 is the Riesel q = 2293·2<sup>12918431</sup>−1
        (3,888,839 digits). Thin sieve at B = 10<sup>7</sup> left K
        <sub>cert</sub> = 98: first un-killed admissible multiplier. PFGW has
        since killed every admissible k through 440. No owner. k = 442 is in
        PFGW now.
      </p>
      <p>
        PFGW 4.1.8 on has-ams3-01, Intel Xeon Platinum 8280 @ 2.70 GHz, 8
        cores, 16 GB. n = 12,918,431. Admissible k are even and not divisible
        by 3. Skip multiples of 3. Snapshot 29 Sep 2026.
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
        again (296 took 124 s, factor 14146369). k = 326 was the sixth Fermat
        exam: 24.85 h, composite. Then 328–440 were cheap kills again. k = 442
        is in PFGW now — next survivor past the trial-factor bound. Six Fermat
        exams, six composites. Density, not the test. A
        40-hour gmpy2 Fermat on the Studio was the k = 98 check without the
        trial-factor gate.
      </p>
      <p>
        No owner yet. Walker: <code>analysis/rank100_pfgw_floors.py</code>
        (Xeon, k = 442 in PFGW — do not mix). Discount sieve:{" "}
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
