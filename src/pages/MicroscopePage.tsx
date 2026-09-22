import { Link } from "react-router-dom";

/** Record Mersenne sink — UP owners / Q hub / DOWN shadow. Papers frozen. */
const EXP = "136279841";
const DIGITS_Q = "41,024,320";
const DIGITS_Q_RAW = "41024320";
const LOG_Q = "94,461,987.56"; // ln q = e ln 2
const LINNIK_DIGITS = "212,500,000";
const SPARSITY = "1.94×10⁻⁷"; // H(Q)/π(Q) ∼ loglog Q / log Q

type LifeRow = {
  label: string;
  digits: string;
  note: string;
  mark?: boolean;
};

const LIFE: LifeRow[] = [
  {
    label: "q itself",
    digits: DIGITS_Q,
    note: "Mersenne record sink",
  },
  {
    label: "rigorous floor τ(q) ≥ 2q − 1",
    digits: "41,024,321",
    note: "K = 2",
  },
  {
    label: "Hire heuristic 50%",
    digits: "41,024,328",
    note: "K ∼ 6.55·10⁷",
    mark: true,
  },
  {
    label: "Hire characteristic",
    digits: "41,024,328",
    note: "K ∼ 9.45·10⁷",
  },
  {
    label: "Hire heuristic 90%",
    digits: "41,024,329",
    note: "K ∼ 2.18·10⁸",
  },
  {
    label: "Hire heuristic 99%",
    digits: "41,024,329",
    note: "K ∼ 4.35·10⁸",
  },
  {
    label: "direct bridge owner v₅₀",
    digits: "41,024,329",
    note: "first-owner scale for a direct 5–q bridge",
  },
  {
    label: "direct bridge likely live τ(v)",
    digits: "41,024,337",
    note: "when that bridge’s ticket finally sits — mixed routes can connect earlier",
  },
];

/** Digit-rail ticks — labeled by digit count / K, not absolute X. */
const RAIL: {
  id: string;
  label: string;
  digits: number;
  blurb: string;
  mark?: boolean;
}[] = [
  { id: "q", label: "q", digits: 41_024_320, blurb: "record sink" },
  {
    id: "floor",
    label: "K=2",
    digits: 41_024_321,
    blurb: "elementary floor",
  },
  {
    id: "hire50",
    label: "Hire 50%",
    digits: 41_024_328,
    blurb: "K ∼ 6.55·10⁷ — first owner expected",
    mark: true,
  },
  {
    id: "v50",
    label: "v₅₀",
    digits: 41_024_329,
    blurb: "direct bridge owner",
  },
  {
    id: "tv",
    label: "τ(v)",
    digits: 41_024_337,
    blurb: "direct bridge live",
  },
];

type KillRow = { k: number; r: string; inShadow: boolean };

/** Lean Hire kill-primes for k < 28 vs exponent-shadow set. */
const FALSIFIER: KillRow[] = [
  { k: 2, r: "375373", inShadow: false },
  { k: 4, r: "5", inShadow: true },
  { k: 8, r: "13", inShadow: true },
  { k: 10, r: "11", inShadow: false },
  { k: 14, r: "1181", inShadow: false },
  { k: 16, r: "7", inShadow: true },
  { k: 20, r: "79", inShadow: false },
  { k: 22, r: "103", inShadow: false },
  { k: 26, r: "5", inShadow: true },
];

function fmtDigits(n: number): string {
  return n.toLocaleString("en-US");
}

export function MicroscopePage() {
  const lo = RAIL[0].digits;
  const hi = RAIL[RAIL.length - 1].digits;
  const span = Math.max(hi - lo, 1);

  return (
    <main className="page microscope-page lab-note-page">
      <h1>Microscope</h1>
      <p className="lede">
        A {DIGITS_Q}-digit Mersenne sink is predicted to acquire its first owner
        only about <strong>8–9 decimal digits</strong> of scale later. Layout:{" "}
        <strong>UP</strong> owners · <strong>Q</strong> hub · <strong>DOWN</strong>{" "}
        shadow. Related: <Link to="/islands">Islands</Link> /{" "}
        <Link to="/corridor">Corridor</Link> — siblings, not parents. Lab only;
        no breakthrough claim.
      </p>

      <p className="islands-bernard">
        τ(q) ∼ q log q. Linnik envelope ~{LINNIK_DIGITS} digits. Hire
        expectation sits at ~41,024,328 digits: an eight-digit jump past q
        itself.
      </p>

      {/* ── UP · owners ─────────────────────────────────────────── */}
      <section
        className="microscope-zone microscope-up"
        aria-label="UP · owners"
      >
        <header className="microscope-zone-head">
          <span className="microscope-zone-tag">UP · owners</span>
          <span className="microscope-zone-arrow" aria-hidden="true">
            ↑
          </span>
        </header>

        <div className="islands-panel corridor-panel microscope-panel">
          <div
            className="islands-corridor microscope-rail"
            aria-label="Record sink digit rail"
          >
            <div className="islands-corridor-head">
              <span className="islands-corridor-title">
                M<sub>{EXP}</sub> · digit rail
              </span>
              <span className="islands-corridor-note">
                labeled by digit count / K — not absolute X
              </span>
            </div>
            <div className="islands-corridor-rail" role="list">
              {RAIL.map((tick) => {
                const pct = ((tick.digits - lo) / span) * 100;
                return (
                  <div
                    key={tick.id}
                    role="listitem"
                    className={
                      tick.mark
                        ? "islands-corridor-tick mark"
                        : "islands-corridor-tick"
                    }
                    style={{ left: `${pct}%` }}
                    title={`${tick.label} · ${fmtDigits(tick.digits)} digits — ${tick.blurb}`}
                  >
                    <span className="islands-corridor-dot" />
                    <span className="islands-corridor-label">{tick.label}</span>
                    <span className="islands-corridor-val">
                      {fmtDigits(tick.digits)}
                    </span>
                  </div>
                );
              })}
              <div className="islands-corridor-line" aria-hidden="true" />
            </div>
            <p className="islands-corridor-caption">
              Linear in digit count from q to direct-bridge τ(v). Hire 50% lands
              only eight digits past q. Mixed routes can connect earlier than the
              direct-bridge scale — do not oversell 41,024,337.
            </p>
          </div>
        </div>

        <div className="hire-beat">
          <h2>Lifecycle · digits scale</h2>
          <p>
            First-owner multiplier K with τ(q) ≈ Kq. Heuristic bands from Jack’s
            table; digit counts are the story, not huge Number values.
          </p>
          <div className="door-table-wrap hire-rate-wrap microscope-life-wrap">
            <table className="door-table hire-rate-table microscope-life-table">
              <thead>
                <tr>
                  <th>Stage</th>
                  <th>Digits</th>
                  <th>Note</th>
                </tr>
              </thead>
              <tbody>
                {LIFE.map((row) => (
                  <tr
                    key={row.label}
                    className={row.mark ? "microscope-mark" : undefined}
                  >
                    <td>{row.label}</td>
                    <td>{row.digits}</td>
                    <td className="microscope-note">{row.note}</td>
                  </tr>
                ))}
              </tbody>
            </table>
          </div>
          <p className="islands-lab-caption">
            Mixed routes can connect earlier than the direct-bridge scale — don’t
            oversell 41,024,337 as the first join. Bridge live scale is a
            mixed-route caveat, not a guaranteed first seating.
          </p>
        </div>

        <div className="hire-beat microscope-certified">
          <h2>Certified-K receipt</h2>
          <div
            className="microscope-cert-slot microscope-cert-filled"
            aria-label="Thin-sieve certified floor on K"
          >
            <p className="microscope-cert-lead">
              Thin-sieve certified floor —{" "}
              <strong>
                K_cert=28
              </strong>
            </p>
            <dl className="microscope-cert-readout">
              <div>
                <dt>K<sub>cert</sub></dt>
                <dd data-slot="k-floor">28</dd>
              </div>
              <div>
                <dt>R</dt>
                <dd data-slot="R">10⁷ (same at 10⁸)</dd>
              </div>
              <div>
                <dt>Wall</dt>
                <dd data-slot="wall-time">≈1.2 s / ≈10.7 s</dd>
              </div>
              <div>
                <dt>Climb</dt>
                <dd data-slot="climb">2 → 28</dd>
              </div>
            </dl>
            <ul className="microscope-cert-bullets">
              <li>
                Plateau: 28q+1 has no prime factor ≤ 5·10⁹ — thin sieve stalls
                there; not a τ hunt.
              </li>
              <li>
                M₃₁ sanity: K<sub>cert</sub> = 46 at R = 10⁵ (matches known first
                owner).
              </li>
            </ul>
            <p className="figure-caption islands-caption islands-cold-body">
              Lower bound only. Survivors may still be composite. No ζ; open
              notebook.
            </p>
            <p className="figure-caption islands-caption">
              Owner-floor receipt → <Link to="/certificates">Certificates</Link>.
            </p>
          </div>
        </div>

        <div className="hire-beat microscope-linnik">
          <h2>Linnik envelope</h2>
          <div className="microscope-punch-box">
            <p>
              Linnik: τ(q) ≪ (3q)<sup>5.18</sup> → ~{LINNIK_DIGITS} digits.
            </p>
            <p>
              Hire expectation: ~41,024,328 digits (eight past q). The envelope
              the lead is the eight-digit jump past q.
            </p>
          </div>
        </div>
      </section>

      {/* ── Q hub ───────────────────────────────────────────────── */}
      <section
        className="microscope-zone microscope-hub"
        aria-label="Q · record sink"
      >
        <header className="microscope-zone-head">
          <span className="microscope-zone-tag">Q · record sink</span>
          <span className="microscope-zone-arrows" aria-hidden="true">
            <span>↑</span>
            <span>↓</span>
          </span>
        </header>
        <div className="microscope-id-box microscope-hub-box">
          <p>
            <em>Q</em> = <em>q</em> = M<sub>{EXP}</sub> = 2<sup>{EXP}</sup> − 1
          </p>
          <ul>
            <li>
              decimal digits:{" "}
              <strong data-digits={DIGITS_Q_RAW}>{DIGITS_Q}</strong> (largest
              known prime as of Sep 2026)
            </li>
            <li>
              because the exponent is odd: q ≡ 1 (mod 3), so m<sub>0</sub>(q) = q
              + 1 = 2<sup>{EXP}</sup> — genuine 2-power-door sink;{" "}
              <strong>gold stops here</strong>
            </li>
            <li>log q ≈ {LOG_Q} (natural)</li>
            <li>
              sparsity caption: H(Q)/π(Q) ∼ loglog Q / log Q ≈ {SPARSITY} —
              ambient graph huge but sparse
            </li>
          </ul>
        </div>
      </section>

      {/* ── DOWN · shadow ───────────────────────────────────────── */}
      <section
        className="microscope-zone microscope-down"
        aria-label="DOWN · shadow"
      >
        <header className="microscope-zone-head">
          <span className="microscope-zone-tag">DOWN · shadow</span>
          <span className="microscope-zone-arrow" aria-hidden="true">
            ↓
          </span>
        </header>

        <div className="hire-beat">
          <h2>Gold door · collapse</h2>
          <div className="microscope-down-box microscope-gold-collapse">
            <p>
              m<sub>0</sub>(Q) = 2<sup>{EXP}</sup> — pure 2-power sink. No further
              gold descent on the hire graph. Label:{" "}
              <strong>gold door collapse</strong>.
            </p>
          </div>
        </div>

        <div className="hire-beat">
          <h2>Exponent shadow</h2>
          <p className="islands-lab-caption">
            Exact arithmetic aside — <em>not</em> a gold edge of the hire
            graph. No significance claim yet.
          </p>
          <div className="microscope-down-box">
            <ul>
              <li>
                p = {EXP} ≡ 2 (mod 3)
              </li>
              <li>
                m<sub>0</sub>(p) = 136279840 = 2<sup>5</sup> · 5 · 851749
              </li>
              <li>
                Descent: 136279841 → {"{"}5, 851749{"}"} → 851749 → {"{"}5, 3407
                {"}"} → 3407 → {"{"}13, 131{"}"} → {"{"}5, 7{"}"} with 5, 7 sinks
              </li>
            </ul>
            <div className="microscope-shadow-chain" aria-label="Boxed shadow chain">
              136279841 → 851749 → 3407 → {"{"}13, 131{"}"} → {"{"}5, 7{"}"}
            </div>
            <p className="figure-caption islands-caption">
              Exponent shadow chain.
            </p>
          </div>
        </div>

        <div className="hire-beat">
          <h2>Complement / sluice factors</h2>
          <p className="islands-lab-caption">
            Papers frozen.
          </p>
          <div className="microscope-down-box">
            <ul>
              <li>
                Rejected door m<sub>1</sub>(Q) = Q − 1 = 2(2<sup>p−1</sup> − 1)
              </li>
              <li>
                p − 1 = 136279840 = 2<sup>5</sup> · 5 · 851749 = 160 · 851749
              </li>
              <li>
                Guaranteed divisors of Q − 1: 2<sup>851749</sup> − 1 (≈ 256,402
                digits), 2<sup>160</sup> − 1, 2<sup>32</sup> − 1, 2<sup>5</sup> − 1
              </li>
              <li>
                Small branch: 2<sup>32</sup> − 1 = 3 · 5 · 17 · 257 · 65537
              </li>
              <li>
                2<sup>160</sup> − 1 factors algebraically through the 2<sup>32</sup>{" "}
                tower (and further cyclotomic pieces) — structured small factors
                only here; full list omitted for space.
              </li>
            </ul>
          </div>
        </div>

        <div className="hire-beat microscope-falsifier">
          <h2>Falsifier · Lean Hire kill-primes</h2>
          <p>
            Kill-primes for k &lt; 28 vs shadow {"{"}5, 7, 13, 131, 3407, 851749
            {"}"}:
          </p>
          <div className="door-table-wrap hire-rate-wrap microscope-life-wrap">
            <table className="door-table hire-rate-table microscope-falsifier-table">
              <thead>
                <tr>
                  <th>k</th>
                  <th>r</th>
                  <th>in shadow?</th>
                </tr>
              </thead>
              <tbody>
                {FALSIFIER.map((row) => (
                  <tr key={row.k}>
                    <td>{row.k}</td>
                    <td>{row.r}</td>
                    <td>{row.inShadow ? "yes" : "no"}</td>
                  </tr>
                ))}
              </tbody>
            </table>
          </div>
          <p className="figure-caption islands-caption islands-cold-body">
            Takeaway: overlap only {"{"}5, 7, 13{"}"} — generic tiny sinks;
            distinctive shadow primes 131, 3407, 851749 never appear as first
            factors. Shadow stays DOWN, separate from UP floor. (e.g. k=2
            kill-prime 375373 is not in the shadow.)
          </p>
        </div>
      </section>

      <p className="figure-caption islands-caption islands-cold-body">
        UP = owners / heuristics / K<sub>cert</sub> / Linnik. DOWN = gold
        collapse + exponent shadow + sluice.
      </p>
    
      <aside className="lab-note-caveats" aria-label="Lab freeze / caveats">
        <p>
          <strong>Lab freeze.</strong> <em>C</em> unnamed. Papers 1–2 frozen.
        </p>
      </aside>

    </main>
  );
}
