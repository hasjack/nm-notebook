import { Link } from "react-router-dom";

/** Thin M₃₁ corridor integers — do not invent. */
const X_STAR = 92274421; // first owner of BRIDGE; m0(X*) = 2 · BRIDGE
const M31 = (1 << 31) - 1; // 2147483647
const M31_FIRST_OWNER = 98784247763; // thin hunt, class B; fat not run
const M31_FIRST_BRIDGE = 300647710579; // thin: first direct 5–M31 bridge owner, class A
// m0(v)=2²·5·7·M31; v/r0 ≈ 3.04
const M31_V_HIRE = 24051816846319; // thin: τ(v), first owner of v; live arcs at X≥τ(v)
// floor was 2v-1≈6.01e11; actual ~40× larger
const M31_MIXED = 313532612461; // thin: earliest mixed M31 connector (class A)
const M31_MIXED_HIRE = 627065224921; // τ(p*)=2p*-1; new corridor upper marker
// vs τ(v)/τ(p*)≈38.36; fat not run

function fmt(n: number): string {
  return n.toLocaleString("en-US");
}

function sci(n: number): string {
  const e = Math.floor(Math.log10(n));
  const m = n / 10 ** e;
  return `${m.toFixed(m >= 10 ? 0 : 2).replace(/\.?0+$/, "")}·10${toSup(e)}`;
}

function toSup(e: number): string {
  const map: Record<string, string> = {
    "0": "⁰",
    "1": "¹",
    "2": "²",
    "3": "³",
    "4": "⁴",
    "5": "⁵",
    "6": "⁶",
    "7": "⁷",
    "8": "⁸",
    "9": "⁹",
  };
  return String(e)
    .split("")
    .map((c) => map[c] ?? c)
    .join("");
}

export function CorridorPage() {
  return (
    <main className="page corridor-page lab-note-page">
      <h1>Corridor</h1>
      <p className="lede">
        Thin M₃₁ number rail — first owners, mixed connector, and seating times.
        The swan spotlight lives on <Link to="/islands">Islands</Link>; fat not
        run.
      </p>

      <p className="islands-bernard">
        Gold joins at 92 million — M₃₁ first owner at 98.8 billion — and a mixed
        connector seats by ≈ 6.27·10¹¹ (≈ 38× sooner than the direct bridge’s
        τ(v)). Thin only; fat not run.
      </p>

      <div className="islands-panel corridor-panel">
        <div
          className="islands-corridor"
          aria-label="M31 island corridor, thin markers"
        >
          <div className="islands-corridor-head">
            <span className="islands-corridor-title">M₃₁ corridor · thin</span>
            <span className="islands-corridor-note">
              upper marker τ(p*) · fat not run
            </span>
          </div>
          <div className="islands-corridor-rail" role="list">
            {(
              [
                {
                  id: "xstar",
                  label: "X*",
                  x: X_STAR,
                  blurb: "last island joins mainland",
                },
                {
                  id: "r0",
                  label: "r₀",
                  x: M31_FIRST_OWNER,
                  blurb: "M₃₁ first owner — island can open",
                },
                {
                  id: "tp",
                  label: "τ(p*)",
                  x: M31_MIXED_HIRE,
                  blurb: "mixed connector seats — current upper marker",
                  mark: true,
                },
                {
                  id: "tv",
                  label: "τ(v)",
                  x: M31_V_HIRE,
                  blurb: "direct bridge ticket finally sits",
                },
              ] as const
            ).map((tick) => {
              const lo = Math.log10(X_STAR);
              const hi = Math.log10(M31_V_HIRE);
              const pct = ((Math.log10(tick.x) - lo) / (hi - lo)) * 100;
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
                  title={`${tick.label} = ${fmt(tick.x)} — ${tick.blurb}`}
                >
                  <span className="islands-corridor-dot" />
                  <span className="islands-corridor-label">{tick.label}</span>
                  <span className="islands-corridor-val">{sci(tick.x)}</span>
                </div>
              );
            })}
            <div className="islands-corridor-line" aria-hidden="true" />
          </div>
          <p className="islands-corridor-caption">
            Log scale from X* to τ(v). Mixed seat τ(p*) = {fmt(M31_MIXED_HIRE)}{" "}
            via p* = {fmt(M31_MIXED)}; direct τ(v) is ≈38× later. Island open
            window under thin markers: [r₀, τ(p*)].
          </p>
        </div>
      </div>

      <p className="islands-lab-caption">
        Lag stack (thin): r₀ ≈ 23× the door floor; mixed connector p* seats at
        τ(p*) ≈ 6.27·10¹¹ (hire floor 2p* − 1); direct bridge owner v seats much
        later at τ(v) ≈ 2.41·10¹³ (τ(v)/τ(p*) ≈ 38). Current upper marker for the
        island corridor is τ(p*), not τ(v). Fat not run — a full component check
        could still find an earlier join.
      </p>

      <p className="figure-caption islands-caption islands-cold-body">
        Witness at <em>X</em>
        <sup>*</sup>; machine check through 2.2·10⁹. M₃₁ = 2³¹ − 1 cannot enter
        S before 2M − 1 ≈ 4.29·10⁹ (proof). Thin: first owner{" "}
        {fmt(M31_FIRST_OWNER)}; first direct 5–M₃₁ bridge owner{" "}
        {fmt(M31_FIRST_BRIDGE)} (class A, m₀ = 2²·5·7·M₃₁, ratio ≈ 3.04). First
        owner of v is τ(v) = {fmt(M31_V_HIRE)}. Earlier mixed connector p* ={" "}
        {fmt(M31_MIXED)} seats at τ(p*) = {fmt(M31_MIXED_HIRE)} ≈ 6.27·10¹¹
        (class A, m₀/M = 2·73) — that is the current corridor upper marker
        (τ(v)/τ(p*) ≈ 38). Fat not run. M = {fmt(M31)}.
      </p>
    
      <aside className="lab-note-caveats" aria-label="Lab freeze / caveats">
        <p>
          <strong>Lab freeze.</strong> Thin markers only; fat not run.{" "}
          <em>C</em> unnamed. Papers 1–2 frozen.
        </p>
      </aside>

    </main>
  );
}
