import { Link } from "react-router-dom";

/** M31 window from When gold disconnects. Assumes hire-graph connectivity at X*. */
const X_STAR = 92274421;
const M31 = 2 ** 31 - 1; // 2147483647
const R0 = 98784247763; // ω(M31) = 46·M31 + 1
const X1 = 627065224921; // α(M31). Disconnected through X1 − 1.
const W = 313532612461; // 146·M31 − 1; door 2·73·M31
const OMEGA_R0 = 1382979468683; // ω(r0) = 14·r0 + 1
const V = 300647710579; // earlier direct 5–M31 owner; no owner up to ω(r0)

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
  const floor = 2 * M31 - 1;
  return (
    <main className="page corridor-page lab-note-page">
      <h1>Corridor</h1>
      <p className="lede">
        The <em>M</em><sub>31</sub> window. Islands is the join at <em>X</em>
        <sup>*</sup>; this rail is what happens after that prime enters.{" "}
        <Link to="/notes/when-gold-disconnects">When gold disconnects</Link>.
      </p>

      <p className="islands-bernard">
        Gold joins at 92 million. <em>M</em><sub>31</sub> enters at {fmt(R0)}.
        The stretch reconnects at {fmt(X1)}.
      </p>

      <div className="islands-panel corridor-panel">
        <div
          className="islands-corridor"
          aria-label="M31 window"
        >
          <div className="islands-corridor-head">
            <span className="islands-corridor-title">
              <em>M</em><sub>31</sub> window
            </span>
            <span className="islands-corridor-note">
              reconnects at <em>X</em><sub>1</sub>
            </span>
          </div>
          <div className="islands-corridor-rail" role="list">
            {(
              [
                {
                  id: "xstar",
                  label: "X*",
                  x: X_STAR,
                  blurb: "hire-graph join, assumed connected",
                  mark: false,
                },
                {
                  id: "r0",
                  label: "r₀",
                  x: R0,
                  blurb: "M31 enters; disconnection starts",
                  mark: false,
                },
                {
                  id: "x1",
                  label: "X₁",
                  x: X1,
                  blurb: "reconnection through w",
                  mark: true,
                },
                {
                  id: "omega",
                  label: "ω(r₀)",
                  x: OMEGA_R0,
                  blurb: "v still has no owner",
                  mark: false,
                },
              ] as const
            ).map((tick) => {
              const lo = Math.log10(X_STAR);
              const hi = Math.log10(OMEGA_R0);
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
                  title={`${tick.label} = ${fmt(tick.x)}. ${tick.blurb}`}
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
            Log scale from <em>X</em><sup>*</sup> to <em>ω</em>(<em>r</em><sub>0</sub>).
            Disconnected on [{fmt(R0)}, {fmt(X1 - 1)}]. The chain through{" "}
            <em>w</em> = {fmt(W)} goes live at <em>X</em><sub>1</sub> = {fmt(X1)}.
          </p>
        </div>
      </div>

      <p className="islands-lab-caption">
        Assuming connectivity at <em>X</em><sup>*</sup> = {fmt(X_STAR)}, gold is
        disconnected for <em>X</em><sup>*</sup> ≤ <em>X</em> ≤ 2<em>M</em><sub>61</sub> − 2
        precisely when {fmt(R0)} ≤ <em>X</em> ≤ {fmt(X1 - 1)}.{" "}
        <em>r</em><sub>0</sub> = <em>ω</em>(<em>M</em><sub>31</sub>) has door 2·23·<em>M</em><sub>31</sub>.
        Reconnection is through <em>w</em> = {fmt(W)}, door 2·73·<em>M</em><sub>31</sub>,
        and the chain 73 → 37 → 19 → 5.
      </p>

      <p className="figure-caption islands-caption islands-cold-body">
        Machine check of the hire-graph note through 2.2·10<sup>9</sup>.{" "}
        <em>M</em><sub>31</sub> = {fmt(M31)} cannot enter <em>S</em> before{" "}
        2<em>M</em> − 1 = {fmt(floor)}. The earlier bridge owner <em>v</em> = {fmt(V)}{" "}
        has door 2<sup>2</sup>·5·7·<em>M</em><sub>31</sub> and no owner up to{" "}
        <em>ω</em>(<em>r</em><sub>0</sub>) = {fmt(OMEGA_R0)}.
      </p>

      <aside className="lab-note-caveats" aria-label="Scope">
        <p>
          This rail is the <em>M</em><sub>31</sub> stretch from the sequel, given{" "}
          <em>X</em><sup>*</sup>.{" "}
          <Link to="/notes/when-gold-disconnects">Note</Link>
          {" · "}
          <Link to="/islands">Islands</Link>.
        </p>
      </aside>
    </main>
  );
}
