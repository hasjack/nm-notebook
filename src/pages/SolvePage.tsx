import { useMemo, useState } from "react";
import { fmt, fmtBase } from "../lib/format";
import { baseForMinusOne, resultAt } from "../lib/walk";

export function SolvePage() {
  const [oddI, setOddI] = useState(1);
  const [beta, setBeta] = useState(1);
  const [oddPi, setOddPi] = useState(1);
  const [alpha, setAlpha] = useState(1);

  const baseFromLockI = useMemo(
    () => baseForMinusOne(beta, oddI),
    [beta, oddI]
  );
  const baseFromLockPi = useMemo(
    () => baseForMinusOne(alpha, oddPi),
    [alpha, oddPi]
  );

  const productI = 1 * beta;
  const productPi = alpha * 1;

  return (
    <main className="page">
      <h1>Solve — pick odd, recover base</h1>
      <p className="lede">
        Two clear stories. Given the locked factor is 1, pick the free factor and
        an odd branch; the base that lands on −1 is e^(odd / free-factor).
        Exploring, not claiming.
      </p>

      <div className="solve-grid">
        <section className="solve-panel">
          <h2>Lock i (α = 1)</h2>
          <p className="hint">
            Expression base<sup>i · βπ</sup>. Pick odd and π-factor β →{" "}
            base = e^(odd / β).
          </p>

          <label className="row">
            <span>odd branch</span>
            <select
              value={oddI}
              onChange={(e) => setOddI(parseInt(e.target.value, 10))}
            >
              {[-5, -3, -1, 1, 3, 5].map((o) => (
                <option key={o} value={o}>
                  {o}
                </option>
              ))}
            </select>
          </label>

          <label className="row">
            <span>π-factor β</span>
            <span>{fmt(beta, 3)}</span>
          </label>
          <input
            type="range"
            min={0.15}
            max={4}
            step={0.01}
            value={beta}
            onChange={(e) => setBeta(parseFloat(e.target.value))}
          />

          <div className="split-readout" style={{ marginTop: "0.8rem" }}>
            <div>
              <div className="kv-label">base</div>
              <div className="kv-value">
                {baseFromLockI != null ? fmtBase(baseFromLockI) : "—"}
              </div>
            </div>
            <div>
              <div className="kv-label">result</div>
              <div className="kv-value">
                {baseFromLockI != null
                  ? resultAt(productI, baseFromLockI)
                  : "—"}
              </div>
            </div>
          </div>
          <div className="rule" style={{ textAlign: "left" }}>
            {baseFromLockI != null
              ? `base = e^(${oddI} / ${fmt(beta, 4)}) = ${fmt(baseFromLockI, 5)}`
              : "need a non-zero π-factor"}
          </div>
          <div className="actions">
            <button type="button" onClick={() => { setOddI(1); setBeta(1); }}>
              Euler: β = 1 → base e
            </button>
            <button
              type="button"
              onClick={() => {
                setOddI(1);
                setBeta(1 / 3);
              }}
            >
              β = ⅓ → base e³
            </button>
          </div>
        </section>

        <section className="solve-panel">
          <h2>Lock π (β = 1)</h2>
          <p className="hint">
            Expression base<sup>α · i · π</sup>. Pick odd and i-factor α →{" "}
            base = e^(odd / α).
          </p>

          <label className="row">
            <span>odd branch</span>
            <select
              value={oddPi}
              onChange={(e) => setOddPi(parseInt(e.target.value, 10))}
            >
              {[-5, -3, -1, 1, 3, 5].map((o) => (
                <option key={o} value={o}>
                  {o}
                </option>
              ))}
            </select>
          </label>

          <label className="row">
            <span>i-factor α</span>
            <span>{fmt(alpha, 3)}</span>
          </label>
          <input
            type="range"
            min={0.15}
            max={4}
            step={0.01}
            value={alpha}
            onChange={(e) => setAlpha(parseFloat(e.target.value))}
          />

          <div className="split-readout" style={{ marginTop: "0.8rem" }}>
            <div>
              <div className="kv-label">base</div>
              <div className="kv-value">
                {baseFromLockPi != null ? fmtBase(baseFromLockPi) : "—"}
              </div>
            </div>
            <div>
              <div className="kv-label">result</div>
              <div className="kv-value">
                {baseFromLockPi != null
                  ? resultAt(productPi, baseFromLockPi)
                  : "—"}
              </div>
            </div>
          </div>
          <div className="rule" style={{ textAlign: "left" }}>
            {baseFromLockPi != null
              ? `base = e^(${oddPi} / ${fmt(alpha, 4)}) = ${fmt(baseFromLockPi, 5)}`
              : "need a non-zero i-factor"}
          </div>
          <div className="actions">
            <button
              type="button"
              onClick={() => {
                setOddPi(1);
                setAlpha(1);
              }}
            >
              Euler: α = 1 → base e
            </button>
            <button
              type="button"
              onClick={() => {
                setOddPi(1);
                setAlpha(1 / 3);
              }}
            >
              α = ⅓ → base e³
            </button>
          </div>
        </section>
      </div>
    </main>
  );
}
