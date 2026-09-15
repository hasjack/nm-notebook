import { useMemo, useState } from "react";
import { fmt, fmtBase, baseFromSlider, sliderFromBase } from "../lib/format";
import { fmtC, polilog } from "../lib/polilog";

const PI2_6 = (Math.PI * Math.PI) / 6;
const CUBE = 1.202056903159594;
function near(a: number, b: number, eps = 1e-4) {
  return Math.abs(a - b) < eps;
}

export function Analysis3Page() {
  const [t, setT] = useState(() => sliderFromBase(Math.E));
  const [alpha, setAlpha] = useState(1);
  const [beta, setBeta] = useState(1);
  const [nTerms, setNTerms] = useState(4000);

  const base = baseFromSlider(t);
  const prod = alpha * beta * Math.log(base);
  // z = base^(α i β π) = exp(i π prod) — always on the unit circle for real levers
  const ang = Math.PI * prod;
  const zRe = Math.cos(ang);
  const zIm = Math.sin(ang);

  const li2 = useMemo(
    () => polilog(2, zRe, zIm, nTerms),
    [zRe, zIm, nTerms]
  );
  const li3 = useMemo(
    () => polilog(3, zRe, zIm, nTerms),
    [zRe, zIm, nTerms]
  );

  const height2 = -2 * li2.re; // at -1, im~0 and this → π²/6
  const height3 = -(4 / 3) * li3.re; // at -1 → cube sum

  const onPeg =
    near(zRe, -1, 1e-3) && near(zIm, 0, 1e-3);
  const h2Green = onPeg && near(height2, PI2_6, 0.01);
  const h3Green = onPeg && near(height3, CUBE, 0.02);

  return (
    <main className="page">
      <h1>Analysis 3 — deform off the peg</h1>
      <p className="lede">
        Argument <strong>z = base^(α · i · β · π) = e^(i π · α·β·ln(base))</strong>{" "}
        lives on the unit circle. At the joint beacon, z = −1 and the cute
        reductions hold. Twist the three levers and watch{" "}
        <strong>Li₂(z)</strong> vs <strong>Li₃(z)</strong>: order 2 can still
        meet π; order 3 does not fall into {"{e, i, π}"}.
      </p>

      <div
        className="value"
        style={{ color: onPeg ? "#1f4e79" : "#9a2f38" }}
      >
        {onPeg ? "ON PEG z = −1" : "DEFORMED"}
      </div>
      <div className="expr">
        z ≈ {fmt(zRe, 4)}
        {zIm >= 0 ? " + " : " − "}
        {fmt(Math.abs(zIm), 4)} i · prod αβln = {fmt(prod, 4)}
      </div>
      <div className="rule">
        heights use real part after −2 / −(4/3); exact only on the peg
      </div>

      <div className="split-readout">
        <div>
          <div className="kv-label">base</div>
          <div className="kv-value">{fmtBase(base)}</div>
        </div>
        <div>
          <div className="kv-label">α (i)</div>
          <div className="kv-value">{fmt(alpha, 3)}</div>
        </div>
        <div>
          <div className="kv-label">β (π)</div>
          <div className="kv-value">{fmt(beta, 3)}</div>
        </div>
        <div>
          <div className="kv-label">|z|</div>
          <div className="kv-value">1</div>
          <div className="hint">unit circle</div>
        </div>
      </div>

      <div className="split-readout">
        <div>
          <div className="kv-label">Li₂(z)</div>
          <div className="kv-value" style={{ fontSize: "0.95rem" }}>
            {fmtC(li2, 4)}
          </div>
        </div>
        <div>
          <div className="kv-label">−2 Re Li₂</div>
          <div className="kv-value" style={{ fontSize: "0.95rem" }}>
            {fmt(height2, 5)}
          </div>
          <div className="hint">
            {h2Green ? "π²/6" : `π²/6 = ${fmt(PI2_6, 5)}`}
          </div>
        </div>
        <div>
          <div className="kv-label">Li₃(z)</div>
          <div className="kv-value" style={{ fontSize: "0.95rem" }}>
            {fmtC(li3, 4)}
          </div>
        </div>
        <div>
          <div className="kv-label">−(4/3) Re Li₃</div>
          <div className="kv-value" style={{ fontSize: "0.95rem" }}>
            {fmt(height3, 5)}
          </div>
          <div className="hint">
            {h3Green ? "cube sum" : `cube ≈ ${fmt(CUBE, 5)}`}
          </div>
        </div>
      </div>

      <div className="panel">
        <label className="row">
          <span>base</span>
          <span>{fmtBase(base)}</span>
        </label>
        <input
          type="range"
          min={0}
          max={1}
          step={0.001}
          value={t}
          onChange={(e) => setT(parseFloat(e.target.value))}
        />
        <label className="row" style={{ marginTop: "0.8rem" }}>
          <span>α (i-factor)</span>
          <span>{fmt(alpha, 3)}</span>
        </label>
        <input
          type="range"
          min={-2}
          max={4}
          step={0.01}
          value={alpha}
          onChange={(e) => setAlpha(parseFloat(e.target.value))}
        />
        <label className="row" style={{ marginTop: "0.8rem" }}>
          <span>β (π-factor)</span>
          <span>{fmt(beta, 3)}</span>
        </label>
        <input
          type="range"
          min={-2}
          max={4}
          step={0.01}
          value={beta}
          onChange={(e) => setBeta(parseFloat(e.target.value))}
        />
        <label className="row" style={{ marginTop: "0.8rem" }}>
          <span>series terms for Li_s</span>
          <span>{nTerms}</span>
        </label>
        <input
          type="range"
          min={500}
          max={12000}
          step={100}
          value={nTerms}
          onChange={(e) => setNTerms(parseInt(e.target.value, 10))}
        />

        <p className="hint">
          Crack reading: on the peg, −2 Re Li₂ matches π²/6 (exit into π).
          −(4/3) Re Li₃ matches the cube sum only as a polilog identity — deform
          away and both heights become complex/off-target; neither deformation
          invents a cube reduction into e, i, π. The missing exit is still
          Li₃(−1) → alphabet, which this dial cannot force.
        </p>
        <div className="actions">
          <button
            type="button"
            onClick={() => {
              setT(sliderFromBase(Math.E));
              setAlpha(1);
              setBeta(1);
            }}
          >
            peg e · α=1 · β=1
          </button>
          <button
            type="button"
            onClick={() => {
              setT(sliderFromBase(Math.E ** 3));
              setAlpha(1);
              setBeta(1 / 3);
            }}
          >
            peg e³ · β=⅓ (same z=−1)
          </button>
          <button
            type="button"
            onClick={() => {
              setT(sliderFromBase(Math.E));
              setAlpha(1);
              setBeta(0.5);
            }}
          >
            deform → z ≈ i
          </button>
          <button
            type="button"
            onClick={() => {
              setT(sliderFromBase(Math.E));
              setAlpha(1);
              setBeta(0.25);
            }}
          >
            deform β=¼
          </button>
        </div>
      </div>
    </main>
  );
}
