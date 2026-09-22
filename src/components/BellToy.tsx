import { useEffect, useMemo, useRef, useState } from "react";

type Results = {
  S: number;
  Eab: number;
  Eabp: number;
  Eapb: number;
  Eapbp: number;
};

function clamp(x: number, lo: number, hi: number) {
  return Math.min(hi, Math.max(lo, x));
}

function angleDiff(theta: number, lam: number) {
  let d = Math.abs(theta - lam) % (2 * Math.PI);
  return Math.min(d, 2 * Math.PI - d);
}

/** Interactive CHSH sampler for the progress-state Bell toy. */
export function BellToyInteractive() {
  const [w, setW] = useState(Math.PI / 4);
  const [deltaHigh, setDeltaHigh] = useState(0.85);
  const [deltaLow, setDeltaLow] = useState(0.2);
  const [nSamples, setNSamples] = useState(100_000);
  const [results, setResults] = useState<Results>({
    S: 0,
    Eab: 0,
    Eabp: 0,
    Eapb: 0,
    Eapbp: 0,
  });

  const settings = useMemo(
    () => ({ a: 0, b: Math.PI / 4, bp: -Math.PI / 4, ap: Math.PI / 2 }),
    [],
  );

  const timerRef = useRef<number | null>(null);

  useEffect(() => {
    if (timerRef.current !== null) window.clearTimeout(timerRef.current);
    timerRef.current = window.setTimeout(() => {
      const dHi = clamp(deltaHigh, 0, 0.999999);
      const dLo = clamp(deltaLow, 0, 0.999999);
      const sigma0 = new Int8Array(nSamples);
      const p0 = new Float64Array(nSamples);
      const lam = new Float64Array(nSamples);
      for (let i = 0; i < nSamples; i++) {
        sigma0[i] = Math.random() < 0.5 ? -1 : 1;
        p0[i] = Math.random();
        lam[i] = Math.random() * 2 * Math.PI - Math.PI;
      }
      const pairs = [
        ["ab", "a", "b"],
        ["abp", "a", "bp"],
        ["apb", "ap", "b"],
        ["apbp", "ap", "bp"],
      ] as const;
      const E: Record<string, number> = {};
      for (const [key, th1, th2] of pairs) {
        let sum = 0;
        const t1 = settings[th1];
        const t2 = settings[th2];
        for (let i = 0; i < nSamples; i++) {
          const d1 = angleDiff(t1, lam[i]);
          const d2 = angleDiff(t2, lam[i]);
          const da = d1 < w ? dHi : dLo;
          const db = d2 < w ? dHi : dLo;
          const sigmaA = sigma0[i] * (Math.floor(p0[i] + da) % 2 === 0 ? 1 : -1);
          const sigmaB = sigma0[i] * (Math.floor(p0[i] + db) % 2 === 0 ? 1 : -1);
          sum += sigmaA * sigmaB;
        }
        E[key] = sum / nSamples;
      }
      setResults({
        S: Number((E.ab + E.abp + E.apb - E.apbp).toFixed(4)),
        Eab: Number(E.ab.toFixed(4)),
        Eabp: Number(E.abp.toFixed(4)),
        Eapb: Number(E.apb.toFixed(4)),
        Eapbp: Number(E.apbp.toFixed(4)),
      });
    }, 120);
    return () => {
      if (timerRef.current !== null) window.clearTimeout(timerRef.current);
    };
  }, [w, deltaHigh, deltaLow, nSamples, settings]);

  return (
    <div className="toy-panel">
      <label className="row">
        <span>Response window w (rad)</span>
        <span className="toy-readout">{w.toFixed(3)}</span>
      </label>
      <input
        type="range"
        min={Math.PI / 6}
        max={Math.PI / 3}
        step={0.01}
        value={w}
        onChange={(e) => setW(parseFloat(e.target.value))}
      />
      <label className="row">
        <span>δ high (in-window)</span>
        <span className="toy-readout">{deltaHigh.toFixed(3)}</span>
      </label>
      <input
        type="range"
        min={0}
        max={0.99}
        step={0.01}
        value={deltaHigh}
        onChange={(e) =>
          setDeltaHigh(Math.max(parseFloat(e.target.value), deltaLow))
        }
      />
      <label className="row">
        <span>δ low (out-of-window)</span>
        <span className="toy-readout">{deltaLow.toFixed(3)}</span>
      </label>
      <input
        type="range"
        min={0}
        max={0.99}
        step={0.01}
        value={deltaLow}
        onChange={(e) =>
          setDeltaLow(Math.min(parseFloat(e.target.value), deltaHigh))
        }
      />
      <label className="row">
        <span>Samples</span>
        <span className="toy-readout">{nSamples.toLocaleString()}</span>
      </label>
      <input
        type="range"
        min={20000}
        max={200000}
        step={10000}
        value={nSamples}
        onChange={(e) => setNSamples(parseInt(e.target.value, 10))}
      />
      <p className="hint">Lemma assumes δ ∈ [0, 1). Sliders enforce that.</p>
      <div className="toy-readout toy-chsh">
        <div>
          CHSH S = <span className="toy-s">{results.S}</span>
        </div>
        <div className="toy-grid">
          <div>E(ab) = {results.Eab}</div>
          <div>E(ab′) = {results.Eabp}</div>
          <div>E(a′b) = {results.Eapb}</div>
          <div>E(a′b′) = {results.Eapbp}</div>
        </div>
      </div>
    </div>
  );
}
