import { useEffect, useMemo, useRef, useState } from "react";

type ViewMode =
  | "escape"
  | "flipCount"
  | "parity"
  | "firstFlip"
  | "occPlus"
  | "occMinus";

type SwitchModel = "threshold" | "sinswitch";

type Probe = {
  c: number;
  b: number;
  escapeIter: number | null;
  flips: number;
  firstFlip: number | null;
  occPlus: number;
  occMinus: number;
  xs: number[];
  sigmas: number[];
  gateAbs: number[];
  gateLabel: string;
};

function clamp(x: number, lo: number, hi: number) {
  return Math.min(hi, Math.max(lo, x));
}

function lerp(a: number, b: number, t: number) {
  return a + (b - a) * t;
}

function colorRamp(t: number): [number, number, number] {
  const x = clamp(t, 0, 1);
  return [
    Math.round(255 * clamp(lerp(0.05, 1.0, x), 0, 1)),
    Math.round(255 * clamp(lerp(0.02, 0.75, Math.pow(x, 0.9)), 0, 1)),
    Math.round(255 * clamp(lerp(0.08, 0.15, Math.pow(x, 0.7)), 0, 1)),
  ];
}

function signNonzero(x: number) {
  return x >= 0 ? 1 : -1;
}

function simulatePoint(params: {
  model: SwitchModel;
  c: number;
  b: number;
  kappa: number;
  maxIter: number;
  escapeR: number;
  traceN: number;
}): Probe {
  const { model, c, b, kappa, maxIter, escapeR, traceN } = params;
  let x = b;
  let flips = 0;
  let firstFlip: number | null = null;
  let escapeIter: number | null = null;
  let sigma =
    model === "threshold" ? signNonzero(b) : signNonzero(Math.sin(kappa * b));
  let occPlus = 0;
  let occMinus = 0;
  const xs: number[] = [];
  const sigmas: number[] = [];
  const gateAbs: number[] = [];
  const nTrace = Math.min(maxIter, traceN);
  const threshold = 1.0 + Math.abs(b) * kappa;
  const gateLabel =
    model === "threshold" ? "|x_n| − (1+|b|κ)" : "|sin(κ x_n)|";

  for (let n = 0; n < maxIter; n++) {
    if (sigma === 1) occPlus++;
    else occMinus++;
    if (n < nTrace) {
      xs.push(x);
      sigmas.push(sigma);
      gateAbs.push(
        model === "threshold"
          ? Math.max(0, Math.abs(x) - threshold)
          : Math.abs(Math.sin(kappa * x)),
      );
    }
    const xNext = sigma * x * x + c;
    const sigmaNext =
      model === "threshold"
        ? Math.abs(xNext) > threshold
          ? -sigma
          : sigma
        : signNonzero(Math.sin(kappa * xNext));
    if (sigmaNext !== sigma) {
      flips++;
      if (firstFlip === null) firstFlip = n + 1;
    }
    x = xNext;
    sigma = sigmaNext;
    if (Math.abs(x) > escapeR) {
      escapeIter = n + 1;
      break;
    }
  }
  const steps = escapeIter ?? maxIter;
  return {
    c,
    b,
    escapeIter,
    flips,
    firstFlip,
    occPlus: occPlus / steps,
    occMinus: occMinus / steps,
    xs,
    sigmas,
    gateAbs,
    gateLabel,
  };
}

export function SwitchingAtlasExplorer() {
  const [cMin, setCMin] = useState(-1.5);
  const [cMax, setCMax] = useState(0.5);
  const [bMin, setBMin] = useState(-1.0);
  const [bMax, setBMax] = useState(1.0);
  const [model, setModel] = useState<SwitchModel>("threshold");
  const [kappa, setKappa] = useState(0.6235);
  const [maxIter, setMaxIter] = useState(250);
  const [escapeR, setEscapeR] = useState(2.0);
  const [view, setView] = useState<ViewMode>("escape");
  const [resPreset, setResPreset] = useState<"low" | "med" | "high">("med");
  const [probe, setProbe] = useState<Probe | null>(null);
  const canvasRef = useRef<HTMLCanvasElement | null>(null);

  const dims = useMemo(() => {
    if (resPreset === "low") return { w: 320, h: 200 };
    if (resPreset === "high") return { w: 800, h: 500 };
    return { w: 520, h: 320 };
  }, [resPreset]);

  const timerRef = useRef<number | null>(null);

  useEffect(() => {
    if (timerRef.current !== null) window.clearTimeout(timerRef.current);
    timerRef.current = window.setTimeout(() => {
      const canvas = canvasRef.current;
      if (!canvas) return;
      canvas.width = dims.w;
      canvas.height = dims.h;
      const ctx = canvas.getContext("2d", { willReadFrequently: true });
      if (!ctx) return;
      const img = ctx.createImageData(dims.w, dims.h);
      const data = img.data;
      const flipMax = 20;
      for (let j = 0; j < dims.h; j++) {
        const bj = lerp(bMax, bMin, j / (dims.h - 1));
        for (let i = 0; i < dims.w; i++) {
          const ci = lerp(cMin, cMax, i / (dims.w - 1));
          const out = simulatePoint({
            model,
            c: ci,
            b: bj,
            kappa,
            maxIter,
            escapeR,
            traceN: 0,
          });
          let rgb: [number, number, number] = [0, 0, 0];
          if (view === "escape") {
            rgb = colorRamp((out.escapeIter ?? maxIter) / maxIter);
          } else if (view === "flipCount") {
            rgb = colorRamp(clamp(out.flips / flipMax, 0, 1));
          } else if (view === "parity") {
            rgb = out.flips % 2 === 1 ? [220, 70, 70] : [60, 110, 220];
          } else if (view === "firstFlip") {
            rgb = colorRamp(clamp((out.firstFlip ?? maxIter) / maxIter, 0, 1));
          } else if (view === "occPlus") {
            rgb = colorRamp(clamp(out.occPlus, 0, 1));
          } else {
            rgb = colorRamp(clamp(out.occMinus, 0, 1));
          }
          const idx = 4 * (j * dims.w + i);
          data[idx] = rgb[0];
          data[idx + 1] = rgb[1];
          data[idx + 2] = rgb[2];
          data[idx + 3] = 255;
        }
      }
      ctx.putImageData(img, 0, 0);
    }, 120);
    return () => {
      if (timerRef.current !== null) window.clearTimeout(timerRef.current);
    };
  }, [dims, cMin, cMax, bMin, bMax, model, kappa, maxIter, escapeR, view]);

  function onCanvasClick(e: React.MouseEvent<HTMLCanvasElement>) {
    const canvas = canvasRef.current;
    if (!canvas) return;
    const rect = canvas.getBoundingClientRect();
    const x = clamp((e.clientX - rect.left) / rect.width, 0, 1);
    const y = clamp((e.clientY - rect.top) / rect.height, 0, 1);
    setProbe(
      simulatePoint({
        model,
        c: lerp(cMin, cMax, x),
        b: lerp(bMax, bMin, y),
        kappa,
        maxIter,
        escapeR,
        traceN: 600,
      }),
    );
  }

  return (
    <div className="toy-panel">
      <p className="lede" style={{ marginBottom: "0.6rem" }}>
        <code>xₙ₊₁ = σₙ xₙ² + c</code>
        {model === "threshold"
          ? ", flip when |xₙ₊₁| > 1+|b|κ."
          : ", σₙ₊₁ = sign(sin(κ xₙ₊₁))."}
      </p>
      <div className="toy-grid">
        <div>
          <label className="row">
            <span>switch rule</span>
          </label>
          <select
            value={model}
            onChange={(e) => {
              setModel(e.target.value as SwitchModel);
              setProbe(null);
            }}
          >
            <option value="threshold">threshold flip</option>
            <option value="sinswitch">sign–sin gate</option>
          </select>
          <label className="row">
            <span>κ</span>
            <span className="toy-readout">{kappa.toFixed(4)}</span>
          </label>
          <input
            type="range"
            min={0}
            max={2}
            step={0.0005}
            value={kappa}
            onChange={(e) => setKappa(parseFloat(e.target.value))}
          />
          <label className="row">
            <span>maxIter</span>
            <span className="toy-readout">{maxIter}</span>
          </label>
          <input
            type="range"
            min={50}
            max={800}
            step={10}
            value={maxIter}
            onChange={(e) => setMaxIter(parseInt(e.target.value, 10))}
          />
          <label className="row">
            <span>escape radius</span>
            <span className="toy-readout">{escapeR.toFixed(2)}</span>
          </label>
          <input
            type="range"
            min={1.5}
            max={10}
            step={0.1}
            value={escapeR}
            onChange={(e) => setEscapeR(parseFloat(e.target.value))}
          />
        </div>
        <div>
          <label className="row">
            <span>view</span>
          </label>
          <select
            value={view}
            onChange={(e) => setView(e.target.value as ViewMode)}
          >
            <option value="escape">escape time</option>
            <option value="parity">flip parity</option>
            <option value="firstFlip">first flip iteration</option>
            <option value="flipCount">flip count</option>
            <option value="occPlus">occupancy σ=+1</option>
            <option value="occMinus">occupancy σ=−1</option>
          </select>
          <label className="row">
            <span>resolution</span>
            <span className="toy-readout">
              {dims.w}×{dims.h}
            </span>
          </label>
          <select
            value={resPreset}
            onChange={(e) =>
              setResPreset(e.target.value as "low" | "med" | "high")
            }
          >
            <option value="low">low</option>
            <option value="med">medium</option>
            <option value="high">high</option>
          </select>
          <div className="toy-grid" style={{ marginTop: "0.7rem" }}>
            <label>
              c min
              <input
                type="number"
                value={cMin}
                step={0.1}
                onChange={(e) => setCMin(parseFloat(e.target.value))}
              />
            </label>
            <label>
              c max
              <input
                type="number"
                value={cMax}
                step={0.1}
                onChange={(e) => setCMax(parseFloat(e.target.value))}
              />
            </label>
            <label>
              b min
              <input
                type="number"
                value={bMin}
                step={0.1}
                onChange={(e) => setBMin(parseFloat(e.target.value))}
              />
            </label>
            <label>
              b max
              <input
                type="number"
                value={bMax}
                step={0.1}
                onChange={(e) => setBMax(parseFloat(e.target.value))}
              />
            </label>
          </div>
        </div>
      </div>
      <canvas
        ref={canvasRef}
        onClick={onCanvasClick}
        className="toy-canvas"
        width={dims.w}
        height={dims.h}
      />
      <p className="hint">Click to probe. Horizontal: c. Vertical: b = x₀.</p>
      {probe ? (
        <div className="toy-probe">
          <div className="toy-readout toy-grid">
            <div>c = {probe.c.toFixed(6)}</div>
            <div>b = {probe.b.toFixed(6)}</div>
            <div>κ = {kappa.toFixed(4)}</div>
            <div>escape = {probe.escapeIter ?? "no"}</div>
            <div>flips = {probe.flips}</div>
            <div>first flip = {probe.firstFlip ?? "none"}</div>
            <div>occ + = {probe.occPlus.toFixed(3)}</div>
            <div>occ − = {probe.occMinus.toFixed(3)}</div>
          </div>
          <div className="toy-grid" style={{ marginTop: "0.8rem" }}>
            <TracePlot title="x_n" values={probe.xs} color="#1f4e79" />
            <TracePlot
              title="σ_n"
              values={probe.sigmas}
              color="#9a2f38"
              yMin={-1.2}
              yMax={1.2}
            />
            <TracePlot
              title={probe.gateLabel}
              values={probe.gateAbs}
              color="#2f6b4f"
              yMin={0}
            />
          </div>
        </div>
      ) : null}
      <p className="hint">
        CPU-bound. Medium resolution is the default; high after κ / maxIter
        settle.
      </p>
    </div>
  );
}

function TracePlot(props: {
  title: string;
  values: number[];
  color: string;
  yMin?: number;
  yMax?: number;
}) {
  const { title, values, color } = props;
  const W = 320;
  const H = 140;
  const pad = 10;
  const yMin = props.yMin ?? Math.min(...values, 0);
  const yMax = props.yMax ?? Math.max(...values, 0);
  const denom = yMax - yMin === 0 ? 1 : yMax - yMin;
  const pts = values
    .map((v, i) => {
      const x = pad + (i * (W - 2 * pad)) / Math.max(1, values.length - 1);
      const y = pad + (1 - (v - yMin) / denom) * (H - 2 * pad);
      return `${x.toFixed(2)},${y.toFixed(2)}`;
    })
    .join(" ");
  return (
    <div className="toy-trace">
      <div className="toy-readout">{title}</div>
      <svg width={W} height={H} viewBox={`0 0 ${W} ${H}`}>
        <polyline points={pts} fill="none" stroke={color} strokeWidth="1.5" />
      </svg>
    </div>
  );
}
