import { useMemo, useState } from "react";
import { Link } from "react-router-dom";
import {
  ODLYZKO_GAMMAS,
  PRIMES_TO_1000,
  PSI_STAIR_X_MAX,
  mainTerm,
  psiFromZeros,
  psiStair,
} from "../lib/psiStairData";
import "./DoorCoveragePage.css";

const N_MAX = ODLYZKO_GAMMAS.length;

function niceTicks(lo: number, hi: number, count = 5): number[] {
  if (!(hi > lo)) return [lo];
  const span = hi - lo;
  const raw = span / Math.max(1, count - 1);
  const pow = 10 ** Math.floor(Math.log10(raw));
  const candidates = [1, 2, 2.5, 5, 10].map((m) => m * pow);
  let step = candidates[0]!;
  for (const c of candidates) {
    if (span / c <= count + 1) {
      step = c;
      break;
    }
  }
  const start = Math.ceil(lo / step) * step;
  const ticks: number[] = [];
  for (let t = start; t <= hi + step * 1e-9; t += step) ticks.push(t);
  return ticks;
}

function buildStairPath(
  xMax: number,
  toX: (v: number) => number,
  toY: (v: number) => number,
): string {
  const events: number[] = [];
  for (const p of PRIMES_TO_1000) {
    if (p > xMax) break;
    let pk = p;
    while (pk <= xMax) {
      events.push(pk);
      const next = pk * p;
      if (next / p !== pk) break;
      pk = next;
    }
  }
  events.sort((a, b) => a - b);

  const parts: string[] = [];
  let x0 = 1;
  let y = 0;
  parts.push(`M ${toX(x0).toFixed(2)} ${toY(y).toFixed(2)}`);
  for (const xe of events) {
    parts.push(`L ${toX(xe).toFixed(2)} ${toY(y).toFixed(2)}`);
    y = psiStair(xe);
    parts.push(`L ${toX(xe).toFixed(2)} ${toY(y).toFixed(2)}`);
  }
  parts.push(`L ${toX(xMax).toFixed(2)} ${toY(y).toFixed(2)}`);
  return parts.join(" ");
}

function buildCurvePath(
  xMin: number,
  xMax: number,
  steps: number,
  yAt: (x: number) => number,
  toX: (v: number) => number,
  toY: (v: number) => number,
): string {
  const parts: string[] = [];
  for (let i = 0; i <= steps; i++) {
    const t = i / steps;
    // Slight log bias so early primes keep room on screen.
    const x = xMin * Math.pow(xMax / xMin, t);
    const y = yAt(x);
    parts.push(
      `${i === 0 ? "M" : "L"} ${toX(x).toFixed(2)} ${toY(y).toFixed(2)}`,
    );
  }
  return parts.join(" ");
}

function PsiStairChart({ n, xMax }: { n: number; xMax: number }) {
  const W = 720;
  const H = 420;
  const pad = { l: 52, r: 18, t: 28, b: 44 };
  const iw = W - pad.l - pad.r;
  const ih = H - pad.t - pad.b;
  const xMin = 1.5;

  const view = useMemo(() => {
    const samples = 280;
    let yMin = 0;
    let yMax = xMax;
    for (let i = 0; i <= samples; i++) {
      const t = i / samples;
      const x = xMin * Math.pow(xMax / xMin, t);
      const ys = [psiStair(x), mainTerm(x), psiFromZeros(x, n)];
      for (const y of ys) {
        if (y < yMin) yMin = y;
        if (y > yMax) yMax = y;
      }
    }
    // Pad a little; keep zero in frame when close.
    const padY = Math.max(2, (yMax - yMin) * 0.06);
    yMin -= padY;
    yMax += padY;
    return { yMin, yMax };
  }, [n, xMax]);

  const toX = (v: number) =>
    pad.l + ((Math.log(v) - Math.log(xMin)) / (Math.log(xMax) - Math.log(xMin))) * iw;
  const toY = (v: number) =>
    pad.t + ih * (1 - (v - view.yMin) / (view.yMax - view.yMin));

  const stairPath = buildStairPath(xMax, toX, toY);
  const mainPath = buildCurvePath(xMin, xMax, 240, mainTerm, toX, toY);
  const wavePath = buildCurvePath(
    xMin,
    xMax,
    360,
    (x) => psiFromZeros(x, n),
    toX,
    toY,
  );

  const xTicks = [2, 3, 5, 7, 11, 20, 50, 100, 200, 500, 1000].filter(
    (t) => t >= 2 && t <= xMax,
  );
  const yTicks = niceTicks(view.yMin, view.yMax, 6);

  return (
    <figure className="power-firing-chart psi-stair-chart">
      <svg
        viewBox={`0 0 ${W} ${H}`}
        role="img"
        aria-label={`Chebyshev ψ stair versus main term and truncated wave sum with ${n} critical zeros, x up to ${xMax}`}
      >
        <title>
          Chebyshev ψ stair lining up with waves from the first {n} critical
          zeros (assumes the critical line)
        </title>

        {yTicks.map((t) => (
          <g key={`y-${t}`}>
            <line
              x1={pad.l}
              y1={toY(t)}
              x2={pad.l + iw}
              y2={toY(t)}
              stroke="#e6ddd0"
              strokeWidth="1"
            />
            <text
              x={pad.l - 8}
              y={toY(t) + 4}
              textAnchor="end"
              fontSize="11"
              fill="#6b5e4e"
            >
              {Math.abs(t) >= 100 ? t.toFixed(0) : t.toFixed(1)}
            </text>
          </g>
        ))}

        {xTicks.map((t) => (
          <g key={`x-${t}`}>
            <line
              x1={toX(t)}
              y1={pad.t}
              x2={toX(t)}
              y2={pad.t + ih}
              stroke="#eee6da"
              strokeWidth="1"
            />
            <text
              x={toX(t)}
              y={pad.t + ih + 18}
              textAnchor="middle"
              fontSize="11"
              fill="#6b5e4e"
            >
              {t}
            </text>
          </g>
        ))}

        <line
          x1={pad.l}
          y1={pad.t}
          x2={pad.l}
          y2={pad.t + ih}
          stroke="#8a7a68"
          strokeWidth="1"
        />
        <line
          x1={pad.l}
          y1={pad.t + ih}
          x2={pad.l + iw}
          y2={pad.t + ih}
          stroke="#8a7a68"
          strokeWidth="1"
        />

        {/* Main term (diagonal) */}
        <path d={mainPath} fill="none" stroke="#8a7a68" strokeWidth="1.5" strokeDasharray="5 4" />
        {/* Truncated wave sum */}
        <path d={wavePath} fill="none" stroke="#b85c38" strokeWidth="2" />
        {/* ψ stair */}
        <path d={stairPath} fill="none" stroke="#1f5f8b" strokeWidth="2.25" />

        <text x={pad.l} y={16} fontSize="12" fill="#1f5f8b">
          ψ(x) stair
        </text>
        <text x={pad.l + 90} y={16} fontSize="12" fill="#8a7a68">
          main term x − log(2π)
        </text>
        <text x={pad.l + 250} y={16} fontSize="12" fill="#b85c38">
          main − Σ waves (n = {n})
        </text>
        <text
          x={pad.l + iw / 2}
          y={H - 6}
          textAnchor="middle"
          fontSize="12"
          fill="#3d3428"
        >
          x (log scale)
        </text>
      </svg>
      <figcaption className="figure-caption">
        This plot <em>assumes</em> zeros sit at ½ + iγ; it shows lining-up with
        the Chebyshev ψ stair, it does not prove the hypothesis. Trivial zeros
        can wait. Odlyzko γ’s hardcoded — not recomputed here.
      </figcaption>
    </figure>
  );
}

/** Lab: Chebyshev ψ stair vs truncated explicit-formula waves (critical line assumed). */
export function PsiStairPage() {
  const [n, setN] = useState(5);
  const [xMax, setXMax] = useState(100);

  return (
    <main className="page notes lab-note-page door-coverage-page">
      <h1>ψ stair</h1>
      <p className="lede">
        Riemann–von Mangoldt lining-up: the Chebyshev ψ stair against the
        truncated explicit formula built from Odlyzko’s critical zeros. Drag{" "}
        <em>n</em> — at 0 only the main term; at 1 a slow ripple; by 5 the jumps
        at 2, 3, 5, 7, 11 start to appear. Related:{" "}
        <Link to="/primes">Primes</Link>, <Link to="/zeta-doors">Zeta doors</Link>{" "}
        (separate shelf).
      </p>

      <h2>What is plotted</h2>
      <p>
        Three series versus <em>x</em>. The stair is ψ(x) = Σ log <em>p</em> over
        prime powers <em>p</em>
        <sup>k</sup> ≤ <em>x</em>. The dashed line is the main term{" "}
        <em>x</em> − log(2π). The warm curve is that main term minus the first{" "}
        <em>n</em> conjugate-pair waves
      </p>
      <aside className="lab-theorem" aria-label="Wave for one conjugate pair">
        <p className="lab-theorem-implies">
          ((2 √x) / hypot(½, γ)) · cos(γ log x − atan2(γ, ½))
        </p>
      </aside>
      <p>
        with each γ taken from Odlyzko’s tables and ρ placed on the critical
        line at ½ + iγ. Findings and visualisation only — not a proof claim.
      </p>

      <div className="coverage-controls psi-stair-controls">
        <label>
          Zeros used: <strong>{n}</strong> / {N_MAX}
          <input
            type="range"
            min={0}
            max={N_MAX}
            step={1}
            value={n}
            onChange={(e) => setN(Number(e.target.value))}
            aria-valuemin={0}
            aria-valuemax={N_MAX}
            aria-valuenow={n}
            aria-label="Number of critical zeros in the truncated sum"
          />
        </label>
        <label>
          x max: <strong>{xMax}</strong>
          <input
            type="range"
            min={30}
            max={PSI_STAIR_X_MAX}
            step={10}
            value={xMax}
            onChange={(e) => setXMax(Number(e.target.value))}
            aria-valuemin={30}
            aria-valuemax={PSI_STAIR_X_MAX}
            aria-valuenow={xMax}
            aria-label="Maximum x on the plot"
          />
        </label>
        <button
          type="button"
          onClick={() => {
            setN(5);
            setXMax(100);
          }}
        >
          Money shot (n = 5, x ≤ 100)
        </button>
      </div>

      <PsiStairChart n={n} xMax={xMax} />

      <h2>How to read it</h2>
      <p>
        At <em>n</em> = 0 the warm curve sits on the dashed main term. Adding the
        first zero lays a slow cos(γ log <em>x</em>) ripple. By a handful of
        zeros the truncated sum begins to track the stair’s jumps — the classic
        explicit-formula money shot. Wider <em>x</em> needs more zeros before the
        match looks sharp; this page keeps a few hundred for a first look.
      </p>

      <p className="lab-footnote">
        Hardcoded Odlyzko γ’s ({N_MAX}) and primes through {PSI_STAIR_X_MAX}.
        Source: <code>src/lib/psiStairData.ts</code>. Lab findings only.
      </p>
    </main>
  );
}
