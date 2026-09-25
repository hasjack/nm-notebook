import { useMemo, useState } from "react";

type CChoice = 5 | 1010;

type LatticeLabel = {
  a: number;
  b: number;
  R: number;
  /** Odd-part factorisation of R, or of S when |R|=1. */
  odd: string;
  highlight?: boolean;
  /** Label offset in SVG pixels from the lattice point. */
  dx?: number;
  dy?: number;
};

type ContMark = {
  x: number;
  y: number;
  label: string;
  dx?: number;
  dy?: number;
};

function fmtR(R: number): string {
  if (R === 0) return "R = 0";
  return R > 0 ? `R = +${R}` : `R = ${R}`;
}

/** Precomputed labels — small set, findings-only. */
const LABELS_C5: LatticeLabel[] = [
  { a: 3, b: 4, R: -34, odd: "17", highlight: true, dx: -10, dy: 22 },
  { a: 4, b: 3, R: -34, odd: "17", dx: 10, dy: 18 },
  { a: 4, b: 4, R: 3, odd: "3", dx: 10, dy: -8 },
  { a: 2, b: 4, R: -53, odd: "53", dx: -10, dy: -10 },
  { a: 1, b: 5, R: 1, odd: "S: 3² · 7", dx: 10, dy: -6 },
  { a: 5, b: 1, R: 1, odd: "S: 3² · 7", dx: -10, dy: 18 },
];

const LABELS_C1010: LatticeLabel[] = [
  {
    a: 791,
    b: 812,
    R: -1,
    odd: "S: 7³ · 13 · 229 · 1009",
    highlight: true,
    dx: 12,
    dy: -18,
  },
];

function curveY(c: number, x: number): number {
  const inside = c ** 3 - x ** 3;
  if (inside <= 0) return 0;
  return inside ** (1 / 3);
}

function buildCurvePath(
  c: number,
  xMin: number,
  xMax: number,
  toX: (v: number) => number,
  toY: (v: number) => number,
  steps = 160,
): string {
  const parts: string[] = [];
  for (let i = 0; i <= steps; i++) {
    const x = xMin + ((xMax - xMin) * i) / steps;
    const y = curveY(c, x);
    if (y < 0) continue;
    parts.push(
      `${i === 0 ? "M" : "L"} ${toX(x).toFixed(2)} ${toY(y).toFixed(2)}`,
    );
  }
  return parts.join(" ");
}

export function CubeCurvePlot() {
  const [c, setC] = useState<CChoice>(5);

  const view = useMemo(() => {
    if (c === 5) {
      const continuous: ContMark[] = [
        { x: 3, y: curveY(5, 3), label: "(3, ≈4.610)", dx: 10, dy: -10 },
        { x: 4, y: curveY(5, 4), label: "(4, ≈3.936)", dx: 10, dy: 16 },
      ];
      return {
        xMin: 0,
        xMax: 5,
        yMin: 0,
        yMax: 5.2,
        labels: LABELS_C5,
        ticks: [0, 1, 2, 3, 4, 5],
        continuous,
        title: "c = 5 · n = 3",
        showAllLattice: true as boolean,
        nearMissNote: null as string | null,
      };
    }
    // Zoom near the known near-miss (791, 812). Curve and lattice differ by ~5e-7.
    return {
      xMin: 760,
      xMax: 840,
      yMin: 760,
      yMax: 840,
      labels: LABELS_C1010,
      ticks: [760, 780, 800, 820, 840],
      continuous: [] as ContMark[],
      title: "c = 1010 · zoom near (791, 812)",
      showAllLattice: false,
      nearMissNote:
        "curve at x = 791 sits at y ≈ 812 + 5×10⁻⁷ — visually on the lattice point",
    };
  }, [c]);

  const W = 640;
  const H = 520;
  const pad = { l: 48, r: 20, t: 36, b: 48 };
  const iw = W - pad.l - pad.r;
  const ih = H - pad.t - pad.b;
  const toX = (v: number) =>
    pad.l + ((v - view.xMin) / (view.xMax - view.xMin)) * iw;
  const toY = (v: number) =>
    pad.t + ih * (1 - (v - view.yMin) / (view.yMax - view.yMin));

  const pathXMax = Math.min(view.xMax, c);
  const path = buildCurvePath(
    c,
    Math.max(view.xMin, 0),
    pathXMax,
    toX,
    toY,
  );

  const gridStep = c === 5 ? 1 : 10;
  const gridXs: number[] = [];
  const gridYs: number[] = [];
  for (
    let g = Math.ceil(view.xMin / gridStep) * gridStep;
    g <= view.xMax + 1e-9;
    g += gridStep
  ) {
    gridXs.push(g);
  }
  for (
    let g = Math.ceil(view.yMin / gridStep) * gridStep;
    g <= view.yMax + 1e-9;
    g += gridStep
  ) {
    gridYs.push(g);
  }

  const faintDots: { a: number; b: number }[] = [];
  if (view.showAllLattice) {
    for (let a = 0; a <= 5; a++) {
      for (let b = 0; b <= 5; b++) {
        if (!view.labels.some((L) => L.a === a && L.b === b)) {
          faintDots.push({ a, b });
        }
      }
    }
  }

  return (
    <figure className="power-firing-chart cube-curve-plot">
      <div className="cube-curve-controls" role="group" aria-label="Choose c">
        <button
          type="button"
          className={c === 5 ? "basins-toggle on" : "basins-toggle"}
          onClick={() => setC(5)}
          aria-pressed={c === 5}
        >
          c = 5
        </button>
        <button
          type="button"
          className={c === 1010 ? "basins-toggle on" : "basins-toggle"}
          onClick={() => setC(1010)}
          aria-pressed={c === 1010}
        >
          c = 1010
        </button>
      </div>
      <svg
        viewBox={`0 0 ${W} ${H}`}
        role="img"
        aria-label={`Real curve y = (c³ − x³)^{1/3} for c = ${c}, with nearby lattice R labels`}
      >
        <title>
          Continuous cube balance y = (c³ − x³)^(1/3) vs integer lattice for c ={" "}
          {c}
        </title>

        {gridXs.map((g) => (
          <line
            key={`vx-${g}`}
            x1={toX(g)}
            y1={pad.t}
            x2={toX(g)}
            y2={pad.t + ih}
            stroke="#e6ddd0"
            strokeWidth="1"
          />
        ))}
        {gridYs.map((g) => (
          <line
            key={`hy-${g}`}
            x1={pad.l}
            y1={toY(g)}
            x2={pad.l + iw}
            y2={toY(g)}
            stroke="#e6ddd0"
            strokeWidth="1"
          />
        ))}

        <rect
          x={pad.l}
          y={pad.t}
          width={iw}
          height={ih}
          fill="none"
          stroke="#8a7a68"
          strokeWidth="1"
        />

        {view.ticks.map((t) => (
          <g key={`tick-${t}`}>
            <text
              x={toX(t)}
              y={pad.t + ih + 16}
              textAnchor="middle"
              fontSize="11"
              fill="#6b5e4e"
            >
              {t}
            </text>
            <text
              x={pad.l - 8}
              y={toY(t) + 4}
              textAnchor="end"
              fontSize="11"
              fill="#6b5e4e"
            >
              {t}
            </text>
          </g>
        ))}

        <text x={pad.l} y={18} fontSize="13" fill="#3d3428">
          {view.title} · y = (c³ − x³)
          <tspan baselineShift="super" fontSize="9">
            1/3
          </tspan>
        </text>

        <path d={path} fill="none" stroke="#1f5f8b" strokeWidth="2.25" />

        {faintDots.map((p) => (
          <circle
            key={`dot-${p.a}-${p.b}`}
            cx={toX(p.a)}
            cy={toY(p.b)}
            r="2.2"
            fill="#cfc4b4"
          />
        ))}

        {view.continuous.map((p) => {
          const dx = p.dx ?? 8;
          const dy = p.dy ?? -8;
          return (
            <g key={`cont-${p.x}`}>
              <circle
                cx={toX(p.x)}
                cy={toY(p.y)}
                r="4.5"
                fill="#faf7f1"
                stroke="#1f5f8b"
                strokeWidth="1.75"
              />
              <text
                x={toX(p.x) + dx}
                y={toY(p.y) + dy}
                textAnchor={dx < 0 ? "end" : "start"}
                fontSize="11"
                fill="#1f5f8b"
              >
                {p.label}
              </text>
            </g>
          );
        })}

        {view.labels.map((L) => {
          const cx = toX(L.a);
          const cy = toY(L.b);
          const dx = L.dx ?? 10;
          const dy = L.dy ?? -10;
          const lx = cx + dx;
          const ly = cy + dy;
          const anchor = dx < 0 ? "end" : "start";
          return (
            <g key={`lat-${L.a}-${L.b}`}>
              <circle
                cx={cx}
                cy={cy}
                r={L.highlight ? 5.5 : 4}
                fill={L.highlight ? "#b85c38" : "#3d3428"}
              />
              <text
                x={lx}
                y={ly}
                textAnchor={anchor}
                fontSize={L.highlight ? 12 : 11}
                fill="#3d3428"
                fontWeight={L.highlight ? 600 : 400}
              >
                ({L.a}, {L.b})
              </text>
              <text
                x={lx}
                y={ly + 13}
                textAnchor={anchor}
                fontSize="10"
                fill="#6b5e4e"
              >
                {fmtR(L.R)}
                {L.odd ? ` · ${L.odd}` : ""}
              </text>
            </g>
          );
        })}

        {view.nearMissNote ? (
          <text
            x={pad.l + 8}
            y={pad.t + ih - 10}
            fontSize="11"
            fill="#1f5f8b"
          >
            {view.nearMissNote}
          </text>
        ) : null}
      </svg>
      <figcaption className="figure-caption">
        Real curve balances cubes continuously; lattice points carry a signed
        mismatch R = a³ + b³ − c³ (odd factors of R, or of S = a³ + b³ when
        R = ±1). For c = 5 the n = 2 neighbour (3, 4) sits off the n = 3 curve
        at R = −34 = −2 · 17; hollow marks show the continuous positions at
        x = 3 and x = 4. For c = 1010 the near-miss 791³ + 812³ = 1010³ − 1 has
        R = −1 and S ≡ 1 (mod 3), so m₀(S) = S + 1 = 1010³ — the door names the
        neighbour. That still does not explain R = 0; continuous balance is not
        a door, and this plot is not an FLT argument.
      </figcaption>
    </figure>
  );
}
