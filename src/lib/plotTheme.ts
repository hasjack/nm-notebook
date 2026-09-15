import type { Data, Layout } from "plotly.js";
import { MARKS, ODDS, curve, locusMinusOne, walk, type Pt } from "./walk";

export const CREAM = "#f4efe6";
export const MAROON = "#9a2f38";
export const NAVY = "#1f4e79";
export const ORANGE = "#c45c26";
export const MUTED = "#7a7468";
export const PAPER = "#fffaf3";

export function ptsToXYZ(pts: Pt[]) {
  return {
    x: pts.map((p) => p.x),
    y: pts.map((p) => p.y),
    z: pts.map((p) => p.z),
  };
}

/** 3D ribbon for a fixed product α·β; orange diamond at focusBase. */
export function traces3d(product: number, focusBase: number | null): Data[] {
  const w = ptsToXYZ(walk(product));
  const mx: number[] = [];
  const my: number[] = [];
  const mz: number[] = [];
  const mt: string[] = [];
  MARKS.forEach((m) => {
    const p = curve(product, m.base);
    mx.push(p.x);
    my.push(p.y);
    mz.push(p.z);
    mt.push(m.label);
  });
  const traces: Data[] = [
    {
      type: "scatter3d",
      mode: "lines",
      x: w.x,
      y: w.y,
      z: w.z,
      line: { color: MAROON, width: 5 },
      hoverinfo: "skip",
      name: "walk",
    },
    {
      type: "scatter3d",
      mode: "text+markers",
      x: mx,
      y: my,
      z: mz,
      text: mt,
      textposition: "top center",
      marker: { size: 5, color: NAVY },
      name: "marks",
    },
  ];
  if (focusBase && focusBase > 0) {
    const f = curve(product, focusBase);
    traces.push({
      type: "scatter3d",
      mode: "markers",
      x: [f.x],
      y: [f.y],
      z: [f.z],
      marker: { size: 9, color: ORANGE, symbol: "diamond" },
      name: "focus",
    });
  }
  return traces;
}

export const layout3d: Partial<Layout> = {
  paper_bgcolor: CREAM,
  margin: { l: 0, r: 0, t: 8, b: 0 },
  showlegend: false,
  font: { family: "Georgia, Palatino, serif" },
  scene: {
    xaxis: { title: { text: "base" }, range: [0, 22] },
    yaxis: { title: { text: "real part" }, range: [-1.2, 1.2] },
    zaxis: { title: { text: "i piece" }, range: [-1.2, 1.2] },
    camera: { eye: { x: 1.55, y: 1.35, z: 0.85 } },
    aspectmode: "manual",
    aspectratio: { x: 1.4, y: 0.85, z: 0.85 },
  },
};

export type FactorAxis = "pi-factor" | "i-factor" | "product";

const factorAxisLabel: Record<FactorAxis, string> = {
  "pi-factor": "π-factor β",
  "i-factor": "i-factor α",
  product: "α · β",
};

/**
 * −1 locus: factor · ln(base) = odd.
 * y-axis is the free factor (β under lock-i, α under lock-π).
 */
export function traces2d(
  activeOdd: number,
  curU: number | null,
  curFactor: number | null,
  axis: FactorAxis = "product"
): Data[] {
  const yName = factorAxisLabel[axis];
  const traces: Data[] = ODDS.map((odd) => {
    const L = locusMinusOne(odd);
    return {
      type: "scatter",
      mode: "lines",
      x: L.u,
      y: L.factor,
      line: {
        width: odd === activeOdd ? 3 : 1.2,
        color: odd === activeOdd ? MAROON : "#c4b8a4",
      },
      name: "odd " + odd,
      hovertemplate:
        "ln base=%{x:.3f}<br>" + yName + "=%{y:.3f}<extra>odd " + odd + "</extra>",
    };
  });
  if (curU != null && curFactor != null && Number.isFinite(curFactor)) {
    traces.push({
      type: "scatter",
      mode: "markers",
      x: [curU],
      y: [curFactor],
      marker: { size: 11, color: ORANGE, symbol: "diamond" },
      name: "now",
      hovertemplate:
        "ln base=%{x:.3f}<br>" + yName + "=%{y:.3f}<extra>now</extra>",
    });
  }
  traces.push({
    type: "scatter",
    mode: "lines",
    x: [1, 1],
    y: [-6, 6],
    line: { color: NAVY, width: 1, dash: "dot" },
    hoverinfo: "skip",
    name: "ln e = 1",
  });
  return traces;
}

export function layout2d(axis: FactorAxis = "product"): Partial<Layout> {
  const yTitle = factorAxisLabel[axis];
  return {
    paper_bgcolor: CREAM,
    plot_bgcolor: PAPER,
    margin: { l: 50, r: 20, t: 28, b: 45 },
    title: {
      text: `−1 locus: ${yTitle} · ln(base) = odd`,
      font: { size: 13, family: "Georgia, serif" },
    },
    xaxis: {
      title: { text: "ln(base)  (powers of e)" },
      range: [Math.log(0.05), Math.log(22)],
      zeroline: true,
    },
    yaxis: { title: { text: yTitle }, range: [-4, 4], zeroline: true },
    showlegend: false,
    font: { family: "Georgia, Palatino, serif" },
    annotations: [
      {
        x: 1,
        y: 1,
        text: "Euler point",
        showarrow: true,
        arrowhead: 2,
        ax: 40,
        ay: -30,
        font: { size: 11, color: NAVY },
      },
    ],
  };
}

export const plotConfig = { responsive: true, displayModeBar: false as const };
