import { useMemo, useState } from "react";
import { Link } from "react-router-dom";
import type { Data, Layout } from "plotly.js";
import Plot from "../components/Plot";
import {
  CREAM,
  MAROON,
  NAVY,
  PAPER,
  plotConfig,
} from "../lib/plotTheme";

const GREEN = "#2f6b4f";
const ORANGE = "#c45c26";
const GOLD = "#d4a017";
const MUTED_LINE = "#7a7468";

function primesUpTo(n: number): number[] {
  if (n < 2) return [];
  const sieve = new Uint8Array(n + 1);
  sieve.fill(1);
  sieve[0] = 0;
  sieve[1] = 0;
  for (let i = 2; i * i <= n; i++) {
    if (!sieve[i]) continue;
    for (let j = i * i; j <= n; j += i) sieve[j] = 0;
  }
  const out: number[] = [];
  for (let i = 2; i <= n; i++) if (sieve[i]) out.push(i);
  return out;
}

function oddPrimesTo(n: number): number[] {
  return primesUpTo(n).filter((p) => p % 2 === 1);
}

/** 3-free door neighbour: p + χ₃(p). */
function doorOf(p: number): number {
  if (p % 3 === 1) return p + 1;
  if (p % 3 === 2) return p - 1;
  return p; // p = 3: no door in this recipe
}

function factorOddPrimes(n: number): number[] {
  return [...new Set(factorParts(n).filter((q) => q !== 2))];
}

type DoorRow = {
  p: number;
  left: number;
  right: number;
  door: number | null;
  sacked: boolean;
  doorFactors: number[];
  sink: boolean;
};

function doorRowsTo(n: number): DoorRow[] {
  return oddPrimesTo(n).map((p) => {
    const left = p - 1;
    const right = p + 1;
    if (p === 3) {
      return {
        p,
        left,
        right,
        door: null,
        sacked: true,
        doorFactors: [],
        sink: false,
      };
    }
    const door = doorOf(p);
    const doorFactors = factorOddPrimes(door);
    return {
      p,
      left,
      right,
      door,
      sacked: false,
      doorFactors,
      sink: doorFactors.length === 0,
    };
  });
}


function factorParts(n: number): number[] {
  const parts: number[] = [];
  let x = Math.abs(n);
  for (let d = 2; d * d <= x; d++) {
    while (x % d === 0) {
      parts.push(d);
      x = Math.floor(x / d);
    }
  }
  if (x > 1) parts.push(x);
  return parts;
}

function uniq(a: number[]): number[] {
  return [...new Set(a)];
}

/** Unique ±1 door (fire 3). Mod-6 law. */
function legalM(p: number): { m: number; door: 1 | -1 } {
  if (p === 3) return { m: 2, door: 1 };
  if (p % 6 === 5) return { m: p - 1, door: 1 };
  return { m: p + 1, door: -1 };
}

function walkHire(N: number) {
  const S = new Set<number>([2]);
  const hireAt = new Map<number, number>([[2, 2]]);
  const growth: { at: number; size: number }[] = [];
  const events: { p: number; neu: number[]; size: number }[] = [];
  for (const p of primesUpTo(N).filter((x) => x >= 3)) {
    const { m } = legalM(p);
    const neu: number[] = [];
    for (const q of uniq(factorParts(m))) {
      if (!S.has(q)) {
        S.add(q);
        hireAt.set(q, p);
        neu.push(q);
      }
    }
    if (neu.length) {
      neu.sort((a, b) => a - b);
      events.push({ p, neu, size: S.size });
    }
    growth.push({ at: p, size: S.size });
  }
  return {
    S: [...S].sort((a, b) => a - b),
    hireAt,
    growth,
    events,
  };
}

/** Sack-5 door (E): prefer 3-free m; if that m carries 5, flip to the ×3 neighbour. Hire 3 when used; never hire 5. */
function legalMSack5(p: number): { m: number; door: 1 | -1; flipped: boolean } {
  if (p === 3) return { m: 2, door: 1, flipped: false };
  const base = legalM(p);
  const freeHas5 = uniq(factorParts(base.m)).includes(5);
  if (!freeHas5) return { m: base.m, door: base.door, flipped: false };
  const m = base.door === 1 ? p + 1 : p - 1;
  const door: 1 | -1 = base.door === 1 ? -1 : 1;
  return { m, door, flipped: true };
}

function walkHireSack5(N: number) {
  const S = new Set<number>([2]);
  const hireAt = new Map<number, number>([[2, 2]]);
  const growth: { at: number; size: number }[] = [];
  const events: { p: number; neu: number[]; size: number }[] = [];
  let flips = 0;
  for (const p of primesUpTo(N).filter((x) => x >= 3)) {
    if (p === 3) {
      growth.push({ at: p, size: S.size });
      continue;
    }
    const { m, flipped } = legalMSack5(p);
    if (flipped) flips += 1;
    const neu: number[] = [];
    for (const q of uniq(factorParts(m))) {
      if (q === 5) continue; // sacked completely
      // 3 stands in when the flip midrange uses it
      if (!S.has(q)) {
        S.add(q);
        hireAt.set(q, p);
        neu.push(q);
      }
    }
    if (neu.length) {
      neu.sort((a, b) => a - b);
      events.push({ p, neu, size: S.size });
    }
    growth.push({ at: p, size: S.size });
  }
  return {
    S: [...S].sort((a, b) => a - b),
    hireAt,
    growth,
    events,
    flips,
  };
}


type Adj = Map<number, Set<number>>;

function buildGraph(nodes: number[]): Adj {
  const set = new Set(nodes);
  const adj: Adj = new Map(nodes.map((n) => [n, new Set<number>()]));
  const link = (a: number, b: number) => {
    if (a === b || !set.has(a) || !set.has(b)) return;
    adj.get(a)!.add(b);
    adj.get(b)!.add(a);
  };
  for (const s of nodes) {
    if (s === 2) continue;
    const { m } = legalM(s);
    for (const q of uniq(factorParts(m))) link(s, q);
  }
  return adj;
}

function buildGraphSack5(nodes: number[]): Adj {
  const set = new Set(nodes);
  const adj: Adj = new Map(nodes.map((n) => [n, new Set<number>()]));
  const link = (a: number, b: number) => {
    if (a === b || !set.has(a) || !set.has(b)) return;
    adj.get(a)!.add(b);
    adj.get(b)!.add(a);
  };
  for (const s of nodes) {
    if (s === 2) continue;
    const { m } = legalMSack5(s);
    for (const q of uniq(factorParts(m))) {
      if (q === 5) continue; // sacked — not a vertex
      link(s, q);
    }
  }
  return adj;
}


function edgeCount(adj: Adj, nodes: number[]): number {
  let e = 0;
  for (const a of nodes) for (const b of adj.get(a)!) if (b > a) e++;
  return e;
}

function nullStar(nodes: number[], extraCount: number, seed: number): Adj {
  let s = seed >>> 0;
  const rand = () => {
    s = (Math.imul(s, 1664525) + 1013904223) >>> 0;
    return s / 2 ** 32;
  };
  const adj: Adj = new Map(nodes.map((n) => [n, new Set<number>()]));
  const link = (a: number, b: number) => {
    adj.get(a)!.add(b);
    adj.get(b)!.add(a);
  };
  for (const n of nodes) if (n !== 2) link(2, n);
  const others = nodes.filter((n) => n !== 2);
  const possible: [number, number][] = [];
  for (let i = 0; i < others.length; i++)
    for (let j = i + 1; j < others.length; j++)
      possible.push([others[i], others[j]]);
  for (let i = possible.length - 1; i > 0; i--) {
    const j = Math.floor(rand() * (i + 1));
    const tmp = possible[i];
    possible[i] = possible[j];
    possible[j] = tmp;
  }
  for (let i = 0; i < Math.min(extraCount, possible.length); i++)
    link(possible[i][0], possible[i][1]);
  return adj;
}

function laplacianEigs(nodes: number[], adj: Adj): number[] {
  const k = nodes.length;
  if (k === 0) return [];
  const idx = new Map(nodes.map((n, i) => [n, i]));
  const M = Array.from({ length: k }, () => Array(k).fill(0));
  for (const a of nodes) {
    const i = idx.get(a)!;
    const nbr = [...adj.get(a)!];
    M[i][i] = nbr.length;
    for (const b of nbr) M[i][idx.get(b)!] = -1;
  }
  for (let iter = 0; iter < 600; iter++) {
    let p = 0;
    let q = 1;
    let max = 0;
    for (let i = 0; i < k; i++) {
      for (let j = i + 1; j < k; j++) {
        const v = Math.abs(M[i][j]);
        if (v > max) {
          max = v;
          p = i;
          q = j;
        }
      }
    }
    if (max < 1e-14) break;
    const app = M[p][p];
    const aqq = M[q][q];
    const apq = M[p][q];
    const tau = (aqq - app) / (2 * apq);
    const t =
      (tau >= 0 ? 1 : -1) / (Math.abs(tau) + Math.sqrt(1 + tau * tau));
    const c = 1 / Math.sqrt(1 + t * t);
    const s = t * c;
    for (let i = 0; i < k; i++) {
      if (i === p || i === q) continue;
      const aip = M[i][p];
      const aiq = M[i][q];
      M[i][p] = M[p][i] = c * aip - s * aiq;
      M[i][q] = M[q][i] = s * aip + c * aiq;
    }
    M[p][p] = app - t * apq;
    M[q][q] = aqq + t * apq;
    M[p][q] = M[q][p] = 0;
  }
  return M.map((r, i) => r[i]).sort((a, b) => a - b);
}

const DEFAULT_N = 200;

export function HireSpectrumPage() {
  const [N, setN] = useState(DEFAULT_N);
  const [viewMin, setViewMin] = useState(0);
  const [viewMax, setViewMax] = useState(DEFAULT_N);

  const model = useMemo(() => {
    const growthN = Math.min(N, 10000);
    const graphN = Math.min(N, 800);
    const { S: Sfull, growth, events, hireAt } = walkHire(growthN);
    const { S } = walkHire(graphN);
    const adj = buildGraph(S);
    const eigs = laplacianEigs(S, adj);
    const deg = S.map((n) => ({ n, d: adj.get(n)!.size })).sort(
      (a, b) => b.d - a.d || a.n - b.n
    );
    const totalE = edgeCount(adj, S);
    const extra = totalE - (S.length - 1);
    const nullRuns = 24;
    const nullStats: {
      bottom: number;
      top: number;
      midMax: number;
      max: number;
    }[] = [];
    for (let i = 0; i < nullRuns; i++) {
      const nadj = nullStar(S, extra, 1000 + i * 97);
      const ne = laplacianEigs(S, nadj);
      const mid =
        ne.length > 2 ? Math.max(...ne.slice(1, -1)) : ne[1] ?? 0;
      nullStats.push({
        bottom: ne[1] - ne[0],
        top: ne[ne.length - 1] - ne[ne.length - 2],
        midMax: mid,
        max: ne[ne.length - 1],
      });
    }
    const mean = (xs: number[]) =>
      xs.reduce((a, b) => a + b, 0) / Math.max(1, xs.length);
    const midHire =
      eigs.length > 2 ? Math.max(...eigs.slice(1, -1)) : eigs[1] ?? 0;
    // growth samples
    const xs: number[] = [];
    for (let x = 20; x <= growthN; ) {
      xs.push(x);
      if (x < 200) x += 20;
      else if (x < 1000) x += 50;
      else if (x < 4000) x += 100;
      else x += 200;
    }
    if (!xs.includes(growthN)) xs.push(growthN);
    const yS = xs.map((x) => {
      let s = 1;
      for (const g of growth) {
        if (g.at <= x) s = g.size;
        else break;
      }
      return s;
    });
    const yPi = xs.map((x) => primesUpTo(x).length);

    // sun layout for S at graphN
    const hubs = deg.filter((d) => d.n !== 2).slice(0, 6).map((d) => d.n);
    const hubSet = new Set(hubs);
    const pos = new Map<number, { x: number; y: number }>();
    pos.set(2, { x: 0, y: 0 });
    const others = S.filter((n) => n !== 2);
    others.forEach((n, i) => {
      const ang = (2 * Math.PI * i) / others.length - Math.PI / 2;
      const r = hubSet.has(n) ? 1.0 : 1.55;
      pos.set(n, { x: r * Math.cos(ang), y: r * Math.sin(ang) });
    });
    const edgeSegs: { x0: number; y0: number; x1: number; y1: number; gold: boolean }[] = [];
    for (const a of S) {
      for (const b of adj.get(a)!) {
        if (b <= a) continue;
        const pa = pos.get(a)!;
        const pb = pos.get(b)!;
        const gold = a !== 2 && b !== 2;
        edgeSegs.push({
          x0: pa.x,
          y0: pa.y,
          x1: pb.x,
          y1: pb.y,
          gold,
        });
      }
    }


    // Staircase: |S| as step function of walk prime p; hire map q → H(q)
    const stairX: number[] = [0];
    const stairY: number[] = [1];
    let lastSize = 1;
    for (const g of growth) {
      stairX.push(g.at, g.at);
      stairY.push(lastSize, g.size);
      lastSize = g.size;
    }
    const hireQs: number[] = [];
    const hireHs: number[] = [];
    const hireThin: boolean[] = [];
    for (const [q, h] of hireAt.entries()) {
      if (q === 2) continue;
      hireQs.push(q);
      hireHs.push(h);
      hireThin.push(h <= 2 * q + 3);
    }
    return {
      growthN,
      graphN,
      Sfull,
      S,
      growth,
      deg,
      eigs,
      extra,
      totalE,
      midHire,
      bottomGap: eigs.length > 1 ? eigs[1] - eigs[0] : 0,
      topGap:
        eigs.length > 1
          ? eigs[eigs.length - 1] - eigs[eigs.length - 2]
          : 0,
      lambdaMax: eigs.length ? eigs[eigs.length - 1] : 0,
      nullBottom: mean(nullStats.map((r) => r.bottom)),
      nullTop: mean(nullStats.map((r) => r.top)),
      nullMid: mean(nullStats.map((r) => r.midMax)),
      nullMax: mean(nullStats.map((r) => r.max)),
      xs,
      yS,
      yPi,
      pos,
      hubs,
      edgeSegs,
      sizeAtN: growth.length ? growth[growth.length - 1].size : 1,
      stairX,
      stairY,
      hireQs,
      hireHs,
      hireThin,
      eventsHead: events.slice(0, 16),
      thinCount: hireThin.filter(Boolean).length,
      lateCount: hireThin.filter((x) => !x).length,
    };
  }, [N]);

  /** Sack-5 hire-sun + H (same caps as standing sun). */
  const sack5 = useMemo(() => {
    const growthN = Math.min(N, 10000);
    const graphN = Math.min(N, 800);
    const walked = walkHireSack5(growthN);
    const { S } = walkHireSack5(graphN);
    const adj = buildGraphSack5(S);
    const eigs = laplacianEigs(S, adj);
    const deg = S.map((n) => ({ n, d: adj.get(n)!.size })).sort(
      (a, b) => b.d - a.d || a.n - b.n,
    );
    const totalE = edgeCount(adj, S);
    const extra = totalE - (S.length - 1);
    const nullRuns = 24;
    const nullStats: {
      bottom: number;
      top: number;
      midMax: number;
      max: number;
    }[] = [];
    for (let i = 0; i < nullRuns; i++) {
      const nadj = nullStar(S, extra, 2000 + i * 97);
      const ne = laplacianEigs(S, nadj);
      const mid =
        ne.length > 2 ? Math.max(...ne.slice(1, -1)) : ne[1] ?? 0;
      nullStats.push({
        bottom: ne[1] - ne[0],
        top: ne[ne.length - 1] - ne[ne.length - 2],
        midMax: mid,
        max: ne[ne.length - 1],
      });
    }
    const mean = (xs: number[]) =>
      xs.reduce((a, b) => a + b, 0) / Math.max(1, xs.length);
    const midHire =
      eigs.length > 2 ? Math.max(...eigs.slice(1, -1)) : eigs[1] ?? 0;

    const hubs = deg.filter((d) => d.n !== 2).slice(0, 6).map((d) => d.n);
    const hubSet = new Set(hubs);
    const pos = new Map<number, { x: number; y: number }>();
    pos.set(2, { x: 0, y: 0 });
    const others = S.filter((n) => n !== 2);
    others.forEach((n, i) => {
      const ang = (2 * Math.PI * i) / Math.max(1, others.length) - Math.PI / 2;
      const r = hubSet.has(n) ? 1.0 : 1.55;
      pos.set(n, { x: r * Math.cos(ang), y: r * Math.sin(ang) });
    });
    const edgeSegs: {
      x0: number;
      y0: number;
      x1: number;
      y1: number;
      gold: boolean;
    }[] = [];
    for (const a of S) {
      for (const b of adj.get(a)!) {
        if (b <= a) continue;
        const pa = pos.get(a)!;
        const pb = pos.get(b)!;
        edgeSegs.push({
          x0: pa.x,
          y0: pa.y,
          x1: pb.x,
          y1: pb.y,
          gold: a !== 2 && b !== 2,
        });
      }
    }

    return {
      growthN,
      graphN,
      S,
      flips: walked.flips,
      sizeAtN: walked.growth.length
        ? walked.growth[walked.growth.length - 1].size
        : 1,
      deg,
      eigs,
      extra,
      totalE,
      midHire,
      bottomGap: eigs.length > 1 ? eigs[1] - eigs[0] : 0,
      topGap:
        eigs.length > 1
          ? eigs[eigs.length - 1] - eigs[eigs.length - 2]
          : 0,
      lambdaMax: eigs.length ? eigs[eigs.length - 1] : 0,
      nullBottom: mean(nullStats.map((r) => r.bottom)),
      nullTop: mean(nullStats.map((r) => r.top)),
      nullMid: mean(nullStats.map((r) => r.midMax)),
      nullMax: mean(nullStats.map((r) => r.max)),
      pos,
      hubs,
      edgeSegs,
    };
  }, [N]);

  const vMin = Math.max(0, Math.min(viewMin, N));
  const vMax = Math.max(vMin + 1, Math.min(viewMax, N));

  const growthData: Data[] = useMemo(
    () => [
      {
        type: "scatter",
        mode: "lines+markers",
        name: "|S| after walk to X",
        x: model.xs,
        y: model.yS,
        line: { color: MAROON },
      },
      {
        type: "scatter",
        mode: "lines",
        name: "π(X) all primes",
        x: model.xs,
        y: model.yPi,
        line: { color: NAVY, dash: "dot" },
      },
    ],
    [model]
  );

  const growthLayout: Partial<Layout> = {
    paper_bgcolor: CREAM,
    plot_bgcolor: PAPER,
    margin: { l: 50, r: 20, t: 40, b: 45 },
    title: {
      text: `|S| growth (walk to ${model.growthN}) — hiring, not a freeze`,
      font: { size: 13, family: "Georgia, serif" },
    },
    xaxis: { title: { text: "X" } },
    yaxis: { title: { text: "count" }, rangemode: "tozero" },
    legend: { orientation: "h", y: -0.22 },
    font: { family: "Georgia, Palatino, serif" },
  };


  const stairData: Data[] = useMemo(() => {
    const xs: number[] = [];
    const ys: number[] = [];
    for (let i = 0; i < model.stairX.length; i++) {
      const x = model.stairX[i];
      if (x < vMin || x > vMax) continue;
      xs.push(x);
      ys.push(model.stairY[i]);
    }
    // anchor left edge of window at last size before vMin
    let y0 = 1;
    for (let i = 0; i < model.stairX.length; i++) {
      if (model.stairX[i] <= vMin) y0 = model.stairY[i];
      else break;
    }
    if (xs.length === 0 || xs[0] > vMin) {
      xs.unshift(vMin);
      ys.unshift(y0);
    }
    return [
      {
        type: "scatter" as const,
        mode: "lines" as const,
        name: "|S| staircase",
        x: xs,
        y: ys,
        line: { color: MAROON, width: 2, shape: "hv" as const },
      },
    ];
  }, [model, vMin, vMax]);

  const stairLayout: Partial<Layout> = {
    paper_bgcolor: CREAM,
    plot_bgcolor: PAPER,
    margin: { l: 50, r: 20, t: 40, b: 45 },
    title: {
      text: `Hiring staircase — window [${vMin}, ${vMax}]`,
      font: { size: 13, family: "Georgia, serif" },
    },
    xaxis: { title: { text: "walk prime p" }, range: [vMin, vMax] },
    yaxis: { title: { text: "|S|" }, rangemode: "tozero" },
    font: { family: "Georgia, Palatino, serif" },
  };

  const scheduleData: Data[] = useMemo(() => {
    const inWin = (h: number) => h >= vMin && h <= vMax;
    const thinX: number[] = [];
    const thinY: number[] = [];
    const lateX: number[] = [];
    const lateY: number[] = [];
    for (let i = 0; i < model.hireHs.length; i++) {
      const h = model.hireHs[i];
      const q = model.hireQs[i];
      if (!inWin(h)) continue;
      if (model.hireThin[i]) {
        thinX.push(h);
        thinY.push(q);
      } else {
        lateX.push(h);
        lateY.push(q);
      }
    }
    return [
      {
        type: "scatter" as const,
        mode: "markers" as const,
        name: "thin door (~2q±1)",
        x: thinX,
        y: thinY,
        marker: { size: 8, color: GOLD },
        hovertemplate: "hire %{y} at p=%{x}<extra></extra>",
      },
      {
        type: "scatter" as const,
        mode: "markers" as const,
        name: "later hire",
        x: lateX,
        y: lateY,
        marker: { size: 8, color: NAVY },
        hovertemplate: "hire %{y} at p=%{x}<extra></extra>",
      },
      {
        type: "scatter" as const,
        mode: "lines" as const,
        name: "H=q (immediate)",
        x: [vMin, vMax],
        y: [vMin, vMax],
        line: { color: MUTED_LINE, dash: "dot", width: 1 },
        hoverinfo: "skip" as const,
      },
      {
        type: "scatter" as const,
        mode: "lines" as const,
        name: "H=2q (thin door)",
        x: [vMin, vMax],
        y: [vMin / 2, vMax / 2],
        line: { color: ORANGE, dash: "dash", width: 1 },
        hoverinfo: "skip" as const,
      },
      {
        type: "scatter" as const,
        mode: "lines" as const,
        name: "H=4q (2²·q door)",
        x: [vMin, vMax],
        y: [vMin / 4, vMax / 4],
        line: { color: NAVY, dash: "dot", width: 1 },
        hoverinfo: "skip" as const,
      },
      {
        type: "scatter" as const,
        mode: "lines" as const,
        name: "H=8q (2³·q door)",
        x: [vMin, vMax],
        y: [vMin / 8, vMax / 8],
        line: { color: GREEN, dash: "dot", width: 1 },
        hoverinfo: "skip" as const,
      },
      {
        type: "scatter" as const,
        mode: "lines" as const,
        name: "H=10q (2·5·q)",
        x: [vMin, vMax],
        y: [vMin / 10, vMax / 10],
        line: { color: MUTED_LINE, dash: "dot", width: 1 },
        hoverinfo: "skip" as const,
      },
      {
        type: "scatter" as const,
        mode: "lines" as const,
        name: "H=16q (2⁴·q)",
        x: [vMin, vMax],
        y: [vMin / 16, vMax / 16],
        line: { color: "#8b6b9f", dash: "dot", width: 1 },
        hoverinfo: "skip" as const,
      },
    ];
  }, [model, vMin, vMax]);

  const scheduleLayout: Partial<Layout> = {
    paper_bgcolor: CREAM,
    plot_bgcolor: PAPER,
    margin: { l: 50, r: 20, t: 40, b: 50 },
    title: {
      text: `Hire schedule — H(q) in [${vMin}, ${vMax}]`,
      font: { size: 13, family: "Georgia, serif" },
    },
    xaxis: {
      title: { text: "H(q) = first p that hires q" },
      range: [vMin, vMax],
    },
    yaxis: { title: { text: "prime q hired" }, rangemode: "tozero" },
    legend: { orientation: "h", y: -0.28 },
    font: { family: "Georgia, Palatino, serif" },
  };

  const degData: Data[] = useMemo(
    () => [
      {
        type: "bar",
        x: model.deg.slice(0, 12).map((d) => String(d.n)),
        y: model.deg.slice(0, 12).map((d) => d.d),
        marker: {
          color: model.deg
            .slice(0, 12)
            .map((d) =>
              d.n === 2 ? "#f5f0e6" : model.hubs.includes(d.n) ? ORANGE : NAVY
            ),
        },
      },
    ],
    [model]
  );

  const degLayout: Partial<Layout> = {
    paper_bgcolor: CREAM,
    plot_bgcolor: PAPER,
    margin: { l: 45, r: 20, t: 36, b: 50 },
    title: {
      text: `Degree on hire-graph (sites = S through ${model.graphN})`,
      font: { size: 13, family: "Georgia, serif" },
    },
    yaxis: { title: { text: "degree" }, rangemode: "tozero" },
    font: { family: "Georgia, Palatino, serif" },
  };

  const eigData: Data[] = useMemo(
    () => [
      {
        type: "scatter",
        mode: "markers+lines",
        name: "hire Laplacian",
        x: model.eigs.map((_, i) => i),
        y: model.eigs,
        marker: { size: 7, color: GOLD },
        line: { color: GOLD, width: 1 },
      },
    ],
    [model]
  );

  const eigLayout: Partial<Layout> = {
    paper_bgcolor: CREAM,
    plot_bgcolor: PAPER,
    margin: { l: 50, r: 20, t: 40, b: 45 },
    title: {
      text: "Spectrum of graph Laplacian H (no zeta fitting)",
      font: { size: 13, family: "Georgia, serif" },
    },
    xaxis: { title: { text: "index" } },
    yaxis: { title: { text: "λ" }, rangemode: "tozero" },
    font: { family: "Georgia, Palatino, serif" },
    shapes: [
      {
        type: "line",
        x0: -0.5,
        x1: model.eigs.length - 0.5,
        y0: 1,
        y1: 1,
        line: { color: MUTED_LINE, dash: "dot", width: 1 },
      },
    ],
    annotations: [
      {
        x: model.eigs.length * 0.15,
        y: 1,
        text: "bottom gap ~ 1 (tone)",
        showarrow: false,
        yshift: 12,
        font: { size: 11, color: MUTED_LINE },
      },
    ],
  };

  const sunEdgeGold: Data = {
    type: "scatter",
    mode: "lines",
    name: "gold hire chords",
    x: model.edgeSegs.filter((e) => e.gold).flatMap((e) => [e.x0, e.x1, null]),
    y: model.edgeSegs.filter((e) => e.gold).flatMap((e) => [e.y0, e.y1, null]),
    line: { color: GOLD, width: 2 },
    hoverinfo: "skip",
  };
  const sunEdgeSpoke: Data = {
    type: "scatter",
    mode: "lines",
    name: "spokes to 2",
    x: model.edgeSegs.filter((e) => !e.gold).flatMap((e) => [e.x0, e.x1, null]),
    y: model.edgeSegs.filter((e) => !e.gold).flatMap((e) => [e.y0, e.y1, null]),
    line: { color: "#4a6a8a", width: 1 },
    hoverinfo: "skip",
  };
  const sunNodes: Data = {
    type: "scatter",
    mode: "markers+text",
    name: "S",
    x: model.S.map((n) => model.pos.get(n)!.x),
    y: model.S.map((n) => model.pos.get(n)!.y),
    text: model.S.map(String),
    textposition: "top center",
    textfont: { size: 10, color: "#e8e0d0" },
    marker: {
      size: model.S.map((n) => (n === 2 ? 18 : model.hubs.includes(n) ? 14 : 10)),
      color: model.S.map((n) =>
        n === 2 ? "#f5f0e6" : model.hubs.includes(n) ? ORANGE : "#5b8ab8"
      ),
      line: { width: 1, color: "#1a2744" },
    },
    hovertemplate: "%{text}<extra></extra>",
  };

  const sunLayout: Partial<Layout> = {
    paper_bgcolor: "#0f1c2e",
    plot_bgcolor: "#0f1c2e",
    margin: { l: 20, r: 20, t: 40, b: 40 },
    title: {
      text: `Hire-sun through ${model.graphN}`,
      font: { size: 13, family: "Georgia, serif", color: "#e8e0d0" },
    },
    xaxis: { visible: false, scaleanchor: "y", scaleratio: 1 },
    yaxis: { visible: false },
    showlegend: true,
    legend: {
      orientation: "h",
      y: -0.12,
      font: { color: "#c8c0b0", size: 10 },
    },
    font: { family: "Georgia, Palatino, serif", color: "#e8e0d0" },
  };

  const sack5SunEdgeGold: Data = {
    type: "scatter",
    mode: "lines",
    name: "gold hire chords",
    x: sack5.edgeSegs.filter((e) => e.gold).flatMap((e) => [e.x0, e.x1, null]),
    y: sack5.edgeSegs.filter((e) => e.gold).flatMap((e) => [e.y0, e.y1, null]),
    line: { color: GOLD, width: 2 },
    hoverinfo: "skip",
  };
  const sack5SunEdgeSpoke: Data = {
    type: "scatter",
    mode: "lines",
    name: "spokes to 2",
    x: sack5.edgeSegs.filter((e) => !e.gold).flatMap((e) => [e.x0, e.x1, null]),
    y: sack5.edgeSegs.filter((e) => !e.gold).flatMap((e) => [e.y0, e.y1, null]),
    line: { color: "#4a6a8a", width: 1 },
    hoverinfo: "skip",
  };
  const sack5SunNodes: Data = {
    type: "scatter",
    mode: "markers+text",
    name: "S (no 5; 3 stands in)",
    x: sack5.S.map((n) => sack5.pos.get(n)!.x),
    y: sack5.S.map((n) => sack5.pos.get(n)!.y),
    text: sack5.S.map(String),
    textposition: "top center",
    textfont: { size: 10, color: "#e8e0d0" },
    marker: {
      size: sack5.S.map((n) =>
        n === 2 ? 18 : n === 3 ? 16 : sack5.hubs.includes(n) ? 14 : 10,
      ),
      color: sack5.S.map((n) =>
        n === 2
          ? "#f5f0e6"
          : n === 3
            ? ORANGE
            : sack5.hubs.includes(n)
              ? ORANGE
              : "#5b8ab8",
      ),
      line: { width: 1, color: "#1a2744" },
    },
    hovertemplate: "%{text}<extra></extra>",
  };
  const sack5SunLayout: Partial<Layout> = {
    paper_bgcolor: "#0f1c2e",
    plot_bgcolor: "#0f1c2e",
    margin: { l: 20, r: 20, t: 40, b: 40 },
    title: {
      text: `E · sack {5} sun through ${sack5.graphN} (3 stands in for 5)`,
      font: { size: 13, family: "Georgia, serif", color: "#e8e0d0" },
    },
    xaxis: { visible: false, scaleanchor: "y", scaleratio: 1 },
    yaxis: { visible: false },
    showlegend: true,
    legend: {
      orientation: "h",
      y: -0.12,
      font: { color: "#c8c0b0", size: 10 },
    },
    font: { family: "Georgia, Palatino, serif", color: "#e8e0d0" },
  };


  return (
    <main className="page hire-spectrum-page lab-note-page">
      <h1>Spectrum</h1>
      <p className="lede">
        Hire-sun recipes and interactive lab dials — growth, staircase, schedule,
        and sack-5 spectra. Handshake lives on 
        <Link to="/hire">Introduction</Link>; the rate table is on 
        <Link to="/hire-lab">Hire rate</Link>.
      </p>

      <section className="hire-intro">
        <h2>Hire-sun H</h2>
        <p>
          Three recipes, same Laplacian idea. <strong>A</strong> is standing
          3-free (5 in the chair; 3 never a vertex). <strong>E</strong> sacks{" "}
          {"{5}"} — when the free door would carry 5, flip to the ×3 neighbour
          and let 3 stand in. <strong>F</strong> sacks {"{5,7}"} and punches
          holes: some covers get stuck (red rims) and only re-enter if a later
          factor uses them.
        </p>
      </section>

      <figure className="figure-block">
        <img
          src="/figures/hire/H_recipes_sun100.png"
          alt="Hire-sun H recipes A, E, and F through 100"
        />
        <figcaption className="figure-caption">
          A / E / F hire-sun recipes through 100. White hub is 2; orange is early
          crew; blue later hires; gold chords are the undirected hire wires in{" "}
          <em>H</em>.
        </figcaption>
      </figure>

      <div className="figure-grid">
        <figure className="figure-block">
          <img
            src="/figures/hire/H_standing_sun100.png"
            alt="Standing recipe A hire-sun H through 100"
          />
          <figcaption className="figure-caption">
            A · standing 3-free door (5 in the chair), H through 100.
          </figcaption>
        </figure>
        <figure className="figure-block">
          <img
            src="/figures/hire/H_sack5_sun100.png"
            alt="Sack-5 recipe E hire-sun H through 100"
          />
          <figcaption className="figure-caption">
            E · sack {"{5}"} — 3 stands in for 5, H through 100.
          </figcaption>
        </figure>
        <figure className="figure-block">
          <img
            src="/figures/hire/H_sack57_sun100.png"
            alt="Sack-5-and-7 recipe F hire-sun H through 100"
          />
          <figcaption className="figure-caption">
            F · sack {"{5,7}"} — holes show as stuck covers, H through 100.
          </figcaption>
        </figure>
      </div>

      <h2>Lab dials</h2>
      <p className="hint" style={{ marginTop: 0 }}>
        Interactive growth, staircase, schedule, hire-sun, and E · sack {"{5}"}{" "}
        spectra. Scrub N and the view window; readouts update live.
      </p>

      <div className="split-readout">
        <div>
          <div className="kv-label">N (dial)</div>
          <div className="kv-value">{N}</div>
        </div>
        <div>
          <div className="kv-label">|S| @ growth</div>
          <div className="kv-value">{model.sizeAtN}</div>
        </div>
        <div>
          <div className="kv-label">bottom gap</div>
          <div className="kv-value" style={{ color: GREEN }}>
            {model.bottomGap.toFixed(3)}
          </div>
        </div>
        <div>
          <div className="kv-label">λ_max ≈ |S|</div>
          <div className="kv-value">{model.lambdaMax.toFixed(2)}</div>
        </div>
      </div>

      <div className="panel">
        <label className="row">
          <span>N — walk depth (growth ≤10000, graph/H ≤800)</span>
          <span>{N}</span>
        </label>
        <input
          type="range"
          min={50}
          max={10000}
          step={10}
          value={N}
          onChange={(e) => {
            const next = parseInt(e.target.value, 10);
            setN(next);
            setViewMax((vm) => Math.min(Math.max(vm, 50), next));
            setViewMin((vn) => Math.min(vn, next - 1));
          }}
        />
        <label className="row">
          <span>view from (staircase / schedule window)</span>
          <span>{vMin}</span>
        </label>
        <input
          type="range"
          min={0}
          max={Math.max(0, N - 1)}
          step={1}
          value={vMin}
          onChange={(e) => {
            const next = parseInt(e.target.value, 10);
            setViewMin(next);
            setViewMax((vm) => Math.max(vm, next + 1));
          }}
        />
        <label className="row">
          <span>view to</span>
          <span>{vMax}</span>
        </label>
        <input
          type="range"
          min={Math.min(N, vMin + 1)}
          max={N}
          step={1}
          value={vMax}
          onChange={(e) => setViewMax(parseInt(e.target.value, 10))}
        />
        <p className="hint" style={{ marginTop: "0.5rem" }}>
          Scrub <strong>view from / to</strong> to zoom the staircase and hire
          schedule. N sets how deep the walk runs. Try a window around a plateau
          (e.g. 100–160) to see flats vs jumps.
        </p>
      </div>

      <div className="graph2d" style={{ height: 340 }}>
        <Plot
          data={growthData}
          layout={growthLayout}
          config={plotConfig}
          style={{ width: "100%", height: "100%" }}
          useResizeHandler
        />
      </div>

      <div className="graph2d" style={{ height: 320, marginTop: "1rem" }}>
        <Plot
          data={stairData}
          layout={stairLayout}
          config={plotConfig}
          style={{ width: "100%", height: "100%" }}
          useResizeHandler
        />
      </div>

      <div className="graph2d" style={{ height: 360, marginTop: "1rem" }}>
        <Plot
          data={scheduleData}
          layout={scheduleLayout}
          config={plotConfig}
          style={{ width: "100%", height: "100%" }}
          useResizeHandler
        />
      </div>

      <div className="panel">
        <p className="hint" style={{ marginTop: 0 }}>
          <strong>Staircase.</strong> Flat stretches = covers that hire nobody new.
          Jumps = new names. Gold hires hug H≈2q (thin m=2q). Navy “late” hires
          are not random — they mostly sit on H≈4q (m=2²·q) and H≈8q (m=2³·q),
          with thinner bands at 10q, 14q, 16q (2·5·q, 2·7·q, 2⁴·q). Push N to 10000 to see them fill in. Example: 43 joins at 173
          via 172=2²·43; 5 joins early at 11 via 10=2·5. Through the dial:{" "}
          {model.thinCount} thin, {model.lateCount} later.
        </p>
        <p className="hint">
          <strong>First jumps:</strong>{" "}
          {model.eventsHead
            .map((e) => `${e.p}→+${e.neu.join(",")}`)
            .join("; ") || "—"}
        </p>
      </div>

      <div className="graph2d" style={{ height: 420, marginTop: "1rem" }}>
        <Plot
          data={[sunEdgeSpoke, sunEdgeGold, sunNodes]}
          layout={sunLayout}
          config={plotConfig}
          style={{ width: "100%", height: "100%" }}
          useResizeHandler
        />
      </div>

      <h2 style={{ fontSize: "1.1rem", marginTop: "1.6rem" }}>
        E · sack {5} hire-sun H
      </h2>
      <p className="hint" style={{ marginTop: 0 }}>
        Other agent’s E: prefer the 3-free door; when that door carries 5, flip
        to the ×3 neighbour and <strong>hire 3</strong> (3 stands in for 5). Never
        hire 5. Flips to {sack5.growthN}: {sack5.flips}. |S|@growth={sack5.sizeAtN}{" "}
        (standing A {model.sizeAtN}).
      </p>
      <div className="graph2d" style={{ height: 420, marginTop: "0.75rem" }}>
        <Plot
          data={[sack5SunEdgeSpoke, sack5SunEdgeGold, sack5SunNodes]}
          layout={sack5SunLayout}
          config={plotConfig}
          style={{ width: "100%", height: "100%" }}
          useResizeHandler
        />
      </div>
      <div className="panel">
        <p className="hint" style={{ marginTop: 0 }}>
          <strong>E · sack {5} H (graph through {sack5.graphN}):</strong> |S|={" "}
          {sack5.S.length}, extra gold={sack5.extra}, bottom gap={" "}
          {sack5.bottomGap.toFixed(4)}, top gap={sack5.topGap.toFixed(3)}, mid-max
          λ={sack5.midHire.toFixed(3)}, λ_max={sack5.lambdaMax.toFixed(3)}.
        </p>
        <p className="hint">
          <strong>Null star</strong> (24 runs): bottom≈{sack5.nullBottom.toFixed(4)},
          top≈{sack5.nullTop.toFixed(3)}, mid-max≈{sack5.nullMid.toFixed(3)},
          λ_max≈{sack5.nullMax.toFixed(3)}. Hire mid-max{" "}
          {sack5.midHire > sack5.nullMid ? "sits above" : "sits near"} the null
          mid-max.
        </p>
        <p className="hint">
          <strong>Top degrees:</strong>{" "}
          {sack5.deg
            .slice(0, 8)
            .map((d) => `${d.n}→${d.d}`)
            .join(", ")}
        </p>
        <p className="hint">
          <strong>S through {sack5.graphN} (no 5; 3 stands in):</strong>{" "}
          {sack5.S.join(", ")}
        </p>
      </div>

      <div className="graph2d" style={{ height: 300, marginTop: "1rem" }}>
        <Plot
          data={degData}
          layout={degLayout}
          config={plotConfig}
          style={{ width: "100%", height: "100%" }}
          useResizeHandler
        />
      </div>

      <div className="graph2d" style={{ height: 320, marginTop: "1rem" }}>
        <Plot
          data={eigData}
          layout={eigLayout}
          config={plotConfig}
          style={{ width: "100%", height: "100%" }}
          useResizeHandler
        />
      </div>

      <div className="panel">
        <p className="hint" style={{ marginTop: 0 }}>
          <strong>Hire H (graph through {model.graphN}):</strong> |S|={model.S.length},
          extra gold wires beyond star={model.extra}, bottom gap={" "}
          {model.bottomGap.toFixed(4)}, top gap={model.topGap.toFixed(3)}, mid-max
          λ={model.midHire.toFixed(3)}, λ_max={model.lambdaMax.toFixed(3)}.
        </p>
        <p className="hint">
          <strong>Null star</strong> (same spokes to 2, same {model.extra} extra
          wires placed at random, mean of 24): bottom≈{model.nullBottom.toFixed(4)},
          top≈{model.nullTop.toFixed(3)}, mid-max≈{model.nullMid.toFixed(3)},
          λ_max≈{model.nullMax.toFixed(3)}. Star fingerprints match (bottom≈1,
          λ_max≈|S|). Hire mid-max {model.midHire > model.nullMid ? "sits above" : "sits near"}{" "}
          the null mid-max — gold piles onto early hubs (5, 7, 11…).
        </p>
        <p className="hint">
          <strong>Top degrees:</strong>{" "}
          {model.deg
            .slice(0, 8)
            .map((d) => `${d.n}→${d.d}`)
            .join(", ")}
        </p>
        <p className="hint">
          <strong>S through {model.graphN}:</strong> {model.S.join(", ")}
        </p>
      </div>

      <blockquote
        style={{
          margin: "1rem 0",
          padding: "0.75rem 0.95rem",
          borderLeft: "3px solid " + ORANGE,
          background: PAPER,
          fontSize: "0.92rem",
          lineHeight: 1.45,
        }}
      >
        <strong style={{ color: ORANGE }}>Island dials (no zeta).</strong> The
        operator is the graph Laplacian on sites {"{"}2{"}"} ∪ hired names —
        real, self-adjoint, nothing more. Bottom gap ≈ 1 is the star / tone 2
        (always a spoke). Top gap is where the door geometry shows. Seat 3 never
        enters the vertex set, so it cannot become a second hub; ban-break
        (using the 3-neighbour) would twin the top energy. Quarter-clock reading:
        ±1 is the half-line step off even m; 3 is silent brick, not a frequency.
        Do not fit these λ to zeros.
      </blockquote>

      <div className="panel">
        <p className="hint" style={{ marginTop: 0 }}>
          Two columns stay separate: this page is the <strong>forced ±1 hop</strong>{" "}
          column (unique door, hire-sun, H). The smoothest ±1/±3 spelling column
          is still available on Spectrum if you want lowest-brick names — same
          law, different job.
        </p>
      </div>
    
      <aside className="lab-note-caveats" aria-label="Lab freeze / caveats">
        <p>
          <strong>Lab freeze.</strong> <em>C</em> unnamed. Papers 1–2 frozen.
        </p>
      </aside>

    </main>
  );
}
