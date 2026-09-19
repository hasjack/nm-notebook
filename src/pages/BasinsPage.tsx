import { useMemo, useRef, useState } from "react";
import type { ChangeEvent, PointerEvent, WheelEvent } from "react";

const FERMAT = "#d4a017";
const MERSENNE = "#c45c26";
const FORK = "#3dba7a";
const FORK_EDGE = "#1e7a45";
const HIRE_EDGE = "#5c7394";
const INK = "#1a1a1a";
const HIRE_FILL = "#c5d4e6";

const VB_W = 1200;
const VB_H = 960;
const MARGIN = 36;
const SINK_Y = 78;
const BOTTOM_Y = 930;
const PREFERRED_GAP = 68;

type Kind = "fermat" | "mersenne" | "hire" | "fork";

type RawNode = {
  p: number;
  door: number;
  oddFactors: number[];
  kind: Kind;
  factorText: string;
};

type Meta = {
  sinks: number[];
  depth: number;
};

type Lane = {
  sink: number;
  left: number;
  right: number;
  center: number;
  width: number;
};

type Placed = RawNode & {
  x: number;
  y: number;
  r: number;
  sinks: number[];
  depth: number;
};

type DrawnEdge = {
  from: number;
  to: number;
  fork: boolean;
  d: string;
};

type Model = {
  nodes: Placed[];
  edges: DrawnEdge[];
  byP: Map<number, Placed>;
  scale: number;
};

function primesUpTo(n: number): number[] {
  if (n < 2) return [];
  const sieve = new Uint8Array(n + 1);
  sieve.fill(1);
  sieve[0] = 0;
  sieve[1] = 0;
  for (let i = 2; i * i <= n; i += 1) {
    if (sieve[i] === 0) continue;
    for (let j = i * i; j <= n; j += i) sieve[j] = 0;
  }
  const out: number[] = [];
  for (let i = 2; i <= n; i += 1) {
    if (sieve[i] === 1) out.push(i);
  }
  return out;
}

/** +1 when p ≡ 1 (mod 3), −1 when p ≡ 2 (mod 3). */
function chi3(p: number): number {
  return p % 3 === 1 ? 1 : -1;
}

function factorDoor(m: number): { odd: number[]; text: string } {
  const parts: string[] = [];
  const odd: number[] = [];
  let x = m;
  let twos = 0;
  while (x % 2 === 0) {
    x = Math.floor(x / 2);
    twos += 1;
  }
  if (twos > 0) parts.push(twos === 1 ? "2" : `2^${twos}`);
  let d = 3;
  while (d * d <= x) {
    if (x % d === 0) {
      let exp = 0;
      while (x % d === 0) {
        x = Math.floor(x / d);
        exp += 1;
      }
      odd.push(d);
      parts.push(exp === 1 ? String(d) : `${d}^${exp}`);
    }
    d += 2;
  }
  if (x > 1) {
    odd.push(x);
    parts.push(String(x));
  }
  return { odd, text: `${m} = ${parts.join(" × ")}` };
}

function kindOf(p: number, odd: number[]): Kind {
  if (odd.length === 0) return p % 3 === 2 ? "fermat" : "mersenne";
  if (odd.length === 1) return "hire";
  return "fork";
}

function buildRaw(n: number): RawNode[] {
  const primes = primesUpTo(n).filter((p) => p !== 2 && p !== 3);
  return primes.map((p) => {
    const door = p + chi3(p);
    const fact = factorDoor(door);
    return {
      p,
      door,
      oddFactors: fact.odd,
      kind: kindOf(p, fact.odd),
      factorText: fact.text,
    };
  });
}

function annotate(byRaw: Map<number, RawNode>): Map<number, Meta> {
  const sinkMemo = new Map<number, number[]>();
  const depthMemo = new Map<number, number>();

  function sinksOf(p: number): number[] {
    const cached = sinkMemo.get(p);
    if (cached) return cached;
    const node = byRaw.get(p);
    if (!node || node.oddFactors.length === 0) {
      const self = node ? [node.p] : [];
      sinkMemo.set(p, self);
      return self;
    }
    const acc = new Set<number>();
    for (const q of node.oddFactors) {
      if (!byRaw.has(q)) continue;
      for (const s of sinksOf(q)) acc.add(s);
    }
    const out = [...acc].sort((a, b) => a - b);
    sinkMemo.set(p, out);
    return out;
  }

  function depthOf(p: number): number {
    const cached = depthMemo.get(p);
    if (cached !== undefined) return cached;
    const node = byRaw.get(p);
    if (!node || node.oddFactors.length === 0) {
      depthMemo.set(p, 0);
      return 0;
    }
    let deepest = 0;
    for (const q of node.oddFactors) {
      if (!byRaw.has(q)) continue;
      deepest = Math.max(deepest, depthOf(q));
    }
    const depth = deepest + 1;
    depthMemo.set(p, depth);
    return depth;
  }

  const out = new Map<number, Meta>();
  for (const p of byRaw.keys()) {
    out.set(p, { sinks: sinksOf(p), depth: depthOf(p) });
  }
  return out;
}

function laneLayout(raw: RawNode[], meta: Map<number, Meta>, sinks: number[]): Lane[] {
  const exclusive = new Map<number, number>();
  for (const sink of sinks) exclusive.set(sink, 0);
  for (const node of raw) {
    if (node.kind === "fork") continue;
    const info = meta.get(node.p);
    if (!info || info.sinks.length !== 1) continue;
    const sink = info.sinks[0];
    if (sink === undefined) continue;
    exclusive.set(sink, (exclusive.get(sink) ?? 0) + 1);
  }
  const weights = sinks.map((sink) => (exclusive.get(sink) ?? 0) + 1);
  const sumW = weights.reduce((sum, w) => sum + w, 0) || 1;
  const available = VB_W - 2 * MARGIN;
  const count = sinks.length;
  if (count === 0) return [];
  const minShare = Math.min(72, available / count);
  const extra = Math.max(0, available - minShare * count);
  const lanes: Lane[] = [];
  let cursor = MARGIN;
  for (let i = 0; i < count; i += 1) {
    const sink = sinks[i];
    if (sink === undefined) continue;
    const weight = weights[i] ?? 1;
    const width = minShare + extra * (weight / sumW);
    lanes.push({
      sink,
      left: cursor,
      right: cursor + width,
      center: cursor + width / 2,
      width,
    });
    cursor += width;
  }
  return lanes;
}

function clamp(value: number, lo: number, hi: number): number {
  if (hi < lo) return (lo + hi) / 2;
  return Math.min(hi, Math.max(lo, value));
}

/** Small left-to-right spread around the lane centre. Overlap rather than leave the lane. */
function spreadInLane(count: number, center: number, left: number, right: number): number[] {
  if (count <= 1) return [center];
  const lo = left + 6;
  const hi = Math.max(lo, right - 6);
  const span = hi - lo;
  const step = count <= 1 ? 0 : span / (count - 1);
  return Array.from({ length: count }, (_, i) => lo + i * step);
}

/**
 * Several nodes share one midpoint. Fan them around that x so each stays clickable.
 * The fan is centred on the midpoint of the extreme sink centres.
 */
function fanAround(center: number, count: number): number[] {
  if (count <= 1) return [center];
  const step = count <= 3 ? 34 : 22;
  const span = step * (count - 1);
  let start = center - span / 2;
  const lo = MARGIN + 12;
  const hi = VB_W - MARGIN - 12;
  if (start < lo) start = lo;
  if (start + span > hi) start = Math.max(lo, hi - span);
  if (start + span > hi) {
    const squeezed = (hi - lo) / (count - 1);
    return Array.from({ length: count }, (_, i) => lo + i * squeezed);
  }
  return Array.from({ length: count }, (_, i) => start + i * step);
}

function midpointOf(sinks: number[], laneOf: Map<number, Lane>): number {
  let lo = Infinity;
  let hi = -Infinity;
  for (const sink of sinks) {
    const c = laneOf.get(sink)?.center;
    if (c === undefined) continue;
    if (c < lo) lo = c;
    if (c > hi) hi = c;
  }
  if (!Number.isFinite(lo) || !Number.isFinite(hi)) return VB_W / 2;
  return (lo + hi) / 2;
}

function markScale(count: number): number {
  return Math.min(1.35, Math.max(0.42, Math.sqrt(36 / Math.max(count, 1))));
}

function rowY(depth: number, rowGap: number): number {
  if (depth <= 0) return SINK_Y;
  return SINK_Y + depth * rowGap;
}

function curve(from: Placed, to: Placed): string {
  const dx = to.x - from.x;
  const dy = to.y - from.y;
  const len = Math.hypot(dx, dy) || 1;
  const ux = dx / len;
  const uy = dy / len;
  const x1 = from.x + ux * (from.r + 1.5);
  const y1 = from.y + uy * (from.r + 1.5);
  const x2 = to.x - ux * (to.r + 1.5);
  const y2 = to.y - uy * (to.r + 1.5);
  const cpx = x1 + (x2 - x1) * 0.72;
  const cpy = y1 + (y2 - y1) * 0.24;
  return `M ${x1.toFixed(2)} ${y1.toFixed(2)} Q ${cpx.toFixed(2)} ${cpy.toFixed(2)} ${x2.toFixed(2)} ${y2.toFixed(2)}`;
}

function rank(kind: Kind): number {
  if (kind === "fork") return 2;
  if (kind === "hire") return 1;
  return 0;
}

function buildModel(n: number): Model {
  const raw = buildRaw(n);
  const byRaw = new Map(raw.map((node) => [node.p, node]));
  const meta = annotate(byRaw);
  const sinkIds = raw
    .filter((node) => node.kind === "fermat" || node.kind === "mersenne")
    .map((node) => node.p)
    .sort((a, b) => a - b);
  const lanes = laneLayout(raw, meta, sinkIds);
  const laneOf = new Map(lanes.map((lane) => [lane.sink, lane]));
  let maxDepth = 0;
  for (const node of raw) {
    const depth = meta.get(node.p)?.depth ?? 0;
    if (depth > maxDepth) maxDepth = depth;
  }
  const rowGap =
    maxDepth > 0 ? (BOTTOM_Y - SINK_Y) / maxDepth : PREFERRED_GAP;
  const scale = markScale(raw.length);

  const placed = new Map<number, Placed>();
  for (const sink of sinkIds) {
    const node = byRaw.get(sink);
    const lane = laneOf.get(sink);
    if (!node || !lane) continue;
    placed.set(sink, {
      ...node,
      x: lane.center,
      y: SINK_Y,
      r: 14 * scale,
      sinks: [sink],
      depth: 0,
    });
  }

  const laneBuckets = new Map<string, RawNode[]>();
  const midBuckets = new Map<string, RawNode[]>();
  for (const node of raw) {
    if (node.kind === "fermat" || node.kind === "mersenne") continue;
    const info = meta.get(node.p);
    if (!info) continue;
    if (node.kind !== "fork" && info.sinks.length === 1) {
      const only = info.sinks[0];
      const key = `${only ?? 0}:${info.depth}`;
      const bucket = laneBuckets.get(key);
      if (bucket) bucket.push(node);
      else laneBuckets.set(key, [node]);
    } else {
      const key = `${info.depth}:${info.sinks.join(",")}`;
      const bucket = midBuckets.get(key);
      if (bucket) bucket.push(node);
      else midBuckets.set(key, [node]);
    }
  }

  for (const [key, group] of laneBuckets) {
    const colon = key.indexOf(":");
    const sink = Number(key.slice(0, colon));
    const depth = Number(key.slice(colon + 1));
    const lane = laneOf.get(sink);
    const center = lane?.center ?? VB_W / 2;
    const left = lane?.left ?? MARGIN;
    const right = lane?.right ?? VB_W - MARGIN;
    group.sort((a, b) => a.p - b.p);
    const xs = spreadInLane(group.length, center, left, right);
    for (let i = 0; i < group.length; i += 1) {
      const node = group[i];
      if (!node) continue;
      const info = meta.get(node.p);
      placed.set(node.p, {
        ...node,
        x: xs[i] ?? center,
        y: rowY(depth, rowGap),
        r: 8 * scale,
        sinks: info?.sinks ?? [],
        depth,
      });
    }
  }

  for (const [key, group] of midBuckets) {
    const colon = key.indexOf(":");
    const depth = Number(key.slice(0, colon));
    const sinkPart = key.slice(colon + 1);
    const ids =
      sinkPart.length === 0 ? [] : sinkPart.split(",").map((part) => Number(part));
    const anchor = midpointOf(ids, laneOf);
    group.sort((a, b) => a.p - b.p);
    const xs = fanAround(anchor, group.length);
    for (let i = 0; i < group.length; i += 1) {
      const node = group[i];
      if (!node) continue;
      const info = meta.get(node.p);
      placed.set(node.p, {
        ...node,
        x: xs[i] ?? anchor,
        y: rowY(depth, rowGap),
        r: (node.kind === "fork" ? 12 : 8) * scale,
        sinks: info?.sinks ?? [],
        depth,
      });
    }
  }

  const nodes = [...placed.values()];
  nodes.sort((a, b) => rank(a.kind) - rank(b.kind) || a.p - b.p);
  const byP = new Map(nodes.map((node) => [node.p, node]));
  const edges: DrawnEdge[] = [];
  for (const node of nodes) {
    for (const q of node.oddFactors) {
      const child = byP.get(q);
      if (!child) continue;
      edges.push({
        from: node.p,
        to: q,
        fork: node.kind === "fork",
        d: curve(node, child),
      });
    }
  }
  edges.sort((a, b) => Number(a.fork) - Number(b.fork));
  return { nodes, edges, byP, scale };
}

function className(kind: Kind): string {
  if (kind === "fermat") return "Fermat";
  if (kind === "mersenne") return "Mersenne";
  if (kind === "fork") return "fork";
  return "hire";
}

function fillOf(kind: Kind): string {
  if (kind === "fermat") return FERMAT;
  if (kind === "mersenne") return MERSENNE;
  if (kind === "fork") return FORK;
  return HIRE_FILL;
}

function downstream(p: number, byP: Map<number, Placed>): Set<number> {
  const seen = new Set<number>();
  const stack: number[] = [p];
  while (stack.length > 0) {
    const cur = stack.pop();
    if (cur === undefined || seen.has(cur)) continue;
    seen.add(cur);
    const node = byP.get(cur);
    if (!node) continue;
    for (const q of node.oddFactors) stack.push(q);
  }
  return seen;
}

function readoutOf(node: Placed): string {
  if (node.kind === "fermat" || node.kind === "mersenne") {
    const empty =
      node.oddFactors.length === 0
        ? " · no odd prime hired from it yet"
        : "";
    return `${node.p} · door ${node.factorText} · ${className(node.kind)} sink · pure power of 2${empty}`;
  }
  const sinks = node.sinks.join(", ");
  return `${node.p} · door ${node.factorText} · class ${className(node.kind)} · sinks ${sinks}`;
}

const N_MIN = 10;
const N_MAX = 65537;
const SLIDER_MAX = 1000;

function nFromSlider(tick: number): number {
  const u = tick / SLIDER_MAX;
  const log = Math.log(N_MIN) + u * (Math.log(N_MAX) - Math.log(N_MIN));
  return Math.max(N_MIN, Math.min(N_MAX, Math.round(Math.exp(log))));
}

function sliderFromN(n: number): number {
  const u = (Math.log(Math.max(n, N_MIN)) - Math.log(N_MIN)) / (Math.log(N_MAX) - Math.log(N_MIN));
  return Math.round(Math.min(1, Math.max(0, u)) * SLIDER_MAX);
}

type ViewBox = { x: number; y: number; w: number; h: number };

export function BasinsPage() {
  const [limit, setLimit] = useState(10);
  const [hover, setHover] = useState<number | null>(null);
  const [pinned, setPinned] = useState<number | null>(null);
  const [view, setView] = useState<ViewBox>({ x: 0, y: 0, w: VB_W, h: VB_H });
  const drag = useRef<{
    pointerId: number;
    sx: number;
    sy: number;
    ox: number;
    oy: number;
  } | null>(null);
  const svgRef = useRef<SVGSVGElement | null>(null);
  const model = useMemo(() => buildModel(limit), [limit]);
  const active = hover ?? pinned;
  const activeNode = active === null ? undefined : model.byP.get(active);
  const lit = useMemo(() => {
    if (active === null) return null;
    if (!model.byP.has(active)) return null;
    return downstream(active, model.byP);
  }, [active, model]);

  function onLimit(event: ChangeEvent<HTMLInputElement>): void {
    setLimit(nFromSlider(Number(event.target.value)));
    setView({ x: 0, y: 0, w: VB_W, h: VB_H });
  }

  function clientToSvg(clientX: number, clientY: number): { x: number; y: number } {
    const el = svgRef.current;
    if (!el) return { x: 0, y: 0 };
    const rect = el.getBoundingClientRect();
    const px = (clientX - rect.left) / Math.max(rect.width, 1);
    const py = (clientY - rect.top) / Math.max(rect.height, 1);
    return { x: view.x + px * view.w, y: view.y + py * view.h };
  }

  function onWheel(event: WheelEvent<SVGSVGElement>): void {
    event.preventDefault();
    const factor = event.deltaY < 0 ? 0.86 : 1.16;
    const nextW = Math.min(VB_W * 1.4, Math.max(VB_W * 0.08, view.w * factor));
    const nextH = nextW * (VB_H / VB_W);
    const focus = clientToSvg(event.clientX, event.clientY);
    const px = (focus.x - view.x) / view.w;
    const py = (focus.y - view.y) / view.h;
    let nx = focus.x - px * nextW;
    let ny = focus.y - py * nextH;
    nx = Math.min(VB_W - nextW * 0.2, Math.max(-nextW * 0.2, nx));
    ny = Math.min(VB_H - nextH * 0.2, Math.max(-nextH * 0.2, ny));
    setView({ x: nx, y: ny, w: nextW, h: nextH });
  }

  function onPointerDown(event: PointerEvent<SVGSVGElement>): void {
    if (event.button !== 0) return;
    const target = event.target as Element | null;
    if (target?.closest?.(".basins-hit")) return;
    (event.currentTarget as SVGSVGElement).setPointerCapture(event.pointerId);
    drag.current = {
      pointerId: event.pointerId,
      sx: event.clientX,
      sy: event.clientY,
      ox: view.x,
      oy: view.y,
    };
  }

  function onPointerMove(event: PointerEvent<SVGSVGElement>): void {
    const d = drag.current;
    if (!d || d.pointerId !== event.pointerId) return;
    const el = svgRef.current;
    if (!el) return;
    const rect = el.getBoundingClientRect();
    const dx = ((event.clientX - d.sx) / Math.max(rect.width, 1)) * view.w;
    const dy = ((event.clientY - d.sy) / Math.max(rect.height, 1)) * view.h;
    setView((cur) => ({ ...cur, x: d.ox - dx, y: d.oy - dy }));
  }

  function onPointerUp(event: PointerEvent<SVGSVGElement>): void {
    if (drag.current?.pointerId === event.pointerId) drag.current = null;
  }

  function resetView(): void {
    setView({ x: 0, y: 0, w: VB_W, h: VB_H });
  }

  return (
    <main className="page basins-page">
      <h1>Basins</h1>

      <div className="basins-panel">
        <label className="basins-slider">
          <span>N = {limit.toLocaleString("en-GB")}</span>
          <input
            type="range"
            min={0}
            max={SLIDER_MAX}
            step={1}
            value={sliderFromN(limit)}
            aria-label="Primes through N"
            onChange={onLimit}
          />
        </label>
        <div className="basins-readout">
          {activeNode ? readoutOf(activeNode) : "hover a prime · scroll to zoom · drag to pan"}
        </div>
        <div className="basins-toolbar">
          <ul className="basins-legend">
            <li>
              <i className="dot fermat" /> Fermat
            </li>
            <li>
              <i className="dot mersenne" /> Mersenne
            </li>
            <li>
              <i className="dot fork" /> fork
            </li>
          </ul>
          <button type="button" className="basins-reset" onClick={resetView}>
            reset view
          </button>
        </div>
        <p className="basins-caption">
          An odd prime other than 3 has two even neighbours. One of them is free
          of the factor 3 — that neighbour is the door. Follow the odd primes in
          the door downhill until you land on a power of 2: those are the sinks
          (Fermat just above, Mersenne just below). Two or more odd primes in a
          door make a fork; the picture draws each split onto the sinks it feeds.
          The rail stops at Fermat 65537; the next sink is Mersenne 131071.
        </p>
        <svg
          ref={svgRef}
          viewBox={`${view.x} ${view.y} ${view.w} ${view.h}`}
          preserveAspectRatio="xMidYMid meet"
          role="img"
          aria-label="Hire basins"
          shapeRendering="geometricPrecision"
          className="basins-svg"
          onWheel={onWheel}
          onPointerDown={onPointerDown}
          onPointerMove={onPointerMove}
          onPointerUp={onPointerUp}
          onPointerCancel={onPointerUp}
        >
          {model.edges.map((edge) => {
            const on = lit?.has(edge.from) ?? false;
            const dim = lit !== null && !on;
            const base = (edge.fork ? 0.55 : 0.28) * model.scale;
            const width = on ? base * 2.8 : base;
            return (
              <path
                key={`${edge.from}-${edge.to}`}
                d={edge.d}
                fill="none"
                stroke={edge.fork ? FORK_EDGE : HIRE_EDGE}
                strokeWidth={width}
                strokeLinecap="round"
                opacity={dim ? 0.06 : on ? 1 : edge.fork ? 0.55 : 0.35}
                style={{ pointerEvents: "none" }}
              />
            );
          })}
          {model.nodes.map((node) => {
            const on = active === node.p;
            const showLabel =
              node.kind === "fermat" ||
              node.kind === "mersenne" ||
              (node.kind === "fork" && model.nodes.length <= 70) ||
              (node.kind === "hire" && limit <= 80) ||
              on;
            return (
              <g key={node.p}>
                <circle
                  cx={node.x}
                  cy={node.y}
                  r={node.r}
                  fill={fillOf(node.kind)}
                  stroke={on ? "#9a2f38" : "#1a1a1a"}
                  strokeWidth={on ? 2 : 1}
                />
                <circle
                  className="basins-hit"
                  cx={node.x}
                  cy={node.y}
                  r={Math.max(node.r + 2, 5)}
                  fill="transparent"
                  onMouseEnter={() => {
                    setHover(node.p);
                  }}
                  onMouseLeave={() => {
                    setHover((cur) => (cur === node.p ? null : cur));
                  }}
                  onClick={() => {
                    setPinned((cur) => (cur === node.p ? null : node.p));
                  }}
                />
                {showLabel && node.kind !== "fermat" && node.kind !== "mersenne" ? (
                  node.kind === "fork" ? (
                    <g pointerEvents="none">
                      <text
                        x={node.x}
                        y={node.y + node.r + 14}
                        textAnchor="middle"
                        fontSize={Math.max(8, 12 * model.scale)}
                        fill={INK}
                        fontFamily="Georgia, Palatino, serif"
                      >
                        {node.p}
                      </text>
                      <text
                        x={node.x}
                        y={node.y + node.r + 26}
                        textAnchor="middle"
                        fontSize={Math.max(7, 10 * model.scale)}
                        fill={INK}
                        fontFamily="Georgia, Palatino, serif"
                      >
                        fork
                      </text>
                    </g>
                  ) : (
                    <text
                      x={node.x}
                      y={node.y + node.r + 12}
                      textAnchor="middle"
                      fontSize={Math.max(8, 12 * model.scale)}
                      fill={INK}
                      fontFamily="Georgia, Palatino, serif"
                      pointerEvents="none"
                    >
                      {node.p}
                    </text>
                  )
                ) : null}
                {node.kind === "fermat" || node.kind === "mersenne" ? (
                  <g pointerEvents="none">
                    <text
                      x={node.x}
                      y={node.y - node.r - 6}
                      textAnchor="middle"
                      fontSize={Math.max(9, 13 * model.scale)}
                      fill={INK}
                      fontFamily="Georgia, Palatino, serif"
                    >
                      {node.p}
                    </text>
                    <text
                      x={node.x}
                      y={node.y - node.r - 18}
                      textAnchor="middle"
                      fontSize={Math.max(8, 10 * model.scale)}
                      fill={INK}
                      fontFamily="Georgia, Palatino, serif"
                    >
                      {node.kind === "fermat" ? "Fermat" : "Mersenne"}
                    </text>
                  </g>
                ) : null}
              </g>
            );
          })}
        </svg>
      </div>
    </main>
  );
}
