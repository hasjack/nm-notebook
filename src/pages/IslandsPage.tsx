import { useMemo, useState } from "react";
import { Link } from "react-router-dom";

/** Hardcoded last-island + bridge facts — do not invent. */
const SINK = 524287; // 2^19 − 1 Mersenne; m0 = 2^19 (out-degree zero)
const ISLAND_A = 1048573; // m0 = 2 · 524287
const ISLAND_B = 8388593; // m0 = 2^4 · 524287
const BRIDGE = 46137211; // m0 = 2² · 11 · 1048573
const X_STAR = 92274421; // first owner of BRIDGE; m0(X*) = 2 · BRIDGE
const MAINLAND = 11; // gold arc target; in comp(5) since X=30

const GOLD = "#d4a017";
const GOLD_DIM = "#8a7010";
const INK = "#e8e0d0";
const INK_SOFT = "#c8bfb0";
const MERSENNE = "#c45c26";
const HIRE_FILL = "#c5d4e6";
const BRIDGE_FILL = "#e8c547";
const MAINLAND_FILL = "#7a9cc0";
const PANEL_STROKE = "#0b1626";

const VB_W = 1100;
const VB_H = 520;

type Phase = "before" | "at";

type SpotNode = {
  id: number;
  x: number;
  y: number;
  r: number;
  fill: string;
  label: string;
  sub?: string;
  tip: string;
  role: "mainland" | "bridge" | "island" | "sink";
};

function fmt(n: number): string {
  return n.toLocaleString("en-US");
}


const TIPS: Record<number, string> = {
  [MAINLAND]: `attachment into comp(5) — ${MAINLAND} is the join point, not the whole mainland`,
  [BRIDGE]: `→${MAINLAND} and →${fmt(ISLAND_A)}  ·  m₀ = 2² · 11 · ${fmt(ISLAND_A)}`,
  [SINK]: `Mersenne sink  ·  ${fmt(SINK)} = 2¹⁹ − 1  ·  m₀ = 2¹⁹`,
  [ISLAND_A]: `chain member  ·  m₀(${fmt(ISLAND_A)}) = 2 · ${fmt(SINK)}`,
  [ISLAND_B]: `chain member  ·  m₀(${fmt(ISLAND_B)}) = 2⁴ · ${fmt(SINK)}`,
};

function arcPath(
  x1: number,
  y1: number,
  x2: number,
  y2: number,
  bend = 0.18,
): string {
  const mx = (x1 + x2) / 2;
  const my = (y1 + y2) / 2;
  const dx = x2 - x1;
  const dy = y2 - y1;
  const cx = mx - dy * bend;
  const cy = my + dx * bend;
  return `M ${x1} ${y1} Q ${cx} ${cy} ${x2} ${y2}`;
}

function markerId(phase: Phase, kind: "gold" | "island"): string {
  return `islands-arrow-${phase}-${kind}`;
}

export function IslandsPage() {
  const [phase, setPhase] = useState<Phase>("at");
  const [hover, setHover] = useState<number | null>(null);
  const [hoverBlob, setHoverBlob] = useState<"mainland" | "island" | null>(
    null,
  );
  const atX = phase === "at";

  const nodes: SpotNode[] = useMemo(
    () => [
      {
        id: MAINLAND,
        x: 140,
        y: 260,
        r: 22,
        fill: MAINLAND_FILL,
        label: String(MAINLAND),
        tip: TIPS[MAINLAND],
        role: "mainland",
      },
      {
        id: BRIDGE,
        x: 480,
        y: 260,
        r: 28,
        fill: BRIDGE_FILL,
        label: fmt(BRIDGE),
        sub: "bridge",
        tip: TIPS[BRIDGE],
        role: "bridge",
      },
      {
        id: ISLAND_A,
        x: 780,
        y: 160,
        r: 22,
        fill: HIRE_FILL,
        label: fmt(ISLAND_A),
        tip: TIPS[ISLAND_A],
        role: "island",
      },
      {
        id: ISLAND_B,
        x: 900,
        y: 160,
        r: 20,
        fill: HIRE_FILL,
        label: fmt(ISLAND_B),
        tip: TIPS[ISLAND_B],
        role: "island",
      },
      {
        id: SINK,
        x: 840,
        y: 360,
        r: 26,
        fill: MERSENNE,
        label: fmt(SINK),
        sub: "Mersenne sink",
        tip: TIPS[SINK],
        role: "sink",
      },
    ],
    [],
  );

  const byId = useMemo(() => {
    const m = new Map<number, SpotNode>();
    for (const n of nodes) m.set(n.id, n);
    return m;
  }, [nodes]);

  const focusBlob: "mainland" | "island" | "bridge" | null = (() => {
    if (hover !== null) {
      const role = byId.get(hover)?.role;
      if (role === "mainland") return "mainland";
      if (role === "bridge") return "bridge";
      if (role === "island" || role === "sink") return "island";
    }
    return hoverBlob;
  })();

  const activeTip =
    hover !== null
      ? TIPS[hover]
      : focusBlob === "mainland"
        ? TIPS[MAINLAND]
        : focusBlob === "island"
          ? "last island — Mersenne sink plus chain"
          : null;

  const islandEdges: Array<{ from: number; to: number }> = [
    { from: ISLAND_A, to: SINK },
    { from: ISLAND_B, to: SINK },
  ];

  const goldEdges: Array<{ from: number; to: number }> = [
    { from: BRIDGE, to: MAINLAND },
    { from: BRIDGE, to: ISLAND_A },
  ];

  return (
    <main className="page islands-page">
      <h1>Islands</h1>
      <p className="lede">
        Basins is the drain lattice; this page is the one special object — the
        last island and the bridge that joins it to the mainland at{" "}
        <em>X</em>
        <sup>*</sup>.
      </p>

      <p className="islands-bernard">
        Gold joins at 92 million — and the next named island cannot even show up
        before 4.29 billion.
      </p>

      <p className="lede" style={{ maxWidth: "42rem" }}>
        Thin M₃₁ rail:{" "}
        <Link to="/corridor">Corridor</Link>
        {" · "}
        Notes: <Link to="/notes/hire-graph">The hire graph of the 3-free door</Link>
        {" · "}
        <Link to="/notes/when-gold-disconnects">When gold disconnects</Link>.
      </p>

      <div className="islands-panel">
        <div className="islands-toolbar" role="group" aria-label="Bridge phase">
          <button
            type="button"
            className={
              phase === "before" ? "islands-toggle on" : "islands-toggle"
            }
            aria-pressed={phase === "before"}
            onClick={() => setPhase("before")}
          >
            before <em>X</em>
            <sup>*</sup>
          </button>
          <button
            type="button"
            className={phase === "at" ? "islands-toggle on" : "islands-toggle"}
            aria-pressed={phase === "at"}
            onClick={() => setPhase("at")}
          >
            at <em>X</em>
            <sup>*</sup>
          </button>
          <span className="islands-status">
            {atX
              ? "gold joins mainland to island — components: 1"
              : "island separate — gold components: 2"}
          </span>
        </div>

        <div className="islands-readout" aria-live="polite">
          {activeTip ??
            (atX
              ? `X* = ${fmt(X_STAR)} first owns the bridge`
              : "hover a node · bridge still dim")}
        </div>

        <svg
          className="islands-svg"
          viewBox={`0 0 ${VB_W} ${VB_H}`}
          preserveAspectRatio="xMidYMid meet"
          role="img"
          aria-label="Last island and bridge at X-star"
          shapeRendering="geometricPrecision"
        >
          <defs>
            <marker
              id={markerId(phase, "gold")}
              viewBox="0 0 10 10"
              refX="9"
              refY="5"
              markerWidth="7"
              markerHeight="7"
              orient="auto-start-reverse"
            >
              <path d="M 0 0 L 10 5 L 0 10 z" fill={GOLD} />
            </marker>
            <marker
              id={markerId(phase, "island")}
              viewBox="0 0 10 10"
              refX="9"
              refY="5"
              markerWidth="6"
              markerHeight="6"
              orient="auto-start-reverse"
            >
              <path d="M 0 0 L 10 5 L 0 10 z" fill={INK_SOFT} />
            </marker>
          </defs>

          <g
            opacity={
              focusBlob === "island" ? 0.28 : focusBlob === "bridge" ? 0.72 : 1
            }
            className="islands-blob"
            onMouseEnter={() => setHoverBlob("mainland")}
            onMouseLeave={() =>
              setHoverBlob((b) => (b === "mainland" ? null : b))
            }
          >
            <ellipse
              cx={140}
              cy={260}
              rx={90}
              ry={70}
              fill="#1a2a40"
              opacity={0.45}
            />
            <text
              x={140}
              y={188}
              textAnchor="middle"
              className="islands-cluster-label"
            >
              mainland
            </text>
          </g>
          <g
            opacity={
              focusBlob === "mainland" ? 0.28 : focusBlob === "bridge" ? 0.72 : 1
            }
            className="islands-blob"
            onMouseEnter={() => setHoverBlob("island")}
            onMouseLeave={() =>
              setHoverBlob((b) => (b === "island" ? null : b))
            }
          >
            <ellipse
              cx={840}
              cy={250}
              rx={160}
              ry={140}
              fill="#1a2a40"
              opacity={0.45}
            />
            <text
              x={840}
              y={88}
              textAnchor="middle"
              className="islands-cluster-label"
            >
              last island
            </text>
          </g>

          {islandEdges.map((e) => {
            const a = byId.get(e.from)!;
            const b = byId.get(e.to)!;
            return (
              <path
                key={`i-${e.from}-${e.to}`}
                d={arcPath(a.x, a.y, b.x, b.y, 0.12)}
                fill="none"
                stroke={INK_SOFT}
                strokeWidth={1.6}
                strokeLinecap="round"
                markerEnd={`url(#${markerId(phase, "island")})`}
                opacity={0.9}
              />
            );
          })}

          {goldEdges.map((e) => {
            const a = byId.get(e.from)!;
            const b = byId.get(e.to)!;
            const bend = e.to === MAINLAND ? -0.22 : 0.2;
            return (
              <path
                key={`g-${e.from}-${e.to}`}
                d={arcPath(a.x, a.y, b.x, b.y, bend)}
                fill="none"
                stroke={atX ? GOLD : GOLD_DIM}
                strokeWidth={atX ? 2.8 : 1.4}
                strokeLinecap="round"
                strokeDasharray={atX ? undefined : "6 5"}
                markerEnd={atX ? `url(#${markerId(phase, "gold")})` : undefined}
                opacity={atX ? 1 : 0.22}
                className={atX ? "islands-gold-on" : "islands-gold-off"}
              />
            );
          })}

          {nodes.map((n) => {
            const isBridge = n.role === "bridge";
            const dimBridge = isBridge && !atX;
            const on = hover === n.id;
            const inMainland = n.role === "mainland";
            const inIsland = n.role === "island" || n.role === "sink";
            let blobDim = 1;
            if (focusBlob === "island" && inMainland) blobDim = 0.28;
            if (focusBlob === "mainland" && inIsland) blobDim = 0.28;
            if (focusBlob === "bridge" && (inMainland || inIsland)) blobDim = 0.72;
            const showSub =
              n.sub ??
              (inMainland && (on || focusBlob === "mainland")
                ? "attachment → comp(5)"
                : undefined);
            return (
              <g
                key={n.id}
                opacity={dimBridge ? 0.28 : blobDim}
                className={dimBridge ? "islands-bridge-dim" : "islands-node"}
              >
                <circle
                  cx={n.x}
                  cy={n.y}
                  r={n.r}
                  fill={n.fill}
                  stroke={on ? INK : PANEL_STROKE}
                  strokeWidth={on ? 2.4 : 1.2}
                />
                <circle
                  className="islands-hit"
                  cx={n.x}
                  cy={n.y}
                  r={Math.max(n.r + 8, 18)}
                  fill="transparent"
                  onMouseEnter={() => setHover(n.id)}
                  onMouseLeave={() =>
                    setHover((cur) => (cur === n.id ? null : cur))
                  }
                >
                  <title>{n.tip}</title>
                </circle>
                <text
                  x={n.x}
                  y={n.y - n.r - (showSub ? 18 : 8)}
                  textAnchor="middle"
                  fontSize={n.role === "bridge" ? 13 : 12}
                  fill={INK}
                  fontFamily="Georgia, Palatino, serif"
                  pointerEvents="none"
                >
                  {n.label}
                </text>
                {showSub ? (
                  <text
                    x={n.x}
                    y={n.y - n.r - 4}
                    textAnchor="middle"
                    fontSize={10}
                    fill={INK_SOFT}
                    fontFamily="Georgia, Palatino, serif"
                    pointerEvents="none"
                  >
                    {showSub}
                  </text>
                ) : null}
              </g>
            );
          })}
        </svg>
      </div>

      <p className="islands-lab-caption">
        Lab note — early windows are crowded with leftover 2-power-door
        satellites; <em>X</em>
        <sup>*</sup> is the first time the last island finds a clear bridge into
        the mainland. Past that we only checked through 2.2·10⁹ — “enough space
        forever” stays weak Q2, not a claim.
      </p>

      <p className="figure-caption islands-caption">
        <em>X</em>
        <sup>*</sup> is the first owner of {fmt(BRIDGE)}; m₀(<em>X</em>
        <sup>*</sup>) = 2 · {fmt(BRIDGE)} and m₀({fmt(BRIDGE)}) = 2² · 11 ·{" "}
        {fmt(ISLAND_A)}. Thin M₃₁ certificates:{" "}
        <Link to="/corridor">Corridor →</Link>
      </p>
    </main>
  );
}
