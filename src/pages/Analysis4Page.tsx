import { useMemo, useState } from "react";
import Plot from "../components/Plot";
import { baseFromSlider, fmt, fmtBase, sliderFromBase } from "../lib/format";
import {
  CREAM,
  MAROON,
  MUTED,
  NAVY,
  ORANGE,
  PAPER,
  plotConfig,
} from "../lib/plotTheme";
import type { Data, Layout } from "plotly.js";

const PI2_6 = (Math.PI * Math.PI) / 6;
const CUBE = 1.202056903159594;
const SPINE = [1, 3, 5, 7, 9] as const;

type ProbeId =
  | "sym"
  | "pi-ln-only"
  | "ignore-beta"
  | "ignore-alpha"
  | "alpha-sq"
  | "beta-sq"
  | "alpha-times"
  | "pi-odd";

const PROBES: { id: ProbeId; label: string; note: string }[] = [
  {
    id: "sym",
    label: "symmetric (product)",
    note: "S = (α·β·π·ln(base))² / 6 — flat on full beacon surface",
  },
  {
    id: "pi-ln-only",
    label: "(π ln base)² / 6",
    note: "Ignore α,β — varies on spine as odd² · π²/6",
  },
  {
    id: "ignore-beta",
    label: "(α·π·ln)² / 6",
    note: "Drop β from the nest",
  },
  {
    id: "ignore-alpha",
    label: "(β·π·ln)² / 6",
    note: "Drop α from the nest",
  },
  {
    id: "alpha-sq",
    label: "α² (β·π·ln)² / 6",
    note: "Weight i-factor outside",
  },
  {
    id: "beta-sq",
    label: "β² (α·π·ln)² / 6",
    note: "Weight π-factor outside",
  },
  {
    id: "alpha-times",
    label: "α (β·π·ln)² / 6",
    note: "Linear α times β-nest",
  },
  {
    id: "pi-odd",
    label: "(π · odd)² / 6",
    note: "Explicit odd label — not a dial formula",
  },
];

function near(a: number, b: number, eps = 1e-4) {
  return Math.abs(a - b) < eps;
}

function asymmetric(
  id: ProbeId,
  alpha: number,
  beta: number,
  ln: number,
  odd: number
): number {
  const pi = Math.PI;
  switch (id) {
    case "sym":
      return (alpha * beta * pi * ln) ** 2 / 6;
    case "pi-ln-only":
      return (pi * ln) ** 2 / 6;
    case "ignore-beta":
      return (alpha * pi * ln) ** 2 / 6;
    case "ignore-alpha":
      return (beta * pi * ln) ** 2 / 6;
    case "alpha-sq":
      return alpha ** 2 * (beta * pi * ln) ** 2 / 6;
    case "beta-sq":
      return beta ** 2 * (alpha * pi * ln) ** 2 / 6;
    case "alpha-times":
      return alpha * (beta * pi * ln) ** 2 / 6;
    case "pi-odd":
      return (pi * odd) ** 2 / 6;
  }
}

/**
 * Analysis 4 — asymmetric nest.
 * Classical nest only at Euler; spine may carry asymmetric probes.
 * Twin peg costumes kept visible as star labels.
 */
export function Analysis4Page() {
  const [probe, setProbe] = useState<ProbeId>("pi-ln-only");
  const [which, setWhich] = useState<"beta" | "alpha">("beta");
  const [idx, setIdx] = useState(0);
  const [mode, setMode] = useState<"spine" | "free">("spine");
  const [t, setT] = useState(() => sliderFromBase(Math.E));
  const [alphaF, setAlphaF] = useState(1);
  const [betaF, setBetaF] = useState(1);

  const odd = SPINE[idx];
  const spineBase = Math.exp(odd);
  const spineAlpha = which === "alpha" ? 1 / odd : 1;
  const spineBeta = which === "beta" ? 1 / odd : 1;

  const base = mode === "spine" ? spineBase : baseFromSlider(t);
  const alpha = mode === "spine" ? spineAlpha : alphaF;
  const beta = mode === "spine" ? spineBeta : betaF;
  const ln = Math.log(base);
  const prod = alpha * beta * ln;
  const sym = (prod * Math.PI) ** 2 / 6;
  const asym = asymmetric(probe, alpha, beta, ln, odd);

  const r = Math.round(prod);
  const onPeg = near(prod, r) && Math.abs(r) % 2 === 1;
  const onClassicalNest = near(Math.abs(prod), 1);
  const onEuler =
    near(base, Math.E, 1e-6) && near(alpha, 1) && near(beta, 1);

  const spineSeries: Data[] = useMemo(() => {
    const odds = [...SPINE];
    const symY = odds.map((o) => {
      const a = which === "alpha" ? 1 / o : 1;
      const b = which === "beta" ? 1 / o : 1;
      const p = a * b * o; // ln(e^o)=o
      return (p * Math.PI) ** 2 / 6;
    });
    const asymY = odds.map((o) => {
      const a = which === "alpha" ? 1 / o : 1;
      const b = which === "beta" ? 1 / o : 1;
      return asymmetric(probe, a, b, o, o);
    });
    return [
      {
        type: "scatter",
        mode: "lines+markers",
        x: odds,
        y: symY,
        name: "symmetric nest",
        line: { color: NAVY, width: 2 },
        marker: { size: 8 },
      },
      {
        type: "scatter",
        mode: "lines+markers",
        x: odds,
        y: asymY,
        name: "asymmetric probe",
        line: { color: MAROON, width: 2.5 },
        marker: { size: 9, symbol: "diamond", color: ORANGE },
      },
      {
        type: "scatter",
        mode: "lines",
        x: odds,
        y: odds.map(() => PI2_6),
        name: "π²/6",
        line: { color: MUTED, width: 1, dash: "dash" },
      },
      {
        type: "scatter",
        mode: "lines",
        x: odds,
        y: odds.map(() => CUBE),
        name: "cube sum (guide)",
        line: { color: MUTED, width: 1, dash: "dot" },
      },
    ];
  }, [probe, which]);

  const layout: Partial<Layout> = {
    paper_bgcolor: CREAM,
    plot_bgcolor: PAPER,
    margin: { l: 55, r: 20, t: 40, b: 45 },
    title: {
      text: "Beacon spine — symmetric flat vs asymmetric probe",
      font: { size: 13, family: "Georgia, serif" },
    },
    xaxis: { title: { text: "odd" }, dtick: 2 },
    yaxis: { title: { text: "height" } },
    showlegend: true,
    legend: { orientation: "h", y: -0.2 },
    font: { family: "Georgia, Palatino, serif" },
  };

  const probeMeta = PROBES.find((p) => p.id === probe)!;

  return (
    <main className="page">
      <h1>Analysis 4 — asymmetric nest</h1>
      <p className="lede">
        Do <strong>not</strong> demand the nest stay π²/6 on the whole beacon
        surface. Calibrate classically at Euler (e, 1, 1). Along the spine
        e^odd with factor 1/odd, the symmetric nest is flat — so e³ is not a
        new nest. Asymmetric probes may move. Star costumes at the peg stay:{" "}
        <strong>−2 Li₂(e^(iπ))</strong> and{" "}
        <strong>−(4/3) Li₃(e^(iπ))</strong>.
      </p>

      <div className="value" style={{ fontSize: "1.35rem" }}>
        −(4/3) Li₃(e^(iπ))
      </div>
      <div className="expr">
        twin of −2 Li₂(e^(iπ)) · cube height on the same peg (nicer than the Apéry
        costume)
      </div>
      <div className="rule">
        {onEuler
          ? "classical Euler lock"
          : onPeg && onClassicalNest
            ? "joint beacon (peg + |prod|=1)"
            : onPeg
              ? "on −1 peg"
              : "off peg"}
        {" · "}
        sym nest {fmt(sym, 5)} · probe {fmt(asym, 5)}
      </div>

      <div className="split-readout">
        <div>
          <div className="kv-label">base</div>
          <div className="kv-value">{fmtBase(base)}</div>
        </div>
        <div>
          <div className="kv-label">α</div>
          <div className="kv-value">{fmt(alpha, 5)}</div>
        </div>
        <div>
          <div className="kv-label">β</div>
          <div className="kv-value">{fmt(beta, 5)}</div>
        </div>
        <div>
          <div className="kv-label">α·β·ln</div>
          <div className="kv-value">{fmt(prod, 4)}</div>
        </div>
      </div>

      <div className="graph2d" style={{ height: 360 }}>
        <Plot
          data={spineSeries}
          layout={layout}
          config={plotConfig}
          style={{ width: "100%", height: "100%" }}
          useResizeHandler
        />
      </div>

      <div className="panel">
        <div className="modes" style={{ display: "flex", gap: "0.4rem", flexWrap: "wrap" }}>
          <button
            type="button"
            onClick={() => setMode("spine")}
            style={{
              background: mode === "spine" ? "#1f4e79" : "#fffaf3",
              color: mode === "spine" ? "#fff" : "#1a1a1a",
              border: "1px solid #e2d8c8",
              borderRadius: 8,
              padding: "0.35rem 0.75rem",
              font: "inherit",
              cursor: "pointer",
            }}
          >
            Spine
          </button>
          <button
            type="button"
            onClick={() => setMode("free")}
            style={{
              background: mode === "free" ? "#1f4e79" : "#fffaf3",
              color: mode === "free" ? "#fff" : "#1a1a1a",
              border: "1px solid #e2d8c8",
              borderRadius: 8,
              padding: "0.35rem 0.75rem",
              font: "inherit",
              cursor: "pointer",
            }}
          >
            Free dials
          </button>
        </div>

        <label className="row" style={{ marginTop: "0.8rem" }}>
          <span>asymmetric probe</span>
          <select
            value={probe}
            onChange={(e) => setProbe(e.target.value as ProbeId)}
          >
            {PROBES.map((p) => (
              <option key={p.id} value={p.id}>
                {p.label}
              </option>
            ))}
          </select>
        </label>
        <p className="hint">{probeMeta.note}</p>

        {mode === "spine" && (
          <>
            <div className="actions">
              {SPINE.map((o, i) => (
                <button key={o} type="button" onClick={() => setIdx(i)}>
                  e^{o}
                  {i === idx ? " ·" : ""}
                </button>
              ))}
            </div>
            <label className="row">
              <span>who takes 1/odd?</span>
              <select
                value={which}
                onChange={(e) => setWhich(e.target.value as "beta" | "alpha")}
              >
                <option value="beta">π-factor β</option>
                <option value="alpha">i-factor α</option>
              </select>
            </label>
          </>
        )}

        {mode === "free" && (
          <>
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
            <label className="row">
              <span>α</span>
              <span>{fmt(alphaF, 3)}</span>
            </label>
            <input
              type="range"
              min={0.05}
              max={3}
              step={0.01}
              value={alphaF}
              onChange={(e) => setAlphaF(parseFloat(e.target.value))}
            />
            <label className="row">
              <span>β</span>
              <span>{fmt(betaF, 3)}</span>
            </label>
            <input
              type="range"
              min={0.05}
              max={3}
              step={0.01}
              value={betaF}
              onChange={(e) => setBetaF(parseFloat(e.target.value))}
            />
            <div className="actions">
              <button
                type="button"
                onClick={() => {
                  setT(sliderFromBase(Math.E));
                  setAlphaF(1);
                  setBetaF(1);
                }}
              >
                Euler
              </button>
              <button
                type="button"
                onClick={() => {
                  setT(sliderFromBase(Math.exp(3)));
                  setAlphaF(1);
                  setBetaF(1 / 3);
                }}
              >
                e³ · β=⅓
              </button>
            </div>
          </>
        )}
      </div>

      <div className="catalogue-list" style={{ marginTop: "1rem" }}>
        <article className="catalogue-card grade-clean">
          <header className="catalogue-card-head">
            <h2>Star peg costumes</h2>
            <span className="grade-pill grade-clean">peg</span>
          </header>
          <p>
            π²/6 = −2 Li₂(e^(iπ)). Cube sum = −(4/3) Li₃(e^(iπ)). Same door,
            different floor — prefer this packaging over the Apéry costume.
          </p>
        </article>
        <article className="catalogue-card grade-calligraphy">
          <header className="catalogue-card-head">
            <h2>Honest limit</h2>
            <span className="grade-pill grade-calligraphy">probe</span>
          </header>
          <p>
            Asymmetric formulas are probes. Moving on the spine does not mint a
            closed form. Symmetric nest stays product-only if you demand green
            everywhere — that was Analysis 1–2.
          </p>
        </article>
      </div>
    </main>
  );
}
