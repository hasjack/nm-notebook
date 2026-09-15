import { useMemo, useState } from "react";
import Plot from "../components/Plot";
import { fmt, fmtBase, baseFromSlider, sliderFromBase } from "../lib/format";
import {
  CREAM,
  MAROON,
  MUTED,
  NAVY,
  ORANGE,
  PAPER,
  layout3d,
  plotConfig,
  traces3d,
} from "../lib/plotTheme";
import { resultAt } from "../lib/walk";
import type { Data, Layout } from "plotly.js";

const PI2_OVER_6 = (Math.PI * Math.PI) / 6;

function partialZeta2(n: number): number {
  let s = 0;
  for (let k = 1; k <= n; k++) s += 1 / (k * k);
  return s;
}

type Approach = "spiral" | "sums" | "calligraphy" | "sine";

export function BaselPage() {
  const [approach, setApproach] = useState<Approach>("spiral");
  const [t, setT] = useState(() => sliderFromBase(Math.E));
  const [nTerms, setNTerms] = useState(10);
  const [product, setProduct] = useState(1); // i-factor · π-factor on the walk

  const base = baseFromSlider(t);
  const zVal = resultAt(product, base);
  // magnitude of base^(i·product·π) is always 1 for real product, base>0
  const mag = 1;
  const gap = PI2_OVER_6 - mag;

  const partial = partialZeta2(nTerms);
  const calligraphy = (() => {
    // principal Log(-1) = iπ → −i Log(-1) = π → squared / 6
    const logMinusOne = { re: 0, im: Math.PI }; // iπ
    const piVia = Math.PI; // −i * (iπ) = π
    return (piVia * piVia) / 6;
  })();

  const data3d = useMemo(
    () => traces3d(product, base),
    [product, base]
  );

  const unitVsBasel: Data[] = useMemo(() => {
    const theta = Array.from({ length: 361 }, (_, i) => (i * Math.PI) / 180);
    return [
      {
        type: "scatter",
        mode: "lines",
        x: theta.map((th) => Math.cos(th)),
        y: theta.map((th) => Math.sin(th)),
        line: { color: MAROON, width: 2 },
        name: "unit circle (|z|=1)",
      },
      {
        type: "scatter",
        mode: "markers+text",
        x: [-1, 1, 0, 0],
        y: [0, 0, 1, -1],
        text: ["−1 = e^(iπ)", "+1", "i", "−i"],
        textposition: "top center",
        marker: { size: 8, color: NAVY },
        name: "landmarks",
      },
      {
        type: "scatter",
        mode: "markers+text",
        x: [PI2_OVER_6],
        y: [0],
        text: [`π²/6 ≈ ${PI2_OVER_6.toFixed(4)}`],
        textposition: "top right",
        marker: { size: 11, color: ORANGE, symbol: "diamond" },
        name: "Basel",
      },
    ];
  }, []);

  const layoutUnit: Partial<Layout> = {
    paper_bgcolor: CREAM,
    plot_bgcolor: PAPER,
    margin: { l: 50, r: 30, t: 36, b: 45 },
    title: {
      text: "Where Basel sits relative to the spiral’s complex values",
      font: { size: 13, family: "Georgia, serif" },
    },
    xaxis: {
      title: { text: "real" },
      range: [-1.5, 2.2],
      zeroline: true,
      scaleanchor: "y",
    },
    yaxis: { title: { text: "imag" }, range: [-1.5, 1.5], zeroline: true },
    showlegend: true,
    legend: { orientation: "h", y: -0.2 },
    font: { family: "Georgia, Palatino, serif" },
    annotations: [
      {
        x: 0.2,
        y: -1.25,
        text: "spiral values live on the circle · π²/6 lives outside",
        showarrow: false,
        font: { size: 11, color: MUTED },
      },
    ],
  };

  const sumCurve: Data[] = useMemo(() => {
    const xs: number[] = [];
    const ys: number[] = [];
    for (let n = 1; n <= 80; n++) {
      xs.push(n);
      ys.push(partialZeta2(n));
    }
    return [
      {
        type: "scatter",
        mode: "lines+markers",
        x: xs,
        y: ys,
        line: { color: MAROON, width: 2 },
        marker: { size: 4, color: NAVY },
        name: "partial sums",
      },
      {
        type: "scatter",
        mode: "lines",
        x: [1, 80],
        y: [PI2_OVER_6, PI2_OVER_6],
        line: { color: ORANGE, width: 2, dash: "dash" },
        name: "π²/6",
      },
    ];
  }, []);

  const layoutSum: Partial<Layout> = {
    paper_bgcolor: CREAM,
    plot_bgcolor: PAPER,
    margin: { l: 55, r: 20, t: 36, b: 45 },
    title: {
      text: "Σ 1/n² climbing toward π²/6",
      font: { size: 13, family: "Georgia, serif" },
    },
    xaxis: { title: { text: "terms N" } },
    yaxis: { title: { text: "sum" }, range: [0.8, 1.8] },
    showlegend: true,
    legend: { orientation: "h", y: -0.2 },
    font: { family: "Georgia, Palatino, serif" },
  };

  const approaches: { id: Approach; label: string }[] = [
    { id: "spiral", label: "On the spiral?" },
    { id: "sums", label: "Partial sums" },
    { id: "calligraphy", label: "Calligraphy" },
    { id: "sine", label: "Sine product" },
  ];

  return (
    <main className="page">
      <h1>Basel — π²/6 in this number system</h1>
      <p className="lede">
        ζ(2) = 1 + 1/4 + 1/9 + … = <strong>π²/6 ≈ {PI2_OVER_6.toFixed(6)}</strong>.
        Play the approaches below. The honest headline: the Walk ribbon’s complex
        values always have length <strong>1</strong>; π²/6 does not sit on that
        ribbon — it sits on the real line outside the unit circle.
      </p>

      <div className="value">{PI2_OVER_6.toFixed(6)}</div>
      <div className="expr">π² / 6 · the Basel constant</div>
      <div className="rule">
        alphabet home: clean in π (even zeta) · proofs live in the i / Fourier /
        sine-product room
      </div>

      <div className="modes" style={{ margin: "1rem 0", display: "flex", gap: "0.5rem", flexWrap: "wrap" }}>
        {approaches.map((a) => (
          <button
            key={a.id}
            type="button"
            onClick={() => setApproach(a.id)}
            style={{
              background: approach === a.id ? "#1f4e79" : "#fffaf3",
              color: approach === a.id ? "#fff" : "#1a1a1a",
              border: "1px solid #e2d8c8",
              borderRadius: 8,
              padding: "0.4rem 0.85rem",
              font: "inherit",
              cursor: "pointer",
            }}
          >
            {a.label}
          </button>
        ))}
      </div>

      {approach === "spiral" && (
        <>
          <p className="hint">
            Dial base and the product of i-factor · π-factor. The readout is
            always a point on the unit circle in the complex plane — never π²/6.
            Orange diamond on the ribbon = current base; orange diamond on the
            flat plot = Basel, off the circle.
          </p>
          <div className="split-readout">
            <div>
              <div className="kv-label">spiral value</div>
              <div className="kv-value" style={{ fontSize: "1.1rem" }}>
                {zVal}
              </div>
            </div>
            <div>
              <div className="kv-label">|value|</div>
              <div className="kv-value">{fmt(mag, 0)}</div>
            </div>
            <div>
              <div className="kv-label">π²/6</div>
              <div className="kv-value">{fmt(PI2_OVER_6, 4)}</div>
            </div>
            <div>
              <div className="kv-label">gap</div>
              <div className="kv-value">{fmt(gap, 4)}</div>
            </div>
          </div>
          <div className="graph3d">
            <Plot
              data={data3d}
              layout={layout3d}
              config={plotConfig}
              style={{ width: "100%", height: "100%" }}
              useResizeHandler
            />
          </div>
          <div className="graph2d">
            <Plot
              data={unitVsBasel}
              layout={layoutUnit}
              config={plotConfig}
              style={{ width: "100%", height: "100%" }}
              useResizeHandler
            />
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
              <span>i-factor · π-factor</span>
              <span>{fmt(product, 2)}</span>
            </label>
            <input
              type="range"
              min={-2}
              max={4}
              step={0.01}
              value={product}
              onChange={(e) => setProduct(parseFloat(e.target.value))}
            />
            <p className="hint">
              At base e and product 1 you get −1 — that’s π as a half-turn, not
              π as an area constant. Squaring that half-turn’s angle measure and
              dividing by 6 is a different geometric job (Basel), living off the
              circle.
            </p>
            <div className="actions">
              <button
                type="button"
                onClick={() => {
                  setT(sliderFromBase(Math.E));
                  setProduct(1);
                }}
              >
                Euler landing (−1)
              </button>
            </div>
          </div>
        </>
      )}

      {approach === "sums" && (
        <>
          <p className="hint">
            Stay in the alphabet’s π-room by watching the sum approach π²/6.
            No spiral point equals the sum; the sum is a real climbing toward a
            π-native closed form.
          </p>
          <div className="split-readout">
            <div>
              <div className="kv-label">N terms</div>
              <div className="kv-value">{nTerms}</div>
            </div>
            <div>
              <div className="kv-label">partial sum</div>
              <div className="kv-value">{fmt(partial, 6)}</div>
            </div>
            <div>
              <div className="kv-label">π²/6</div>
              <div className="kv-value">{fmt(PI2_OVER_6, 6)}</div>
            </div>
            <div>
              <div className="kv-label">error</div>
              <div className="kv-value">
                {fmt(PI2_OVER_6 - partial, 6)}
              </div>
            </div>
          </div>
          <div className="graph2d" style={{ height: 360 }}>
            <Plot
              data={sumCurve}
              layout={layoutSum}
              config={plotConfig}
              style={{ width: "100%", height: "100%" }}
              useResizeHandler
            />
          </div>
          <div className="panel">
            <label className="row">
              <span>terms N</span>
              <span>{nTerms}</span>
            </label>
            <input
              type="range"
              min={1}
              max={80}
              step={1}
              value={nTerms}
              onChange={(e) => setNTerms(parseInt(e.target.value, 10))}
            />
            <p className="hint">
              Video beat: stack unit squares 1, 1/4, 1/9, … until the pile’s
              height is π²/6 — then cut to the half-turn −1 and say “same letter
              π, different job.”
            </p>
          </div>
        </>
      )}

      {approach === "calligraphy" && (
        <>
          <p className="hint">
            Rewrite π via the principal log: π = −i Log(−1). Then π²/6 becomes
            calligraphy in {"{e, i}"} — true on the branch, but Log(−1) already
            carried π inside.
          </p>
          <div className="value">{calligraphy.toFixed(6)}</div>
          <div className="expr">
            (−i Log(−1))² / 6 · with Log(−1) = iπ
          </div>
          <div className="rule">
            grade: calligraphy · same number, renamed · see Catalogue
          </div>
          <div className="panel">
            <p>
              Step by step: e^(iπ) = −1 ⇒ take Log ⇒ Log(−1) = iπ (principal) ⇒
              multiply by −i ⇒ π. Square and divide by six. You’ve written Basel
              without the letter π appearing, while still using the half-turn.
            </p>
            <p className="hint">
              For the video: flash circle area A = −i Log(−1) r² next to this —
              same trick family. Then ask: did we leave the island, or just
              change fonts?
            </p>
          </div>
        </>
      )}

      {approach === "sine" && (
        <>
          <p className="hint">
            Euler’s engine for Basel: sin(x) = x ∏_n (1 − x²/(n² π²)). Expand and
            match the x³ coefficient (or use Fourier) to get Σ 1/n² = π²/6. Here
            π marks the zeros — a different dial job than “half-turn to −1.”
          </p>
          <div className="split-readout">
            <div>
              <div className="kv-label">zeros</div>
              <div className="kv-value" style={{ fontSize: "1rem" }}>
                ±π, ±2π, …
              </div>
            </div>
            <div>
              <div className="kv-label">product</div>
              <div className="kv-value" style={{ fontSize: "0.95rem" }}>
                ∏ (1 − x²/(n²π²))
              </div>
            </div>
            <div>
              <div className="kv-label">pays out</div>
              <div className="kv-value">π²/6</div>
            </div>
            <div>
              <div className="kv-label">grade</div>
              <div className="kv-value">clean</div>
            </div>
          </div>
          <div className="panel">
            <p>
              Approaches in your system, ranked:
            </p>
            <ol className="benefits">
              <li>
                <strong>Spiral / half-turn</strong> — shows π as rotation to −1;
                does <em>not</em> host π²/6 as a point on the ribbon.
              </li>
              <li>
                <strong>Partial sums</strong> — watch the real series climb to a
                π-native closed form (clean alphabet, arithmetic path).
              </li>
              <li>
                <strong>Sine product / Fourier</strong> — the classical workshop
                where i and π earn ζ(2); best “why π²?” story.
              </li>
              <li>
                <strong>Calligraphy</strong> — (−i Log(−1))²/6 for the font
                trick; pair with circle area for the video twist.
              </li>
            </ol>
            <p className="hint">
              Dial takeaway: Lock i / Lock π move factors in the exponent so the
              landing stays −1. Basel asks a different question — what real
              height does an infinite sum of reciprocal squares reach — and the
              answer happens to be written with the same letter π.
            </p>
          </div>
        </>
      )}
    </main>
  );
}
