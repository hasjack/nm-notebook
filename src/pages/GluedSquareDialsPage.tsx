import { useMemo, useState } from "react";
import { Link } from "react-router-dom";

const TAU = 2 * Math.PI;

function formatDial(value: number) {
  return value.toFixed(2);
}

function modUnit(value: number) {
  return ((value % 1) + 1) % 1;
}

function svgPath(points: [number, number][]) {
  return `M${points.map(([x, y]) => `${x.toFixed(2)},${y.toFixed(2)}`).join(" L")}`;
}

function curve(fn: (t: number) => [number, number]) {
  return svgPath(Array.from({ length: 101 }, (_, i) => fn((i * TAU) / 100)));
}

function torusPoint(u: number, v: number): [number, number] {
  const radius = 1.6 + 0.65 * Math.cos(v);
  const a = radius * Math.cos(u);
  const b = radius * Math.sin(u);
  const c = 0.65 * Math.sin(v);
  return [130 + 48 * (0.85 * a - 0.52 * b), 125 + 48 * (0.3 * a + 0.49 * b - 0.82 * c)];
}

function curveY(x: number) {
  return Math.sqrt(x ** 3 - 2);
}

function tangentY(x: number) {
  return 5 + 2.7 * (x - 3);
}

function EllipticTangentSvg() {
  const xMin = 1.15;
  const xMax = 3.35;
  const yMin = -1.3;
  const yMax = 5.6;
  const width = 340;
  const height = 260;
  const pad = 24;

  const sx = (x: number) => pad + ((x - xMin) / (xMax - xMin)) * (width - 2 * pad);
  const sy = (y: number) => height - pad - ((y - yMin) / (yMax - yMin)) * (height - 2 * pad);
  const pathFor = (sign: 1 | -1) =>
    svgPath(
      Array.from({ length: 96 }, (_, i) => {
        const x = xMin + ((xMax - xMin) * i) / 95;
        return [sx(x), sy(sign * curveY(x))];
      }),
    );

  const p = { x: 3, y: 5, label: "P" };
  const q = { x: 1.29, y: 0.383, label: "Q" };
  const twoP = { x: 1.29, y: -0.383, label: "2P" };
  const tangentA = { x: 1.16, y: tangentY(1.16) };
  const tangentB = { x: 3.3, y: tangentY(3.3) };

  return (
    <svg viewBox={`0 0 ${width} ${height}`} role="img" aria-label="Tangent and reflection on y squared equals x cubed minus 2">
      <path className="elliptic-axis" d={`M${sx(xMin)},${sy(0)}H${sx(xMax)}`} />
      <path className="elliptic-axis" d={`M${sx(1.26)},${sy(yMin)}V${sy(yMax)}`} />
      <path className="elliptic-curve" d={pathFor(1)} />
      <path className="elliptic-curve elliptic-curve-lower" d={pathFor(-1)} />
      <path
        className="elliptic-tangent"
        d={`M${sx(tangentA.x)},${sy(tangentA.y)}L${sx(tangentB.x)},${sy(tangentB.y)}`}
      />
      <path className="elliptic-reflect" d={`M${sx(q.x)},${sy(q.y)}V${sy(twoP.y)}`} />
      {[p, q, twoP].map((point) => (
        <g key={point.label}>
          <circle className="point" cx={sx(point.x)} cy={sy(point.y)} r="5" />
          <text x={sx(point.x) + 8} y={sy(point.y) - 8}>
            {point.label}
          </text>
        </g>
      ))}
      <text x={sx(2.15)} y={sy(5.25)} textAnchor="middle">
        tangent at P
      </text>
      <text x={sx(1.58)} y={sy(-0.95)} textAnchor="middle">
        reflect Q across y = 0
      </text>
    </svg>
  );
}

function DialSvg({ x, y }: { x: number; y: number }) {
  const dials = [
    { cx: 75, cy: 85, f: x, className: "horizontal", label: "x dial" },
    { cx: 185, cy: 155, f: y, className: "vertical", label: "y dial" },
  ];

  return (
    <svg viewBox="0 0 260 240" role="img" aria-label="Independent horizontal and vertical circle readings">
      {dials.map((dial) => {
        const angle = TAU * dial.f;
        const px = dial.cx + 47 * Math.cos(angle);
        const py = dial.cy - 47 * Math.sin(angle);
        return (
          <g key={dial.label}>
            <circle className={dial.className} cx={dial.cx} cy={dial.cy} r="47" />
            <path className={dial.className} d={`M${dial.cx},${dial.cy}L${px},${py}`} />
            <circle className="point" cx={px} cy={py} r="5" />
            <text x={dial.cx} y={dial.cy + 67} textAnchor="middle">
              {dial.label}
            </text>
          </g>
        );
      })}
    </svg>
  );
}

function TorusSvg({ x, y }: { x: number; y: number }) {
  const { structure, horizontal, vertical, point } = useMemo(() => {
    const structurePaths: { id: string; d: string }[] = [];
    for (let j = 0; j < 12; j += 1) {
      const angle = (j * TAU) / 12;
      structurePaths.push({ id: `u-${j}`, d: curve((t) => torusPoint(t, angle)) });
      structurePaths.push({ id: `v-${j}`, d: curve((t) => torusPoint(angle, t)) });
    }
    return {
      structure: structurePaths,
      horizontal: curve((t) => torusPoint(t, TAU * y)),
      vertical: curve((t) => torusPoint(TAU * x, t)),
      point: torusPoint(TAU * x, TAU * y),
    };
  }, [x, y]);

  return (
    <svg viewBox="0 0 260 240" role="img" aria-label="The same two angles mark a point on a wireframe torus">
      {structure.map((path) => (
        <path key={path.id} className="structure" d={path.d} />
      ))}
      <path className="horizontal" d={horizontal} />
      <path className="vertical" d={vertical} />
      <circle className="point" cx={point[0]} cy={point[1]} r="6" />
      <text x="130" y="232" textAnchor="middle">
        x: around · y: through the tube
      </text>
    </svg>
  );
}

export function GluedSquareDialsPage() {
  const [x, setX] = useState(0.85);
  const [y, setY] = useState(0.3);

  const fx = modUnit(x);
  const fy = modUnit(y);

  return (
    <main className="page glued-dials-page">
      <p className="eyebrow">Alphabet torus</p>
      <h1>Glued square dials</h1>
      <p className="lede">
        A single circular dial forgets whole turns. Two independent dials read a
        complex point <code>z = x + iy</code> as{" "}
        <code>z ↦ (e^(2πix), e^(2πiy))</code>. The Lean file records the same
        move: quotient the complex plane by the square lattice, then prove the
        dial reading is independent of the chosen representative.
      </p>

      <div className="value">ℂ / (ℤ + ℤi)</div>
      <div className="expr">
        <code>SamePoint 1 Complex.I</code> · <code>squareDials</code> ·{" "}
        <code>quotientDials</code>
      </div>

      <section className="glued-dials-controls" aria-label="Dial controls">
        <label className="glued-dials-slider">
          <span>
            Horizontal turns <strong>x = {formatDial(x)}</strong>
          </span>
          <input
            type="range"
            min="0"
            max="2"
            step="0.01"
            value={x}
            onChange={(event) => setX(Number(event.target.value))}
          />
        </label>
        <label className="glued-dials-slider">
          <span>
            Vertical turns <strong>y = {formatDial(y)}</strong>
          </span>
          <input
            type="range"
            min="0"
            max="2"
            step="0.01"
            value={y}
            onChange={(event) => setY(Number(event.target.value))}
          />
        </label>
      </section>

      <p className="rule">
        Example: <code>0.85 + 0.30i</code>,{" "}
        <code>1.85 + 0.30i</code>, and <code>0.85 + 1.30i</code> are the same
        glued-square point, because shifting by <code>1</code> or{" "}
        <code>i</code> just makes a whole turn on one dial.
      </p>

      <section className="glued-dials-grid" aria-label="One point in three views">
        <article>
          <h2>Glued square</h2>
          <svg viewBox="0 0 260 240" role="img" aria-label="A point wraps to the opposite edge of a unit square">
            <path className="horizontal" d="M35 205H225 M35 15H225" />
            <path className="vertical" d="M35 15V205 M225 15V205" />
            <text x="130" y="232" textAnchor="middle">
              left ↔ right · bottom ↔ top
            </text>
            <circle className="point" cx={35 + 190 * fx} cy={205 - 190 * fy} r="6" />
          </svg>
        </article>
        <article>
          <h2>Two circle readings</h2>
          <DialSvg x={fx} y={fy} />
        </article>
        <article>
          <h2>Doughnut picture</h2>
          <TorusSvg x={fx} y={fy} />
        </article>
      </section>

      <section className="catalogue-list">
        <article className="catalogue-card grade-clean">
          <header className="catalogue-card-head">
            <h2>What Lean fixes</h2>
            <span className="grade-pill grade-clean">quotient</span>
          </header>
          <p>
            <code>squareDials_of_samePoint</code> says integer shifts in either
            direction leave the two readings unchanged. That is the formal
            version of gluing opposite edges.
          </p>
        </article>
        <article className="catalogue-card grade-calligraphy">
          <header className="catalogue-card-head">
            <h2>The converse</h2>
            <span className="grade-pill grade-calligraphy">dials</span>
          </header>
          <p>
            <code>squareDials_eq_iff</code> records the sharper statement: equal
            dial readings mean exactly the same square-lattice point.
          </p>
        </article>
        <article className="catalogue-card grade-clean">
          <header className="catalogue-card-head">
            <h2>Continuity</h2>
            <span className="grade-pill grade-clean">topology</span>
          </header>
          <p>
            <code>continuous_squareDials</code>, <code>continuous_point</code>,
            and <code>continuous_quotientDials</code> keep the visual story
            honest: moving the point moves the readings continuously before and
            after gluing.
          </p>
        </article>
      </section>

      <section className="glued-dials-note">
        <h2>What is not formalised yet</h2>
        <p>
          The doughnut drawing is the intended geometric identification. The Lean
          checkpoint has not yet proved surjectivity onto the product of unit
          circles, nor a homeomorphism between the quotient and that product.
        </p>
      </section>

      <section className="elliptic-lab" aria-labelledby="elliptic-lab-title">
        <p className="eyebrow">Companion lab</p>
        <h2 id="elliptic-lab-title">Exact tangent on y² = x³ − 2</h2>
        <p>
          The rational-point toy takes <code>P = (3, 5)</code>, draws the tangent
          line, finds the second intersection{" "}
          <code>Q = (129/100, 383/1000)</code>, then reflects it to{" "}
          <code>2P = (129/100, -383/1000)</code>.
        </p>
        <div className="elliptic-lab-layout">
          <article className="elliptic-figure">
            <EllipticTangentSvg />
          </article>
          <article className="elliptic-copy">
            <h3>Certified algebra</h3>
            <p>
              <code>
                (x^3 - 2) - (5 + 27/10 * (x - 3))^2 = (x - 3)^2 * (x - 129/100)
              </code>
            </p>
            <p>
              <code>EllipticToy.lean</code> verifies the two curve points, the
              factorisation, the reflection, and that <code>129/100</code> is not
              an integer.
            </p>
          </article>
        </div>
        <p>
          The standard mathematical next sentence is Nagell-Lutz: because the
          doubled point has nonintegral rational x-coordinate, <code>P</code> is
          not torsion, so the curve has rank at least one. This Lean example does
          not yet connect to Mathlib's elliptic-curve group or formalise that
          infinite-order argument. No BSD result is claimed here.
        </p>
        <p>
          The point of the lab is concrete and visual: topology gives the
          glued-square dials, rational arithmetic gives an exact tangent move,
          and the lattice-to-cubic bridge remains background motivation rather
          than a constructed Lean object.
        </p>
      </section>

      <p className="home-actions">
        <Link to="/alphabet">Back to Alphabet</Link>
        <Link to="/torus">Torus notes</Link>
      </p>
    </main>
  );
}
