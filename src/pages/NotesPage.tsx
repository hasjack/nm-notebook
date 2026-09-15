export function NotesPage() {
  return (
    <main className="page notes">
      <h1>Benefits &amp; notes</h1>
      <p className="lede">
        A number line spoken only in <strong>e</strong>, <strong>i</strong>, and{" "}
        <strong>π</strong>. Core identity:
      </p>
      <blockquote>
        base^(k · i · π) = −1 ⇔ k · ln(base) = odd integer (±1, ±3, ±5, …)
      </blockquote>
      <p>
        In the split view we write the same strength as <strong>k = α·β</strong>,
        so the expression becomes base^(α · i · βπ), with the lock−1 rule{" "}
        <strong>αβ · ln(base) = odd</strong>.
      </p>

      <h2>Benefits of this number-line view</h2>
      <ol className="benefits">
        <li>
          <strong>Makes Euler’s −1 a constraint, not a slogan.</strong> The famous
          landing is not a magic sticker on e; it is the statement that the
          composite strength k (or αβ) times ln(base) must hit an odd integer. You
          can <em>see</em> when you are on −1 and when you are not.
        </li>
        <li>
          <strong>ln(base) as “how many e-steps.”</strong> Spacing the walk in
          ln-space means each unit on the axis is one multiplication by e. Base e
          sits at ln = 1; e³ at 3; 1/e at −1. The number line is literally counted
          in e.
        </li>
        <li>
          <strong>Odd integers as the only landings for −1.</strong> Cosine equals
          −1 only at odd multiples of π. That is why the locus is a family of
          hyperbolas k · ln(base) = ±1, ±3, ±5… — discrete branches, not a
          continuum of −1 answers.
        </li>
        <li>
          <strong>Singularity at base = 1.</strong> ln(1) = 0, so no finite k (or
          αβ) can satisfy the lock. The demo’s base slider skips a hole around 1;
          the 2D locus has a vertical asymptote there. Base 1 is not “almost e” —
          it is a different kind of point.
        </li>
        <li>
          <strong>k (or αβ) as retuning “i·π strength” when base changes.</strong>{" "}
          Grow the base and the lock automatically shrinks k so the product with
          ln(base) stays on the chosen odd branch. The Split dial then trades that
          same product between α and β without leaving −1.
        </li>
        <li>
          <strong>
            3D walk shows the continuous story; locus shows the discrete
            constraint.
          </strong>{" "}
          The cream Plotly ribbon is every base, one fixed k — a continuous complex
          journey. The 2D locus is the thin set of (ln base, k) pairs that actually
          land on −1. Together they separate “what the walk does” from “where −1 is
          allowed.”
        </li>
      </ol>

      <h2>What we found experimentally in the demo</h2>
      <ul>
        <li>
          <strong>Smooth sampling matters.</strong> Uniform steps in base look
          lumpy once |k| grows; sampling uniformly in ln(base) and scaling point
          count with |k| keeps the 3D walk a clean ribbon instead of a chord
          polygon.
        </li>
        <li>
          <strong>Euler is one point on a hyperbola.</strong> At base e and odd = 1
          you get k = 1 again — but the same branch also passes through (e³, k =
          ⅓), (e⁵, k = ⅕), and so on. Snap buttons make that tangible.
        </li>
        <li>
          <strong>Even integers land on +1</strong>, not −1. Sliding free k through
          0, 1, 2 shows the readout flip between 1, −1, and the imaginary axis (k =
          ½ → i at base e).
        </li>
        <li>
          <strong>α/β split is cosmetic for the angle, useful for storytelling.</strong>{" "}
          Because the angle depends only on the product αβ, the share dial does not
          change the complex value under lock−1 — it only redistributes the same
          strength between the “i” and “π” factors.
        </li>
        <li>
          <strong>Negative bases of the log are excluded</strong> here (real
          positive base only). Crossing base = 1 still feels like a wall; the
          singularity is not a UI bug.
        </li>
      </ul>

      <h2>Adjacent curiosity (not a claim)</h2>
      <p>
        Jack arrived at this explorer via ζ(3) and the Riemann hypothesis. The
        kinship is thematic, not a derivation:
      </p>
      <ul>
        <li>
          <strong>Complex log</strong> is the same function that turns
          multiplicative structure into additive structure on the e-line we plot.
        </li>
        <li>
          The <strong>critical strip</strong> is another place where a continuous
          complex object (ζ(s)) is constrained by discrete arithmetic (zeros),
          analogous in spirit to a continuous walk constrained by odd integers.
        </li>
        <li>
          <strong>Special heights</strong> (ordinates of zeros, or Apéry’s ζ(3))
          feel nearby when you are already staring at distinguished real parameters
          on a log-scaled axis.
        </li>
      </ul>
      <p className="hint">
        None of that is a path to a proof or a closed form. It is why the toy feels
        like the right sandbox — neighbouring furniture in the same room, not a
        bridge between theorems.
      </p>
    </main>
  );
}
