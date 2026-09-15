export function NotesPage() {
  return (
    <main className="page notes">
      <h1>Benefits &amp; notes</h1>
      <p className="lede">
        A number line spoken only in <strong>e</strong>, <strong>i</strong>, and{" "}
        <strong>π</strong>. Jack is exploring — not claiming breakthroughs. Core
        picture:
      </p>
      <blockquote>
        Envisage base<sup>iπ</sup> when the base is free (not held at e). Then
        lock i and see what happens to π; lock π and see what happens to i.
        Landing on −1 means the free factor times ln(base) hits an odd integer.
      </blockquote>
      <p>
        Write the exponent as <strong>α · i · βπ</strong>. Walk holds α = β = 1
        and varies base. Lock i holds α = 1 and retunes the π-factor β. Lock π
        holds β = 1 and retunes the i-factor α. Solve recovers the base from an
        odd branch and the free factor.
      </p>

      <h2>Benefits of this number-line view</h2>
      <ol className="benefits">
        <li>
          <strong>Makes Euler’s −1 a constraint, not a slogan.</strong> The famous
          landing is not a magic sticker on e; it is the statement that (with one
          factor locked at 1) the free factor times ln(base) must hit an odd
          integer. You can <em>see</em> when you are on −1 and when you are not.
        </li>
        <li>
          <strong>Variable base first.</strong> The favourite walk is classical
          iπ with the base dial in ln-space — powers of e as marks — so e is one
          point on a continuous ribbon, not the only allowed world.
        </li>
        <li>
          <strong>Lock i vs lock π as two experiments.</strong> Holding the
          i-factor fixed and retuning π (or the reverse) is the whole point of
          the explorer: watch one constant move while the other stays named.
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
          hyperbolas — discrete branches, not a continuum of −1 answers.
        </li>
        <li>
          <strong>Singularity at base = 1.</strong> ln(1) = 0, so no finite
          i-factor or π-factor can satisfy the lock. The base slider skips a hole
          around 1; the 2D locus has a vertical asymptote there.
        </li>
        <li>
          <strong>
            3D walk shows the continuous story; locus shows the discrete
            constraint.
          </strong>{" "}
          The cream Plotly ribbon is every base at a fixed product of factors —
          a continuous complex journey. The 2D locus is the thin set of
          (ln base, free-factor) pairs that actually land on −1.
        </li>
      </ol>

      <h2>What we found experimentally in the demo</h2>
      <ul>
        <li>
          <strong>Smooth sampling matters.</strong> Uniform steps in base look
          lumpy once the winding grows; sampling uniformly in ln(base) keeps the
          3D walk a clean ribbon instead of a chord polygon.
        </li>
        <li>
          <strong>Euler is one point on a hyperbola.</strong> At base e and odd = 1
          with either factor locked at 1 you recover the classical landing — but
          the same branch also passes through (e³, free-factor = ⅓), and so on.
        </li>
        <li>
          <strong>Even integers land on +1</strong>, not −1. Freeing a factor and
          sliding through 0, 1, 2 shows the readout flip between 1, −1, and the
          imaginary axis.
        </li>
        <li>
          <strong>Negative bases of the log are excluded</strong> here (real
          positive base only). Crossing base = 1 still feels like a wall; the
          singularity is not a UI bug.
        </li>
      </ul>

      <h2>Adjacent curiosity (not a claim)</h2>
      <p>
        Jack arrived at this explorer via the square reciprocal sum, the cube reciprocal sum, and the growth along a critical line.
        The kinship is thematic, not a derivation — a light shoreline touch:
      </p>
      <ul>
        <li>
          <strong>Complex log</strong> is the same function that turns
          multiplicative structure into additive structure on the e-line we plot.
        </li>
        <li>
          The <strong>critical strip</strong> is another place where a continuous
          complex object along a line is constrained by discrete arithmetic (zeros),
          analogous in spirit to a continuous walk constrained by odd integers.
        </li>
        <li>
          <strong>Special heights</strong> (ordinates of zeros, or Apéry’s the cube reciprocal sum /
          the Basel the square reciprocal sum shoreline) feel nearby when you are already staring at
          distinguished real parameters on a log-scaled axis.
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
