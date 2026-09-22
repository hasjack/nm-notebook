export function NotesPage() {
  return (
    <main className="page notes">
      <h1>Benefits &amp; notes</h1>
      <p className="lede">
        A number line spoken only in <strong>e</strong>, <strong>i</strong>, and{" "}
        <strong>π</strong>. Core picture:
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

      <h2>Cast &amp; newer tabs</h2>
      <ul>
        <li>
          <strong>Return</strong> — 0 and a full turn as one character: back to
          where it started.
        </li>
        <li>
          <strong>Beacons / Rotation / Magnitude</strong> — integer
          choreography, turns as a number line, real σ off the cylinder.
        </li>
        <li>
          <strong>Toys</strong> — Physics (waves in the same letters); Bell (
          <code>(σ, p)</code> local CHSH toy); Atlas (orientation-switching
          quadratic map).
        </li>
      </ul>
      
      <h2>Formal (Lean)</h2>
      <p>
        The hire-graph notes have a Lean 4 + Mathlib companion under{" "}
        <code>lean/Hire/</code> — doors, finite hire set, 3 never hired, gold
        arcs, the Laplacian cone, and Layer D: λ<sub>2</sub> = 1 iff gold on the
        leaves is disconnected. <code>GoldBridge</code> is strong Q2 with 0 sorry;
        <code>GoldDisconnects</code> is the sequel scaffolding; Dirichlet
        infinitude of S is still a stub. Built with <code>lake build</code> — not
        part of the Vite bundle. See{" "}
        <a href="https://github.com/hasjack/nm-notebook/tree/master/lean">
          lean/
        </a>
        .
      </p>
    </main>
  );
}
