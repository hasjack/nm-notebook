import { Link } from "react-router-dom";

export function HomePage() {
  return (
    <main className="page home">
      <p className="eyebrow">Natural Mathematics · open notebook</p>
      <h1>The hire graph of the 3-free door</h1>
      <p className="lede">
        Current lead article. Exploring, not claiming breakthroughs. Formal
        companion in <code>lean/</code>.
      </p>

      <section className="home-lead">
        <p>
          For an odd prime <em>p</em> ≠ 3, the non-principal character χ₃ picks a
          unique <strong>3-free</strong> even neighbour{" "}
          <code>m₀(p) = p + χ₃(p)</code>. The other face{" "}
          <code>m₁(p)</code> is divisible by 6. Examples:{" "}
          <code>m₀(11) = 10</code>, <code>m₀(13) = 14</code>.
        </p>
        <p>
          Hire set <em>S</em> seeds 2 and takes odd prime factors ≠ 3 of those
          doors. By Dirichlet, every odd prime except 3 is eventually hired;{" "}
          <strong>3 never enters S</strong>. Spectra live on finite windows{" "}
          <em>G<sub>X</sub></em>: star on 2, directed gold arcs{" "}
          <em>p → q</em> when <em>q</em> | <em>m₀(p)</em>, undirected gold for
          Laplacians. Then λ<sub>max</sub>(H<sub>X</sub>) = <em>n</em>, and
          λ<sub>2</sub> = 1 exactly when undirected gold on the leaves is
          disconnected — visible on the computed windows through X = 200.
        </p>
        <p className="home-actions">
          <Link className="nav-link on" to="/hire">
            Open the hire dials
          </Link>{" "}
          <Link className="nav-link" to="/notes">
            Notes
          </Link>
        </p>
      </section>

      <h2>Alphabet shelf</h2>
      <p>
        The ongoing number line in <strong>e</strong>, <strong>i</strong>, and{" "}
        <strong>π</strong> — Walk, Lock i / Lock π, Basel, Catalogue. The hire
        graph grew out of this sandbox.
      </p>
      <p className="home-actions">
        <Link className="nav-link" to="/walk">
          Walk
        </Link>{" "}
        <Link className="nav-link" to="/lock-i">
          Lock i
        </Link>{" "}
        <Link className="nav-link" to="/lock-pi">
          Lock π
        </Link>{" "}
        <Link className="nav-link" to="/basel">
          Basel
        </Link>{" "}
        <Link className="nav-link" to="/catalogue">
          Catalogue
        </Link>
      </p>

      <h2>Lab</h2>
      <p>
        Probe pages demoted from the top bar — still reachable, not the public
        face. Use the Lab menu in the nav.
      </p>
    </main>
  );
}
