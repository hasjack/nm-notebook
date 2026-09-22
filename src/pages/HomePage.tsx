import { Link } from "react-router-dom";

export function HomePage() {
  return (
    <main className="page home">
      <h1>The hire graph of the 3-free door</h1>
      <p className="lede">
        Of the two even neighbours of an odd prime ≠ 3, exactly one is 3-free.
        Ownership of those doors makes a graph. Lean under <code>lean/</code>.
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
          <em>
            G<sub>X</sub>
          </em>
          : star on 2, directed gold arcs <em>p → q</em> when <em>q</em> |{" "}
          <em>m₀(p)</em>, undirected gold for Laplacians. Then λ<sub>max</sub>(H
          <sub>X</sub>) = <em>n</em>, and λ<sub>2</sub> = 1 exactly when
          undirected gold on the leaves is disconnected — visible on the
          computed windows through X = 200.
        </p>
        <p className="home-actions">
          <Link className="nav-link on" to="/hire">
            Introduction
          </Link>
          <a className="nav-link" href="/paper/hire-graph-of-the-3-free-door.pdf">
            PDF
          </a>
          <a
            className="nav-link"
            href="https://github.com/hasjack/nm-notebook/tree/master/lean"
          >
            Lean
          </a>
          <Link className="nav-link" to="/certificates">
            Certificates
          </Link>
        </p>
      </section>
    </main>
  );
}
