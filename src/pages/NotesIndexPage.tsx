import { Link } from "react-router-dom";

export function NotesIndexPage() {
  return (
    <main className="page notes lab-note-page">
      <h1>Notes</h1>
      <p className="lede">
        PDFs. The hire papers stay on the Hire shelf; this is the rest, plus
        a list of everything.
      </p>

      <h2>Hire</h2>
      <ul>
        <li>
          <Link to="/notes/hire-graph">The hire graph of the 3-free door</Link>
        </li>
        <li>
          <Link to="/notes/when-gold-disconnects">When gold disconnects</Link>
        </li>
      </ul>

      <h2>Standalone</h2>
      <ul>
        <li>
          <Link to="/notes/zeta-doors">
            Prime neighbours of zeta denominators
          </Link>
          . Same χ₃ neighbour as hire, different relation. Live hunt:{" "}
          <Link to="/zeta-doors">Zeta doors</Link>.
        </li>
      </ul>
    </main>
  );
}
