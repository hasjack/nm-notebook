import { Link } from "react-router-dom";

export function NotesIndexPage() {
  return (
    <main className="page notes lab-note-page">
      <h1>Notes</h1>
      <ul>
        <li>
          <Link to="/notes/hire-graph">The hire graph of the 3-free door</Link>
        </li>
        <li>
          <Link to="/notes/when-gold-disconnects">When gold disconnects</Link>
        </li>
        <li>
          <Link to="/notes/zeta-doors">
            Prime neighbours of zeta denominators
          </Link>
        </li>
      </ul>
    </main>
  );
}
