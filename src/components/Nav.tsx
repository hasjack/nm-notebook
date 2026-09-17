import { NavLink } from "react-router-dom";

type LinkItem = { to: string; label: string; end?: boolean };

const issue: LinkItem[] = [
  { to: "/", label: "Lead", end: true },
  { to: "/hire", label: "Hire" },
];

const alphabet: LinkItem[] = [
  { to: "/walk", label: "Walk" },
  { to: "/lock-i", label: "Lock i" },
  { to: "/lock-pi", label: "Lock π" },
  { to: "/basel", label: "Basel" },
  { to: "/free", label: "Free" },
  { to: "/solve", label: "Solve" },
  { to: "/catalogue", label: "Catalogue" },
  { to: "/notes", label: "Notes" },
];

const lab: LinkItem[] = [
  { to: "/magnitude", label: "Magnitude" },
  { to: "/beacons", label: "Beacons" },
  { to: "/rotation", label: "Rotation" },
  { to: "/physics", label: "Physics" },
  { to: "/analysis-1", label: "A1" },
  { to: "/analysis-2", label: "A2" },
  { to: "/analysis-3", label: "A3" },
  { to: "/analysis-4", label: "A4" },
  { to: "/analysis-5", label: "A5" },
  { to: "/primes", label: "Primes" },
  { to: "/super-primes", label: "Super" },
  { to: "/unclaimed", label: "Unclaimed" },
  { to: "/beacon-super", label: "Beacon×S" },
  { to: "/suspect-bench", label: "Suspect" },
  { to: "/missed", label: "Missed" },
  { to: "/spectrum", label: "Spectrum" },
  { to: "/pm1", label: "±1" },
  { to: "/signed-doors", label: "±Doors" },
  { to: "/alphabet-spiral", label: "α-spiral" },
  { to: "/count", label: "Count" },
];

function Group({
  label,
  links,
}: {
  label: string;
  links: LinkItem[];
}) {
  return (
    <div className="nav-group">
      <span className="nav-group-label">{label}</span>
      <div className="nav-links">
        {links.map((l) => (
          <NavLink
            key={l.to}
            to={l.to}
            end={l.end ?? false}
            className={({ isActive }) => (isActive ? "nav-link on" : "nav-link")}
          >
            {l.label}
          </NavLink>
        ))}
      </div>
    </div>
  );
}

export function Nav() {
  return (
    <nav className="nav">
      <NavLink to="/" end className="nav-brand">
        NM notebook
      </NavLink>
      <div className="nav-groups">
        <Group label="Issue" links={issue} />
        <Group label="Alphabet" links={alphabet} />
        <details className="nav-group nav-lab">
          <summary className="nav-group-label">Lab</summary>
          <div className="nav-links">
            {lab.map((l) => (
              <NavLink
                key={l.to}
                to={l.to}
                className={({ isActive }) =>
                  isActive ? "nav-link on" : "nav-link"
                }
              >
                {l.label}
              </NavLink>
            ))}
          </div>
        </details>
      </div>
    </nav>
  );
}
