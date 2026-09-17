import { NavLink } from "react-router-dom";

const links = [
  { to: "/", label: "Walk", end: true },
  { to: "/lock-i", label: "Lock i" },
  { to: "/lock-pi", label: "Lock π" },
  { to: "/free", label: "Free" },
  { to: "/magnitude", label: "Magnitude" },
  { to: "/beacons", label: "Beacons" },
  { to: "/rotation", label: "Rotation" },
  { to: "/physics", label: "Physics" },
  { to: "/basel", label: "Basel" },
  { to: "/analysis-1", label: "A1" },
  { to: "/analysis-2", label: "A2" },
  { to: "/analysis-3", label: "A3" },
  { to: "/analysis-4", label: "A4" },
  { to: "/analysis-5", label: "A5" },
  { to: "/solve", label: "Solve" },
  { to: "/primes", label: "Primes" },
  { to: "/super-primes", label: "Super" },
  { to: "/unclaimed", label: "Unclaimed" },
  { to: "/beacon-super", label: "Beacon×S" },
  { to: "/suspect-bench", label: "Suspect" },
  { to: "/missed", label: "Missed" },
  { to: "/spectrum", label: "Spectrum" },
  { to: "/pm1", label: "±1" },
  { to: "/hire", label: "Hire" },
  { to: "/signed-doors", label: "±Doors" },
  { to: "/alphabet-spiral", label: "α-spiral" },
  { to: "/count", label: "Count" },
  { to: "/catalogue", label: "Catalogue" },
  { to: "/notes", label: "Notes" },
] as const;

export function Nav() {
  return (
    <nav className="nav">
      <div className="nav-brand">e-walk</div>
      <div className="nav-links">
        {links.map((l) => (
          <NavLink
            key={l.to}
            to={l.to}
            end={"end" in l ? l.end : false}
            className={({ isActive }) => (isActive ? "nav-link on" : "nav-link")}
          >
            {l.label}
          </NavLink>
        ))}
      </div>
    </nav>
  );
}
