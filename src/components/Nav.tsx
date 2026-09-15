import { NavLink } from "react-router-dom";

const links = [
  { to: "/", label: "Walk", end: true },
  { to: "/lock-i", label: "Lock i" },
  { to: "/lock-pi", label: "Lock π" },
  { to: "/free", label: "Free" },
  { to: "/basel", label: "Basel" },
  { to: "/analysis-1", label: "A1" },
  { to: "/analysis-2", label: "A2" },
  { to: "/analysis-3", label: "A3" },
  { to: "/solve", label: "Solve" },
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
