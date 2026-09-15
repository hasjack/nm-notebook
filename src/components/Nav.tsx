import { NavLink } from "react-router-dom";

const links = [
  { to: "/", label: "Walk", end: true },
  { to: "/lock-i", label: "Lock i" },
  { to: "/lock-pi", label: "Lock π" },
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
