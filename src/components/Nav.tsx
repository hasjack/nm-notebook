import { NavLink } from "react-router-dom";

const links = [
  { to: "/", label: "Walk", end: true },
  { to: "/lock", label: "Lock −1" },
  { to: "/split", label: "Split i & π" },
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
