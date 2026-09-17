import { useEffect, useState } from "react";
import { NavLink, useLocation } from "react-router-dom";

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

const sections: { label: string; links: LinkItem[] }[] = [
  { label: "Issue", links: issue },
  { label: "Alphabet", links: alphabet },
  { label: "Lab", links: lab },
];

function Links({
  links,
  onNavigate,
  stacked,
}: {
  links: LinkItem[];
  onNavigate?: () => void;
  stacked?: boolean;
}) {
  return (
    <div className={stacked ? "nav-links stacked" : "nav-links"}>
      {links.map((l) => (
        <NavLink
          key={l.to}
          to={l.to}
          end={l.end ?? false}
          onClick={onNavigate}
          className={({ isActive }) => (isActive ? "nav-link on" : "nav-link")}
        >
          {l.label}
        </NavLink>
      ))}
    </div>
  );
}

export function Nav() {
  const [open, setOpen] = useState(false);
  const location = useLocation();

  useEffect(() => {
    setOpen(false);
  }, [location.pathname]);

  useEffect(() => {
    document.body.style.overflow = open ? "hidden" : "";
    return () => {
      document.body.style.overflow = "";
    };
  }, [open]);

  return (
    <>
      <header className="nav-bar">
        <button
          type="button"
          className="nav-burger"
          aria-label={open ? "Close menu" : "Open menu"}
          aria-expanded={open}
          onClick={() => setOpen((v) => !v)}
        >
          <span className={open ? "burger-lines open" : "burger-lines"}>
            <span />
            <span />
            <span />
          </span>
        </button>

        <NavLink to="/" end className="nav-brand">
          NM notebook
        </NavLink>

        <nav className="nav-desktop" aria-label="Primary">
          {sections.map((s) => (
            <div key={s.label} className="nav-group">
              <span className="nav-group-label">{s.label}</span>
              <Links links={s.links} />
            </div>
          ))}
        </nav>
      </header>

      <button
        type="button"
        className={open ? "nav-scrim on" : "nav-scrim"}
        aria-label="Dismiss menu"
        tabIndex={open ? 0 : -1}
        onClick={() => setOpen(false)}
      />

      <aside
        className={open ? "nav-drawer on" : "nav-drawer"}
        aria-hidden={!open}
      >
        <div className="nav-drawer-inner">
          {sections.map((s) => (
            <div key={s.label} className="nav-drawer-section">
              <div className="nav-group-label">{s.label}</div>
              <Links links={s.links} stacked onNavigate={() => setOpen(false)} />
            </div>
          ))}
        </div>
      </aside>
    </>
  );
}
