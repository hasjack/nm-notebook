import { useEffect, useState, type ReactNode } from "react";
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

function isDesktop(): boolean {
  return window.matchMedia("(min-width: 901px)").matches;
}

function Links({
  links,
  onNavigate,
}: {
  links: LinkItem[];
  onNavigate?: () => void;
}) {
  return (
    <div className="nav-links stacked">
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

/** Burger always visible. Desktop: push sidebar (default open). Mobile: overlay. */
export function AppLayout({ children }: { children: ReactNode }) {
  const [open, setOpen] = useState(() =>
    typeof window !== "undefined" ? isDesktop() : true,
  );
  const location = useLocation();

  useEffect(() => {
    const mq = window.matchMedia("(min-width: 901px)");
    const onChange = () => setOpen(mq.matches);
    mq.addEventListener("change", onChange);
    return () => mq.removeEventListener("change", onChange);
  }, []);

  useEffect(() => {
    if (!isDesktop()) setOpen(false);
  }, [location.pathname]);

  useEffect(() => {
    if (open && !isDesktop()) {
      document.body.style.overflow = "hidden";
    } else {
      document.body.style.overflow = "";
    }
    return () => {
      document.body.style.overflow = "";
    };
  }, [open]);

  const closeIfMobile = () => {
    if (!isDesktop()) setOpen(false);
  };

  return (
    <div className={open ? "app-shell menu-open" : "app-shell"}>
      <aside className="app-sidebar" aria-hidden={!open} aria-label="Site menu">
        <div className="app-sidebar-inner">
          {sections.map((s) => (
            <div key={s.label} className="nav-drawer-section">
              <div className="nav-group-label">{s.label}</div>
              <Links links={s.links} onNavigate={closeIfMobile} />
            </div>
          ))}
        </div>
      </aside>

      <div className="app-main">
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
        </header>
        {children}
      </div>

      <button
        type="button"
        className={open ? "nav-scrim on" : "nav-scrim"}
        aria-label="Dismiss menu"
        tabIndex={open ? 0 : -1}
        onClick={() => setOpen(false)}
      />
    </div>
  );
}
