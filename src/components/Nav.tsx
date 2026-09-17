import { useEffect, useMemo, useState, type ReactNode } from "react";
import { NavLink, useLocation } from "react-router-dom";

type LinkItem = { to: string; label: string; end?: boolean };

type NavGroup = {
  id: string;
  label: string;
  blurb?: string;
  links?: LinkItem[];
  /** Nested drill-downs inside a top section (used for Lab). */
  subs?: { id: string; label: string; links: LinkItem[] }[];
};

const tree: NavGroup[] = [
  {
    id: "issue",
    label: "Issue",
    blurb: "Lead article and hire dials.",
    links: [
      { to: "/", label: "Lead", end: true },
      { to: "/hire", label: "Hire" },
    ],
  },
  {
    id: "alphabet",
    label: "Alphabet",
    blurb: "Number line in e, i, and π.",
    links: [
      { to: "/walk", label: "Walk" },
      { to: "/lock-i", label: "Lock i" },
      { to: "/lock-pi", label: "Lock π" },
      { to: "/basel", label: "Basel" },
      { to: "/free", label: "Free" },
      { to: "/solve", label: "Solve" },
      { to: "/catalogue", label: "Catalogue" },
      { to: "/notes", label: "Notes" },
    ],
  },
  {
    id: "lab",
    label: "Lab",
    blurb: "Probe pages — open a shelf.",
    subs: [
      {
        id: "lab-field",
        label: "Field",
        links: [
          { to: "/magnitude", label: "Magnitude" },
          { to: "/beacons", label: "Beacons" },
          { to: "/rotation", label: "Rotation" },
          { to: "/physics", label: "Physics" },
        ],
      },
      {
        id: "lab-analysis",
        label: "Analysis",
        links: [
          { to: "/analysis-1", label: "A1" },
          { to: "/analysis-2", label: "A2" },
          { to: "/analysis-3", label: "A3" },
          { to: "/analysis-4", label: "A4" },
          { to: "/analysis-5", label: "A5" },
        ],
      },
      {
        id: "lab-primes",
        label: "Primes",
        links: [
          { to: "/primes", label: "Primes" },
          { to: "/super-primes", label: "Super" },
          { to: "/unclaimed", label: "Unclaimed" },
          { to: "/beacon-super", label: "Beacon×S" },
          { to: "/suspect-bench", label: "Suspect" },
          { to: "/missed", label: "Missed" },
        ],
      },
      {
        id: "lab-spectra",
        label: "Spectra & doors",
        links: [
          { to: "/spectrum", label: "Spectrum" },
          { to: "/pm1", label: "±1" },
          { to: "/signed-doors", label: "±Doors" },
          { to: "/alphabet-spiral", label: "α-spiral" },
          { to: "/count", label: "Count" },
        ],
      },
    ],
  },
];

function isDesktop(): boolean {
  return window.matchMedia("(min-width: 901px)").matches;
}

function pathInLinks(pathname: string, links: LinkItem[]): boolean {
  return links.some((l) =>
    l.end ? pathname === l.to : pathname === l.to || pathname.startsWith(l.to + "/"),
  );
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

function Brand({ onNavigate }: { onNavigate?: () => void }) {
  return (
    <NavLink to="/" end className="nav-brand" onClick={onNavigate}>
      NM notebook
    </NavLink>
  );
}

/**
 * Burger/close stay fixed in one spot.
 * Logo lives in the menu; a docked twin covers the closed state so mobile
 * transform on the drawer cannot drag the wordmark off-screen.
 */
export function AppLayout({ children }: { children: ReactNode }) {
  const [open, setOpen] = useState(() =>
    typeof window !== "undefined" ? isDesktop() : true,
  );
  const location = useLocation();

  const activeIds = useMemo(() => {
    const ids = new Set<string>();
    for (const g of tree) {
      if (g.links && pathInLinks(location.pathname, g.links)) ids.add(g.id);
      for (const s of g.subs ?? []) {
        if (pathInLinks(location.pathname, s.links)) {
          ids.add(g.id);
          ids.add(s.id);
        }
      }
    }
    if (ids.size === 0) ids.add("issue");
    return ids;
  }, [location.pathname]);

  const [expanded, setExpanded] = useState<Set<string>>(() => new Set(activeIds));

  useEffect(() => {
    setExpanded((prev) => {
      const next = new Set(prev);
      for (const id of activeIds) next.add(id);
      return next;
    });
  }, [activeIds]);

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

  const toggle = (id: string) => {
    setExpanded((prev) => {
      const next = new Set(prev);
      if (next.has(id)) next.delete(id);
      else next.add(id);
      return next;
    });
  };

  return (
    <div className={open ? "app-shell menu-open" : "app-shell"}>
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

      <div
        className={open ? "nav-brand-dock hidden" : "nav-brand-dock"}
        aria-hidden={open}
      >
        <Brand />
      </div>

      <aside className="app-sidebar" aria-label="Site menu">
        <div className="app-sidebar-brand">
          <Brand onNavigate={closeIfMobile} />
        </div>
        <div className="app-sidebar-inner" aria-hidden={!open}>
          <div className="nav-about">
            <p className="nav-about-name">
              Jack Pickett{" "}
              <a
                href="https://github.com/hasjack"
                target="_blank"
                rel="noreferrer"
              >
                @hasjack
              </a>
            </p>
            <p className="nav-about-blurb">
              Public notebook for Natural Mathematics — hire graph, alphabet on e / i / π,
              and Lean lemmas under <code>lean/</code>.
            </p>
          </div>

          {tree.map((g) => {
            const isOpen = expanded.has(g.id);
            return (
              <div key={g.id} className="nav-drawer-section">
                <button
                  type="button"
                  className={isOpen ? "nav-drill on" : "nav-drill"}
                  aria-expanded={isOpen}
                  onClick={() => toggle(g.id)}
                >
                  <span className="nav-drill-label">{g.label}</span>
                  <span className="nav-drill-chevron" aria-hidden="true" />
                </button>
                {isOpen ? (
                  <div className="nav-drill-body">
                    {g.blurb ? <p className="nav-section-blurb">{g.blurb}</p> : null}
                    {g.links ? (
                      <Links links={g.links} onNavigate={closeIfMobile} />
                    ) : null}
                    {g.subs?.map((s) => {
                      const subOpen = expanded.has(s.id);
                      return (
                        <div key={s.id} className="nav-sub">
                          <button
                            type="button"
                            className={subOpen ? "nav-drill sub on" : "nav-drill sub"}
                            aria-expanded={subOpen}
                            onClick={() => toggle(s.id)}
                          >
                            <span className="nav-drill-label">{s.label}</span>
                            <span className="nav-drill-chevron" aria-hidden="true" />
                          </button>
                          {subOpen ? (
                            <Links links={s.links} onNavigate={closeIfMobile} />
                          ) : null}
                        </div>
                      );
                    })}
                  </div>
                ) : null}
              </div>
            );
          })}
        </div>
      </aside>

      <div className="app-main">
        <div className="nav-bar-spacer" aria-hidden="true" />
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
