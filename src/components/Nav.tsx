import { useEffect, useMemo, useState, type ReactNode } from "react";
import { NavLink, useLocation } from "react-router-dom";

type LinkItem = { to: string; label: string; end?: boolean };

type NavSub = { id: string; label: string; links: LinkItem[] };

type NavGroup = {
  id: string;
  label: string;
  blurb?: string;
  links?: LinkItem[];
  subs?: NavSub[];
};

const tree: NavGroup[] = [
  {
    id: "hire",
    label: "Hire",
    blurb: "Door, basins, islands — then the notes.",
    links: [
      { to: "/hire", label: "Introduction" },
      { to: "/basins", label: "Basins" },
      { to: "/islands", label: "Islands" },
      { to: "/paper", label: "Paper" },
      { to: "/when-gold-disconnects", label: "When gold disconnects" },
    ],
  },
  {
    id: "issue",
    label: "Issue",
    blurb: "Main-line trail — commit hashes to land here.",
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
    blurb: "Probe pages — one shelf at a time.",
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

/** Exclusive accordion keys for the current route. Default shelf: Hire. */
function accordionFor(pathname: string): Set<string> {
  for (const g of tree) {
    if (g.links && pathInLinks(pathname, g.links)) return new Set([g.id]);
    for (const s of g.subs ?? []) {
      if (pathInLinks(pathname, s.links)) return new Set([g.id, s.id]);
    }
  }
  return new Set(["hire"]);
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
 * Shelves are exclusive: one top section (and at most one Lab sub) open.
 */
export function AppLayout({ children }: { children: ReactNode }) {
  const [open, setOpen] = useState(() =>
    typeof window !== "undefined" ? isDesktop() : true,
  );
  const location = useLocation();

  const routeAccordion = useMemo(
    () => accordionFor(location.pathname),
    [location.pathname],
  );

  const [expanded, setExpanded] = useState<Set<string>>(() => routeAccordion);

  useEffect(() => {
    setExpanded(routeAccordion);
  }, [routeAccordion]);

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

  const toggleTop = (id: string) => {
    setExpanded((prev) => {
      if (prev.has(id)) return new Set(); // allow all closed
      return new Set([id]);
    });
  };

  const toggleLabSub = (id: string) => {
    setExpanded((prev) => {
      const next = new Set<string>(["lab"]);
      if (!prev.has(id)) next.add(id);
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
                  onClick={() => toggleTop(g.id)}
                >
                  <span className="nav-drill-label">{g.label}</span>
                  <span className="nav-drill-chevron" aria-hidden="true" />
                </button>
                {isOpen ? (
                  <div className="nav-drill-body">
                    {g.blurb ? (
                      <p className="nav-section-blurb">{g.blurb}</p>
                    ) : null}
                    {g.links ? (
                      <Links links={g.links} onNavigate={closeIfMobile} />
                    ) : null}
                    {g.subs?.map((s) => {
                      const subOpen = expanded.has(s.id);
                      return (
                        <div key={s.id} className="nav-sub">
                          <button
                            type="button"
                            className={
                              subOpen ? "nav-drill sub on" : "nav-drill sub"
                            }
                            aria-expanded={subOpen}
                            onClick={() => toggleLabSub(s.id)}
                          >
                            <span className="nav-drill-label">{s.label}</span>
                            <span
                              className="nav-drill-chevron"
                              aria-hidden="true"
                            />
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
