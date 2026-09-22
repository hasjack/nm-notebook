import { useEffect, useMemo, useState, type ReactNode } from "react";
import { NavLink, useLocation } from "react-router-dom";
import { Meta } from "./Meta";
import { REPO_NAME, REPO_URL } from "../lib/meta";

type LinkItem = { to: string; label: string; end?: boolean; icon?: "pdf" };

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
    blurb: "Door → basins → islands → corridor → microscope → certificates → spectrum → hire rate → notes.",
    links: [
      { to: "/hire", label: "Introduction" },
      { to: "/basins", label: "Basins" },
      { to: "/islands", label: "Islands" },
      { to: "/corridor", label: "Corridor" },
      { to: "/microscope", label: "Microscope" },
      { to: "/certificates", label: "Certificates" },
      { to: "/hire-spectrum", label: "Spectrum" },
      { to: "/hire-lab", label: "Hire rate" },
    ],
    subs: [
      {
        id: "hire-notes",
        label: "Notes",
        links: [
          {
            to: "/notes/hire-graph",
            label: "The hire graph of the 3-free door",
            icon: "pdf",
          },
          {
            to: "/notes/when-gold-disconnects",
            label: "When gold disconnects",
            icon: "pdf",
          },
        ],
      },
    ],
  },
  {
    id: "alphabet",
    label: "Alphabet",
    blurb: "Number line in e, i, and π.",
    links: [
      { to: "/alphabet", label: "Alphabet" },
      { to: "/solve", label: "Solve" },
      { to: "/catalogue", label: "Catalogue" },
      { to: "/alphabet/notes", label: "Benefits" },
    ],
  },
  {
    id: "toys",
    label: "Toys",
    blurb: "Waves, (σ, p) Bell, switching atlas.",
    links: [
      { to: "/physics", label: "Physics" },
      { to: "/toys/bell", label: "Bell" },
      { to: "/toys/atlas", label: "Atlas" },
    ],
  },
  {
    id: "notes",
    label: "Notes",
    links: [
      {
        to: "/notes/hire-graph",
        label: "The hire graph of the 3-free door",
        icon: "pdf",
      },
      {
        to: "/notes/when-gold-disconnects",
        label: "When gold disconnects",
        icon: "pdf",
      },
      {
        to: "/notes/zeta-doors",
        label: "Prime neighbours of zeta denominators",
        icon: "pdf",
      },
    ],
  },
  {
    id: "lab",
    label: "Lab",
    blurb: "More probes — field, analysis, primes, spectra.",
    links: [
      { to: "/zeta-doors", label: "Zeta doors" },
      { to: "/rank100", label: "Rank 100" },
      { to: "/magnitude", label: "Magnitude" },
      { to: "/beacons", label: "Beacons" },
      { to: "/rotation", label: "Rotation" },
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

const HIRE_OPEN = new Set(["hire", "hire-notes"]);

/** Exclusive accordion keys for the current route. Default: Hire with Notes open. */
function accordionFor(pathname: string): Set<string> {
  for (const g of tree) {
    if (g.links && pathInLinks(pathname, g.links)) {
      return g.id === "hire" ? new Set(HIRE_OPEN) : new Set([g.id]);
    }
    for (const s of g.subs ?? []) {
      if (pathInLinks(pathname, s.links)) return new Set([g.id, s.id]);
    }
  }
  return new Set(HIRE_OPEN);
}

function GithubIcon() {
  return (
    <svg
      className="nav-github-icon"
      viewBox="0 0 16 16"
      width="14"
      height="14"
      aria-hidden="true"
      focusable="false"
    >
      <path
        fill="currentColor"
        d="M8 0C3.58 0 0 3.58 0 8c0 3.54 2.29 6.53 5.47 7.59.4.07.55-.17.55-.38 0-.19-.01-.82-.01-1.49-2.01.37-2.53-.49-2.69-.94-.09-.23-.48-.94-.82-1.13-.28-.15-.68-.52-.01-.53.63-.01 1.08.58 1.23.82.72 1.21 1.87.87 2.33.66.07-.52.28-.87.51-1.07-1.78-.2-3.64-.89-3.64-3.95 0-.87.31-1.59.82-2.15-.08-.2-.36-1.02.08-2.12 0 0 .67-.21 2.2.82.64-.18 1.32-.27 2-.27s1.36.09 2 .27c1.53-1.04 2.2-.82 2.2-.82.44 1.1.16 1.92.08 2.12.51.56.82 1.27.82 2.15 0 3.07-1.87 3.75-3.65 3.95.29.25.54.73.54 1.48 0 1.07-.01 1.93-.01 2.2 0 .21.15.46.55.38A8.01 8.01 0 0 0 16 8c0-4.42-3.58-8-8-8"
      />
    </svg>
  );
}

function PdfIcon() {
  return (
    <svg
      className="nav-pdf-icon"
      viewBox="0 0 12 14"
      width="12"
      height="14"
      aria-hidden="true"
      focusable="false"
    >
      <path
        fill="currentColor"
        d="M2.2.6h5.2L11 4.2v8.2c0 .6-.5 1-.9 1H2.2c-.5 0-1-.4-1-1V1.6c0-.6.5-1 1-1zm5 1.1v2.4h2.4L7.2 1.7z"
      />
    </svg>
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
          {l.icon === "pdf" ? <PdfIcon /> : null}
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
 * Shelves are exclusive: one top section (and at most one nested sub) open.
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
    window.scrollTo(0, 0);
    document.querySelector(".app-main")?.scrollTo(0, 0);
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
      if (id === "hire") return new Set(HIRE_OPEN);
      return new Set([id]);
    });
  };

  const toggleSub = (parentId: string, id: string) => {
    setExpanded((prev) => {
      const next = new Set<string>([parentId]);
      if (!prev.has(id)) next.add(id);
      return next;
    });
  };

  return (
    <div className={open ? "app-shell menu-open" : "app-shell"}>
      <Meta />
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
            <p className="nav-about-blurb">Independent researcher, UK.</p>
            <a
              className="nav-about-repo"
              href={REPO_URL}
              target="_blank"
              rel="noreferrer"
            >
              <GithubIcon />
              {REPO_NAME}
            </a>
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
                            onClick={() => toggleSub(g.id, s.id)}
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
