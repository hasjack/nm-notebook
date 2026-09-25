export const SITE_URL = "https://halfasecond.com";
export const SITE_NAME = "NM notebook";
export const SITE_TITLE = "The hire graph of the 3-free door";
export const SITE_DESCRIPTION =
  "Jack Pickett’s notebook: the hire graph of the 3-free door, Lean, notes, and lab.";
export const SITE_IMAGE = `${SITE_URL}/figures/hire/H_hire_tree.png`;
export const REPO_URL = "https://github.com/hasjack/nm-notebook";
export const REPO_NAME = "nm-notebook";

type PageMeta = { title: string; description?: string };

const pages: Record<string, PageMeta> = {
  "/": { title: SITE_TITLE, description: SITE_DESCRIPTION },
  "/hire": {
    title: "Introduction",
    description: "The 3-free door, hire set, and gold graph.",
  },
  "/basins": { title: "Basins" },
  "/islands": { title: "Islands" },
  "/corridor": { title: "Corridor" },
  "/microscope": { title: "Microscope" },
  "/certificates": { title: "Certificates" },
  "/hire-spectrum": { title: "Spectrum" },
  "/hire-lab": { title: "Hire rate" },
  "/notes": {
    title: "Notes",
    description: "PDFs of the hire papers and the zeta-doors note.",
  },
  "/notes/hire-graph": {
    title: "The hire graph of the 3-free door",
    description: "Paper 1: doors, gold, the Dirichlet bridge into comp(5).",
  },
  "/notes/when-gold-disconnects": {
    title: "When gold disconnects",
    description:
      "Gold is disconnected for infinitely many windows iff infinitely many Mersenne or Fermat primes.",
  },
  "/notes/zeta-doors": {
    title: "Prime neighbours of zeta denominators",
    description:
      "Zeta-door candidates from Bernoulli denominators at k ≡ 2 (mod 12).",
  },
  "/zeta-doors": {
    title: "Zeta doors",
    description: "Lab hunt: 3-free neighbours of zeta denominators.",
  },
  "/psi-stair": {
    title: "ψ stair",
    description: "Chebyshev ψ stair vs truncated explicit-formula waves from critical zeros (critical line assumed).",
  },
  "/rank100": { title: "Rank 100 floor" },
  "/gaussian-doors": {
    title: "Gaussian doors",
    description: "3-free doors as a route from two squares to x²+3y².",
  },
  "/alphabet": { title: "Alphabet" },
  "/alphabet/notes": { title: "Alphabet benefits" },
  "/solve": { title: "Solve" },
  "/catalogue": { title: "Catalogue" },
  "/physics": { title: "Physics" },
  "/toys/bell": { title: "Bell toy" },
  "/toys/atlas": { title: "Atlas" },
  "/count": { title: "Count" },
  "/alphabet-spiral": { title: "Alphabet spiral" },
  "/magnitude": { title: "Magnitude" },
  "/beacons": { title: "Beacons" },
  "/rotation": { title: "Rotation" },
  "/primes": { title: "Primes" },
  "/super-primes": { title: "Super-primes" },
  "/unclaimed": { title: "Unclaimed" },
  "/beacon-super": { title: "Beacon × S" },
  "/suspect-bench": { title: "Suspect" },
  "/missed": { title: "Missed" },
  "/spectrum": { title: "Spectrum" },
  "/pm1": { title: "±1" },
  "/signed-doors": { title: "±Doors" },
  "/analysis-1": { title: "Analysis 1" },
  "/analysis-2": { title: "Analysis 2" },
  "/analysis-3": { title: "Analysis 3" },
  "/analysis-4": { title: "Analysis 4" },
  "/analysis-5": { title: "Analysis 5" },
};

export function metaFor(pathname: string): { title: string; description: string; url: string } {
  const page = pages[pathname] ?? { title: SITE_NAME };
  const title =
    pathname === "/" ? page.title : `${page.title} · ${SITE_NAME}`;
  return {
    title,
    description: page.description ?? SITE_DESCRIPTION,
    url: `${SITE_URL}${pathname === "/" ? "/" : pathname}`,
  };
}
