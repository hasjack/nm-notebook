// Generated from analysis/full-power-door-continuity/power-continuity.json
// and swallow-shapes.json.
export const fullPowerContinuityData = {
  limit: 10_000_000,
  /** Consecutive pairs with disjoint odd support and at least one departing odd factor with exponent ≥2. */
  eligible: 58_666,
  rates: [
    {
      label: "Repeated-factor prime reconnects",
      count: 18_285,
      pct: 31.17,
    },
    {
      label: "Full original power preserved (≥ old exponent)",
      count: 2_927,
      pct: 4.99,
    },
    {
      label: "Entire previous odd part in one arriving door",
      count: 1_336,
      pct: 2.28,
    },
  ],
  byExponent: [
    { exp: 2, opportunities: 52_298, linked: 15_336, full: 2_732 },
    { exp: 3, opportunities: 7_062, linked: 2_571, full: 229 },
    { exp: 4, opportunities: 1_181, linked: 458, full: 21 },
    { exp: 5, opportunities: 222, linked: 78, full: 8 },
    { exp: 6, opportunities: 43, linked: 15, full: 1 },
    { exp: 7, opportunities: 9, linked: 3, full: 0 },
    { exp: 8, opportunities: 1, linked: 0, full: 0 },
  ],
  matched: {
    minControls: 1,
    observedPairs: 35_209,
    coveragePct: 60.02,
    fullPowerObservedPct: 3.39,
    fullPowerControlPct: 3.46,
    note: "Gaps 2 and 4 have no nonconsecutive controls — both headline examples sit outside this comparison.",
  },
  examples: [
    {
      p: 499,
      next: 503,
      oldDoor: 500,
      newDoor: 502,
      oldFactors: "4 · 5³",
      newFactors: "2 · 251",
      path: "m₀(251) = 250 = 2 · 5³",
      note: "Full power and whole odd part. Gap 2 — outside matched controls.",
    },
    {
      p: 2801,
      next: 2803,
      oldDoor: 2800,
      newDoor: 2804,
      oldFactors: "2⁴ · 5² · 7",
      newFactors: "2² · 701",
      path: "m₀(701) = 700 = 2² · 5² · 7",
      note: "Both 5² and 7 reappear in one arriving door. Gap 2 — outside matched controls.",
    },
  ],
  /** Shape of m₀(r) relative to old odd block A, among the 1,336 whole-odd-part preservations. */
  swallowShapes: {
    n: 1_336,
    clean: 1_336,
    messier: 0,
    byK: [
      { k: 1, count: 678, pct: 50.75 },
      { k: 2, count: 325, pct: 24.33 },
      { k: 3, count: 178, pct: 13.32 },
      { k: 4, count: 67, pct: 5.01 },
      { k: 5, count: 39, pct: 2.92 },
      { k: 6, count: 29, pct: 2.17 },
      { k: 7, count: 7, pct: 0.52 },
      { k: 8, count: 7, pct: 0.52 },
      { k: 9, count: 4, pct: 0.3 },
      { k: 10, count: 2, pct: 0.15 },
    ],
    examples: [
      {
        p: 499,
        next: 503,
        k: 1,
        A: 125,
        path: "m₀(251) = 250 = 2¹ · 125",
      },
      {
        p: 2801,
        next: 2803,
        k: 2,
        A: 175,
        path: "m₀(701) = 700 = 2² · 175",
      },
      {
        p: 23201,
        next: 23203,
        k: 3,
        A: 725,
        path: "m₀(5801) = 5800 = 2³ · 725",
      },
      {
        p: 51199,
        next: 51203,
        k: 10,
        A: 25,
        path: "m₀(25601) = 25600 = 2¹⁰ · 25",
      },
    ],
    note: "Every one of the 1,336 is clean m₀(r) = 2ᵏ · A (messier bucket empty through 10M). Clean 2ᵏ A is door arithmetic: r is a χ₃-neighbour of 2ᵏ A — not a new adjacency law.",
  },
} as const;
