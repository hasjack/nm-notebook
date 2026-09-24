// Generated from analysis/full-power-door-continuity/power-continuity.json.
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
} as const;
