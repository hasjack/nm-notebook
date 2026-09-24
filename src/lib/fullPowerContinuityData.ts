// Generated from analysis/full-power-door-continuity/power-continuity.json
// and analysis/whole-odd-block-shapes/swallow-shape.json (normal form).
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
  /** Exact normal-form classification of the 1,336 whole-odd-part preservations (census through 10M). */
  swallowShapes: {
    n: 1_336,
    /** Within the repeated-A cohort of 1,336: B = 1 always; exactly one preserving r per transition. */
    BAlwaysOne: true,
    onePreservingRPerTransition: true,
    /** Preserving door shares by m₀(r) = 2ᵏ A. */
    doorShares: [
      { label: "2A", k: 1, count: 678, pct: 50.75 },
      { label: "4A", k: 2, count: 325, pct: 24.33 },
      { label: "8A", k: 3, count: 178, pct: 13.32 },
      { label: "16A", k: 4, count: 67, pct: 5.01 },
      { label: "32A…1024A", kMin: 5, kMax: 10, count: 88, pct: 6.59 },
    ],
    normalForm: {
      matching: 1_336,
      /** Observed for every case in this cohort (k, v ≥ 1; r prime ≡ 2 mod 3). */
      form: {
        dOld: "2^{v+k} A",
        dNew: "2^v (2^k A + 1)",
        r: "2^k A + 1",
        m0r: "2^k A",
        gap: "2^v",
      },
      doorGaps: [
        { gap: 2, count: 753 },
        { gap: 4, count: 360 },
        { gap: 8, count: 173 },
        { gap: 16, count: 42 },
        { gap: 32, count: 8 },
      ],
      prototypes: [
        {
          A: 125,
          k: 1,
          v: 1,
          dOld: 500,
          dNew: 502,
          r: 251,
          m0r: 250,
          note: "d_old = 4A, d_new = 2(2A+1), m₀(251) = 2A",
        },
        {
          A: 175,
          k: 2,
          v: 2,
          dOld: 2800,
          dNew: 2804,
          r: 701,
          m0r: 700,
          note: "d_old = 16A, d_new = 4(4A+1), m₀(701) = 4A",
        },
      ],
      note: "Construction ⇒ swallow is door arithmetic. Repeated-A cohort (1,336): all B=1 through 10⁷. Broad form (no repeated-factor hyp) is false — see counterexample.",
    },
    /** Broad (no repeated factor in A) conjecture is false. Only mess among 8,924 nonempty whole-block preservations through 10⁷. */
    broadCounterexample: {
      p: 1_310_719,
      next: 1_310_723,
      oldDoor: "2¹⁸ · 5",
      newDoor: "2 · 7 · 251 · 373",
      A: 5,
      r: 251,
      m0r: "250 = 2 · 5³ = 2A · 25",
      B: 25,
      nonemptyWholePreservations: 8_924,
      messyAmongThem: 1,
      note: "Messy = extra multiplicity of primes already in A, not a new odd species.",
    },
  },
} as const;
