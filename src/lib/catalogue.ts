/**
 * Catalogue: classical quantities rewritten in the alphabet {e, i, π}.
 * Grades:
 *   clean      — the letters earn their place (identity / natural proof room)
 *   calligraphy — same content, renamed (often π ↔ −i Log(−1))
 *   refuses    — no simple rewrite known in this alphabet
 */

export type Grade = "clean" | "calligraphy" | "refuses";

export type CatalogueEntry = {
  id: string;
  title: string;
  classical: string;
  rewrite: string;
  alphabet: Array<"e" | "i" | "π">;
  grade: Grade;
  why: string;
  /** One beat for a thought-provoking video */
  videoBeat: string;
};

export const CATALOGUE: CatalogueEntry[] = [
  {
    id: "euler-identity",
    title: "Euler’s identity",
    classical: "e^(iπ) + 1 = 0",
    rewrite: "already in {e, i, π}",
    alphabet: ["e", "i", "π"],
    grade: "clean",
    why: "The home base of the alphabet. Five fundamental symbols in one line; your Walk page is this with the base free.",
    videoBeat: "Start here: the only equation that already speaks fluent e, i, π.",
  },
  {
    id: "euler-formula",
    title: "Euler’s formula",
    classical: "cos θ + i sin θ",
    rewrite: "e^(iθ)",
    alphabet: ["e", "i"],
    grade: "clean",
    why: "Trigonometry is the real/imaginary parts of a complex exponential. π enters when θ is a half-turn.",
    videoBeat: "Circles aren’t drawn — they’re exponentials of i.",
  },
  {
    id: "log-minus-one",
    title: "π from a logarithm",
    classical: "π",
    rewrite: "π = −i Log(−1)  (principal branch)",
    alphabet: ["e", "i"],
    grade: "calligraphy",
    why: "True on the principal branch, but Log(−1) = iπ, so you smuggled π into the log. Pretty calligraphy, not a new definition unless you take Log as primitive.",
    videoBeat: "You can hide π inside log(−1) — but did you remove it, or just rename it?",
  },
  {
    id: "circle-area",
    title: "Area of a circle",
    classical: "A = π r²",
    rewrite: "A = −i Log(−1) · r²",
    alphabet: ["e", "i"],
    grade: "calligraphy",
    why: "Same as π-from-log. Geometry unchanged; alphabet swapped. Good video contrast against clean entries.",
    videoBeat: "Same pizza, different menu font: area in i and log, still secretly π.",
  },
  {
    id: "ii",
    title: "i to the i",
    classical: "i^i",
    rewrite: "i^i = e^(−π/2)  (principal value)",
    alphabet: ["e", "π"],
    grade: "clean",
    why: "i = e^(iπ/2), so i^i = e^(i·iπ/2) = e^(−π/2). A real number built from i — the alphabet flexes.",
    videoBeat: "Raise i to itself and π and e fall out: a real answer from imaginary bases.",
  },
  {
    id: "basel-sum",
    title: "Basel — Basel (1+1/4+1/9+…)",
    classical: "1 + 1/4 + 1/9 + … = π²/6",
    rewrite: "1 + 1/4 + 1/9 + … = π²/6",
    alphabet: ["π"],
    grade: "clean",
    why: "Even reciprocal-power sums like this are π-native. Proofs live in the Fourier / sin-product / complex-analysis room where i is furniture. This is what ‘clean’ looks like for constants.",
    videoBeat: "Infinite sum of squares → π²/6. Even reciprocal-power sums already live on your island.",
  },
  {
    id: "gaussian",
    title: "Gaussian integral",
    classical: "∫_{-∞}^{∞} e^(−x²) dx",
    rewrite: "√π",
    alphabet: ["e", "π"],
    grade: "clean",
    why: "e defines the integrand; π appears in the area. No i required, but the polar-coordinate proof is one twist from the complex plane.",
    videoBeat: "The bell curve’s total mass is √π — e builds the shape, π measures it.",
  },
  {
    id: "stirling",
    title: "Stirling’s approximation",
    classical: "n!",
    rewrite: "n! ~ √(2πn) (n/e)^n",
    alphabet: ["e", "π"],
    grade: "clean",
    why: "Factorials grow with e in the base and π under a square root. Another ‘both letters earn their keep’ classic.",
    videoBeat: "Counting permutations secretly needs e and π.",
  },
  {
    id: "sinc-product",
    title: "Sine infinite product",
    classical: "sin(x)/x",
    rewrite: "sin(x) = x ∏ (1 − x²/(n²π²))",
    alphabet: ["π"],
    grade: "clean",
    why: "Euler’s product for sine is the engine behind Basel. Roots at nπ; the alphabet is geometric.",
    videoBeat: "Sine is a polynomial with roots at every multiple of π — infinity included.",
  },
  {
    id: "wave-phasor",
    title: "Tone / phasor",
    classical: "cos(ωt) + i sin(ωt)",
    rewrite: "e^(i · ω · π · t)  (ω in π-units)",
    alphabet: ["e", "i", "π"],
    grade: "clean",
    why: "Every harmonic oscillator already speaks the walk’s alphabet. Period is the Return character.",
    videoBeat: "Cut from the spiral ribbon to the rotating arrow — same e^(iθ).",
  },
  {
    id: "beat-two-tones",
    title: "Beat — two tones",
    classical: "cos ω₁t + cos ω₂t",
    rewrite: "Re(e^(iω₁πt) + e^(iω₂πt))",
    alphabet: ["e", "i", "π"],
    grade: "clean",
    why: "Interference without leaving the alphabet. Envelope tracks |ω₁−ω₂|.",
    videoBeat: "Two clocks, one sum — the beat you can hear in the letters.",
  },
  {
    id: "damped-envelope",
    title: "Damped envelope",
    classical: "e^(−γt) cos(ωt)",
    rewrite: "Re( e^(−γt) e^(i ω π t) )",
    alphabet: ["e", "i", "π"],
    grade: "clean",
    why: "Time cousin of Magnitude’s base^σ — one dial pinches amplitude.",
    videoBeat: "Decay is still e — just not the walk’s base.",
  },
  {
    id: "alphabet-spiral",
    title: "Alphabet spiral",
    classical: "integers on a spiral",
    rewrite: "z = n · e^(i · n · σ · π)",
    alphabet: ["e", "i", "π"],
    grade: "clean",
    why: "Arms from the alphabet wrap; primes choose seats. Native door for primes on the island — not the sieve-braid sketch.",
    videoBeat: "Same curve language as the walk; diamonds where arithmetic leaves a gap.",
  },
  {
    id: "prime-braids",
    title: "Prime braids",
    classical: "multiples on a spiral · intersections = composites",
    rewrite: "2 plays nice; 3 jams because it is prime",
    alphabet: ["e", "i", "π"],
    grade: "clean",
    why: "NM sieve: each prime adds an irreducible braid. Lonely marks survive. Ties to the knife — only 2 cuts cleanly before the first jam.",
    videoBeat: "Turn on 2 — calm. Add 3 — orange crossings. That is prime as a new spiral.",
  },
  {
    id: "natures-knife",
    title: "2 is nature’s only knife",
    classical: "even / odd · order 2 · half-turn",
    rewrite: "the privileged cut is twofold",
    alphabet: ["e", "i", "π"],
    grade: "clean",
    why: "NM principle: Basel exits at order 2; the peg flips on odd integers; return is a full turn of 2 half-turns. Higher cuts stay in costume.",
    videoBeat: "Nature’s knife has one blade — two.",
  },
  {
    id: "return-0-1",
    title: "Return — 0 and full turn",
    classical: "e^(i 2π) = 1 = e^0",
    rewrite: "back to where it started",
    alphabet: ["e", "i", "π"],
    grade: "clean",
    why: "In Natural Mathematics, 0 and the full turn are one character: return. Not the mute (base→1) and not the wind (base→0).",
    videoBeat: "Zero and one as home — the circle’s handshake with itself.",
  },
  {
    id: "half-turn",
    title: "Minus one as a half-turn",
    classical: "−1",
    rewrite: "−1 = e^(iπ)",
    alphabet: ["e", "i", "π"],
    grade: "clean",
    why: "Your Lock pages hold this fixed while base moves. −1 is not a slogan; it’s a landing on the unit circle.",
    videoBeat: "−1 is what you get when you rotate by π using e and i.",
  },
  {
    id: "cube-sum",
    title: "The cube reciprocal sum",
    classical: "1 + 1/8 + 1/27 + …",
    rewrite: "no simple closed form in {e, i, π} known",
    alphabet: [],
    grade: "refuses",
    why: "Irrational (Apéry), but not known to be a tidy π-package like Basel (1+1/4+1/9+…). The shoreline of the island: odd reciprocal-power sums mostly refuse the alphabet.",
    videoBeat: "Same shape of sum as 1+1/4+… — but π won’t finish the sentence.",
  },
  {
    id: "euler-mascheroni",
    title: "Euler–Mascheroni γ",
    classical: "γ = lim (1 + 1/2 + … + 1/n − ln n)",
    rewrite: "unknown whether γ is even irrational; no clean {e,i,π} form",
    alphabet: ["e"],
    grade: "refuses",
    why: "ln brings e’s inverse; the constant itself sits outside the tidy club. Useful as a ‘still wild’ marker.",
    videoBeat: "Born from e’s logarithm — and still won’t tell us if it’s rational.",
  },
  {
    id: "two-pi-i",
    title: "Residues — 2πi",
    classical: "∮ dz/z",
    rewrite: "2πi",
    alphabet: ["i", "π"],
    grade: "clean",
    why: "One loop around the origin in the complex plane. Contour integration’s unit of currency.",
    videoBeat: "Walk once around 0 and the universe hands you 2πi.",
  },
];

export const GRADE_LABEL: Record<Grade, string> = {
  clean: "Clean",
  calligraphy: "Calligraphy",
  refuses: "Refuses",
};

export const GRADE_BLURB: Record<Grade, string> = {
  clean:
    "The letters earn their place — the identity or its natural proof room already lives here.",
  calligraphy:
    "Same mathematics, renamed. Often π dressed as −i Log(−1). Pretty; not a new fact.",
  refuses:
    "No simple rewrite in {e, i, π} is known. The edge of the island.",
};
