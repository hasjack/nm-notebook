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
    id: "zeta2",
    title: "Basel — Basel (1+1/4+1/9+…)",
    classical: "1 + 1/4 + 1/9 + … = π²/6",
    rewrite: "1 + 1/4 + 1/9 + … = π²/6",
    alphabet: ["π"],
    grade: "clean",
    why: "Even reciprocal-power sums like this are π-native. Proofs live in the Fourier / sin-product / complex-analysis room where i is furniture. This is what ‘clean’ looks like for constants.",
    videoBeat: "Infinite sum of squares → π²/6. The even zetas already live on your island.",
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
    id: "zeta3",
    title: "The cube reciprocal sum",
    classical: "1 + 1/8 + 1/27 + …",
    rewrite: "no simple closed form in {e, i, π} known",
    alphabet: [],
    grade: "refuses",
    why: "Irrational (Apéry), but not known to be a tidy π-package like Basel (1+1/4+1/9+…). The shoreline of the island: odd zetas mostly refuse the alphabet.",
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
