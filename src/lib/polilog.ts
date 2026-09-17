/** Truncated polilog Li_s(z) = Σ_{n=1}^N z^n / n^s (complex z). Valid for |z| ≤ 1. */
export function polilog(
  s: number,
  re: number,
  im: number,
  nTerms = 6000
): { re: number; im: number } {
  let sumRe = 0;
  let sumIm = 0;
  let pRe = 1;
  let pIm = 0;
  for (let n = 1; n <= nTerms; n++) {
    const nRe = pRe * re - pIm * im;
    const nIm = pRe * im + pIm * re;
    pRe = nRe;
    pIm = nIm;
    const den = Math.pow(n, s);
    sumRe += pRe / den;
    sumIm += pIm / den;
  }
  return { re: sumRe, im: sumIm };
}

export function fmtC(z: { re: number; im: number }, d = 5): string {
  const a = Number(z.re.toFixed(d));
  const b = Math.abs(Number(z.im.toFixed(d)));
  if (b < 10 ** -d) return String(a);
  return `${a}${z.im >= 0 ? " + " : " − "}${b} i`;
}

export function mod2(re: number, im: number): number {
  return re * re + im * im;
}

/** Principal Log of a complex number. */
function clog(re: number, im: number): { re: number; im: number } {
  return { re: Math.log(Math.hypot(re, im)), im: Math.atan2(im, re) };
}

function cmul(
  a: { re: number; im: number },
  b: { re: number; im: number }
): { re: number; im: number } {
  return { re: a.re * b.re - a.im * b.im, im: a.re * b.im + a.im * b.re };
}

function cpow3(L: { re: number; im: number }): { re: number; im: number } {
  return cmul(cmul(L, L), L);
}

/**
 * Analytic continuation of Li_2 / Li_3 via inversion for |z| > 1:
 *   Li₂(z) = −Li₂(1/z) − π²/6 − ½ [Ln(−z)]²
 *   Li₃(z) =  Li₃(1/z) − (π²/6) Ln(−z) − ⅙ [Ln(−z)]³
 * (principal Ln; avoid the positive-real cut for −z when possible.)
 * For |z| ≤ 1, falls back to the power series.
 */
export function polilogContinued(
  s: 2 | 3,
  re: number,
  im: number,
  nTerms = 6000
): { re: number; im: number; mode: "series" | "continued" } {
  const r2 = mod2(re, im);
  if (r2 <= 1 + 1e-12) {
    return { ...polilog(s, re, im, nTerms), mode: "series" };
  }
  const invRe = re / r2;
  const invIm = -im / r2;
  const inner = polilog(s, invRe, invIm, nTerms);
  const L = clog(-re, -im); // Ln(−z)
  const PI2_6 = (Math.PI * Math.PI) / 6;

  if (s === 2) {
    const L2 = cmul(L, L);
    return {
      re: -inner.re - PI2_6 - 0.5 * L2.re,
      im: -inner.im - 0.5 * L2.im,
      mode: "continued",
    };
  }
  // s === 3
  const L3 = cpow3(L);
  return {
    re: inner.re - PI2_6 * L.re - L3.re / 6,
    im: inner.im - PI2_6 * L.im - L3.im / 6,
    mode: "continued",
  };
}
