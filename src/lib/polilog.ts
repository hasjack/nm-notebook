/** Truncated polilog Li_s(z) = Σ_{n=1}^N z^n / n^s (complex z). */
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
  // first multiply by z each time starting from z^1
  for (let n = 1; n <= nTerms; n++) {
    // p := p * z
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
