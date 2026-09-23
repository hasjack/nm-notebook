/** Small exact sieve for the interactive explorer, independent of the census. */
export const EXPLORER_LIMIT = 12000;
const spf = new Uint32Array(EXPLORER_LIMIT + 2);
for (let p = 2; p < spf.length; p++) {
  if (spf[p]) continue;
  spf[p] = p;
  for (let n = p * p; n < spf.length; n += p) if (!spf[n]) spf[n] = p;
}

export const isExplorerPrime = (n: number) => n >= 2 && n < spf.length && spf[n] === n;
export const doorOf = (n: number) => n + (n % 3 === 1 ? 1 : -1);
export const superscript = (n: number) => String(n).split("").map(c => "⁰¹²³⁴⁵⁶⁷⁸⁹"[Number(c)]).join("");
export function factorText(n: number): string {
  if (!Number.isInteger(n) || n < 2 || n >= spf.length) throw new RangeError("Outside explorer sieve");
  const result: string[] = [];
  while (n > 1) {
    const q = spf[n];
    let e = 0;
    while (n % q === 0) { n /= q; e++; }
    result.push(`${q}${e > 1 ? superscript(e) : ""}`);
  }
  return result.join(" × ");
}

export const coverageLanes = [
  { label: "All primes", divisor: 0 },
  { label: "5", divisor: 5 },
  { label: "7", divisor: 7 },
  { label: "7²", divisor: 49 },
  { label: "11", divisor: 11 },
].map(({ label, divisor }) => {
  const candidates: number[] = [];
  if (!divisor) {
    for (let p = 2; p <= EXPLORER_LIMIT; p++) if (isExplorerPrime(p)) candidates.push(p);
  } else {
    for (let d = 2 * divisor; d <= EXPLORER_LIMIT; d += 2 * divisor) {
      if (d % 3 === 0) continue;
      candidates.push(d + (d % 3 === 1 ? 1 : -1));
    }
  }
  return { label, divisor, candidates, hires: candidates.filter(isExplorerPrime) };
});
