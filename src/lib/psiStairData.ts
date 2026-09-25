/** Hardcoded Odlyzko γ’s + primes for the ψ-stair Lab plot.
 *  Do not compute critical zeros in TypeScript — values from Odlyzko’s tables.
 *  Findings / visualisation only.
 */

/** Imaginary parts γ of the first 50 critical zeros (Odlyzko). */
export const ODLYZKO_GAMMAS: readonly number[] = [
  14.134725142,
  21.022039639,
  25.010857580,
  30.424876126,
  32.935061588,
  37.586178159,
  40.918719012,
  43.327073281,
  48.005150881,
  49.773832478,
  52.970321478,
  56.446247697,
  59.347044003,
  60.831778525,
  65.112544048,
  67.079810529,
  69.546401711,
  72.067157674,
  75.704690699,
  77.144840069,
  79.337375020,
  82.910380854,
  84.735492981,
  87.425274613,
  88.809111208,
  92.491899271,
  94.651344041,
  95.870634228,
  98.831194218,
  101.317851006,
  103.725538040,
  105.446623052,
  107.168611184,
  111.029535543,
  111.874659177,
  114.320220915,
  116.226680321,
  118.790782866,
  121.370125002,
  122.946829294,
  124.256818554,
  127.516683880,
  129.578704200,
  131.087688531,
  133.497737203,
  134.756509753,
  138.116042055,
  139.736208952,
  141.123707404,
  143.111845808,
];

/** Primes ≤ 1000 for building the Chebyshev ψ stair. */
export const PRIMES_TO_1000: readonly number[] = [
  2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53,
  59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131,
  137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223,
  227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311,
  313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409,
  419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503,
  509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613,
  617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719,
  727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827,
  829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941,
  947, 953, 967, 971, 977, 983, 991, 997,
];

export const PSI_STAIR_X_MAX = 1000;

/** Main term matching the truncated explicit formula: x − log(2π). */
export function mainTerm(x: number): number {
  return x - Math.log(2 * Math.PI);
}

/** Wave for one conjugate pair ρ, ρ̄ with ρ = 1/2 + iγ (Jack’s sketch). */
export function zeroWave(x: number, gamma: number): number {
  if (x <= 0) return 0;
  return (
    ((2 * Math.sqrt(x)) / Math.hypot(0.5, gamma)) *
    Math.cos(gamma * Math.log(x) - Math.atan2(gamma, 0.5))
  );
}

/** Truncated formula: main − Σ_{k=1..n} wave(γ_k). n = 0 → main only. */
export function psiFromZeros(x: number, n: number): number {
  let s = mainTerm(x);
  const m = Math.min(n, ODLYZKO_GAMMAS.length);
  for (let i = 0; i < m; i++) s -= zeroWave(x, ODLYZKO_GAMMAS[i]!);
  return s;
}

/** Chebyshev ψ(x) = Σ_{p^k ≤ x} log p, using PRIMES_TO_1000. */
export function psiStair(x: number): number {
  if (x < 2) return 0;
  let s = 0;
  for (const p of PRIMES_TO_1000) {
    if (p > x) break;
    let pk = p;
    const logp = Math.log(p);
    while (pk <= x) {
      s += logp;
      const next = pk * p;
      if (next / p !== pk) break; // overflow guard
      pk = next;
    }
  }
  return s;
}
