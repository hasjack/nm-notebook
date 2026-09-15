/**
 * e-walk: a number line spoken only in e, i, and π.
 *
 * Expression: base^(α · i · βπ)
 * Angle: α · β · π · ln(base)
 *
 * Landing on −1 requires α · β · ln(base) = odd integer (±1, ±3, ±5, …).
 *
 * Walk: α = β = 1 (classical iπ), vary base.
 * Lock i: α = 1 fixed; retune π-factor β (or free-β).
 * Lock π: β = 1 fixed; retune i-factor α (or free-α).
 *
 * Internal code may use a product variable (= α·β). UI never names that product "k".
 */

export type Pt = { x: number; y: number; z: number };

export const ODDS = [-5, -3, -1, 1, 3, 5] as const;

/** product = α·β enters the angle as base^(product · i · π). */
export function curve(product: number, base: number): Pt {
  const ang = product * Math.PI * Math.log(base);
  return { x: base, y: Math.cos(ang), z: Math.sin(ang) };
}

/** base^(product · i · π) as a readable complex string. */
export function resultAt(product: number, base: number): string {
  const ang = product * Math.PI * Math.log(base);
  const re = Math.cos(ang);
  const im = Math.sin(ang);
  if (Math.abs(im) < 1e-8 && Math.abs(re + 1) < 1e-8) return "−1";
  if (Math.abs(im) < 1e-8 && Math.abs(re - 1) < 1e-8) return "1";
  if (Math.abs(re) < 1e-8) return `${im.toFixed(4)} i`;
  const sign = im >= 0 ? "+" : "−";
  return `${re.toFixed(4)} ${sign} ${Math.abs(im).toFixed(4)} i`;
}

/** Classic Euler readout at base e with product = 1 → e^(iπ). */
export function resultAtE(product: number = 1): string {
  return resultAt(product, Math.E);
}

/**
 * Magnitude dial σ: base^(σ + α·i·βπ) = base^σ · (cos θ + i sin θ),
 * θ = α·β·π·ln(base). σ = 0 recovers the unit-cylinder ribbon.
 */
export function curveMag(product: number, base: number, sigma = 0): Pt {
  const ang = product * Math.PI * Math.log(base);
  const mag = base === 0 ? 0 : Math.pow(base, sigma);
  return { x: base, y: mag * Math.cos(ang), z: mag * Math.sin(ang) };
}

export function walkMag(
  product: number,
  sigma = 0,
  baseMin = 0.05,
  baseMax = 22
): Pt[] {
  const uMin = Math.log(baseMin);
  const uMax = Math.log(baseMax);
  const turns = Math.abs(product) * (uMax - uMin);
  const n = Math.min(12000, Math.max(2500, Math.ceil(turns * 180)));
  const pts: Pt[] = [];
  for (let i = 0; i <= n; i++) {
    const u = uMin + ((uMax - uMin) * i) / n;
    pts.push(curveMag(product, Math.exp(u), sigma));
  }
  return pts;
}

export function resultAtMag(product: number, base: number, sigma = 0): string {
  const ang = product * Math.PI * Math.log(base);
  const mag = Math.pow(base, sigma);
  const re = mag * Math.cos(ang);
  const im = mag * Math.sin(ang);
  if (Math.abs(im) < 1e-8 * Math.max(1, mag) && Math.abs(re + mag) < 1e-8 * Math.max(1, mag) && Math.abs(mag - 1) < 1e-8)
    return "−1";
  if (Math.abs(im) < 1e-8 * Math.max(1, mag) && Math.abs(re - mag) < 1e-8 * Math.max(1, mag) && Math.abs(mag - 1) < 1e-8)
    return "1";
  if (Math.abs(im) < 1e-10) return re.toFixed(4);
  if (Math.abs(re) < 1e-10) return `${im.toFixed(4)} i`;
  const sign = im >= 0 ? "+" : "−";
  return `${re.toFixed(4)} ${sign} ${Math.abs(im).toFixed(4)} i`;
}

export function magnitudeAt(base: number, sigma: number): number {
  return Math.pow(base, sigma);
}


/**
 * Product α·β that keeps base^(α i βπ) = −1 on a chosen odd branch.
 * Undefined at base = 1 (ln 1 = 0).
 * Prefer piFactorForMinusOne / iFactorForMinusOne in UI-facing call sites.
 */
export function kForMinusOne(base: number, odd: number = 1): number | null {
  if (!(odd % 2)) return null;
  const u = Math.log(base);
  if (Math.abs(u) < 1e-12) return null;
  return odd / u;
}

/**
 * π-factor β that locks −1 when i-factor α = 1:
 *   β = odd / ln(base)
 */
export function piFactorForMinusOne(base: number, odd: number = 1): number | null {
  return kForMinusOne(base, odd);
}

/**
 * i-factor α that locks −1 when π-factor β = 1:
 *   α = odd / ln(base)
 */
export function iFactorForMinusOne(base: number, odd: number = 1): number | null {
  return kForMinusOne(base, odd);
}

/**
 * Base that locks −1 for a free factor when its partner is 1:
 *   base = e^(odd / factor)
 * Use with factor = β under lock-i (α=1), or factor = α under lock-π (β=1).
 */
export function baseForMinusOne(factor: number, odd: number = 1): number | null {
  if (!(odd % 2)) return null;
  if (!Number.isFinite(factor) || Math.abs(factor) < 1e-15) return null;
  return Math.exp(odd / factor);
}

/** Bases where a fixed product still gives −1: base = e^(odd / product). */
export function basesForMinusOne(
  product: number,
  odds: readonly number[] = ODDS
): number[] {
  if (Math.abs(product) < 1e-12) return [];
  return odds.map((odd) => Math.exp(odd / product));
}

/**
 * Sample the walk uniformly in ln(base) so angle advances evenly.
 * Point count scales with |product| to avoid lumpy straight-chord artefacts.
 */
export function walk(product: number, baseMin = 0.05, baseMax = 22): Pt[] {
  const uMin = Math.log(baseMin);
  const uMax = Math.log(baseMax);
  const turns = Math.abs(product) * (uMax - uMin);
  const n = Math.min(12000, Math.max(2500, Math.ceil(turns * 180)));
  const pts: Pt[] = [];
  for (let i = 0; i <= n; i++) {
    const u = uMin + ((uMax - uMin) * i) / n;
    pts.push(curve(product, Math.exp(u)));
  }
  return pts;
}

/** Sample the −1 locus in (ln base, factor) for one odd branch: factor · ln(base) = odd. */
export function locusMinusOne(
  odd: number,
  uMin = Math.log(0.05),
  uMax = Math.log(22),
  n = 400
): { u: number[]; factor: number[]; base: number[]; /** @deprecated alias */ k: number[] } {
  const u: number[] = [];
  const factor: number[] = [];
  const base: number[] = [];
  for (let i = 0; i <= n; i++) {
    const ui = uMin + ((uMax - uMin) * i) / n;
    if (Math.abs(ui) < 0.02) continue; // skip the singularity at base = 1
    u.push(ui);
    factor.push(odd / ui);
    base.push(Math.exp(ui));
  }
  return { u, factor, base, k: factor };
}

export const MARKS = [
  { base: Math.E ** -3, label: "1/e³", ln: -3 },
  { base: Math.E ** -1, label: "1/e", ln: -1 },
  { base: 1, label: "1", ln: 0 },
  { base: Math.E, label: "e", ln: 1 },
  { base: Math.E ** 2, label: "e²", ln: 2 },
  { base: Math.E ** 3, label: "e³", ln: 3 },
] as const;

/* ── α / β factors (product = α·β) ─────────────────────────────────── */

export type AlphaBeta = {
  alpha: number;
  beta: number;
  /** α·β — composite strength in the angle */
  product: number;
};

/**
 * Split a fixed product (= α·β) into (α, β) with share ∈ [0, 1].
 * Kept for internal maths; UI no longer exposes a share dial named around k.
 */
export function productToAlphaBeta(product: number, share: number): AlphaBeta {
  const s = Math.min(1, Math.max(0, share));
  if (!Number.isFinite(product) || Math.abs(product) < 1e-15) {
    return { alpha: 0, beta: 0, product: 0 };
  }
  const mag = Math.abs(product);
  const sign = Math.sign(product); // ±1
  const alpha = sign * Math.pow(mag, s);
  const beta = product / alpha;
  return { alpha, beta, product };
}

export function productFromAlphaBeta(alpha: number, beta: number): number {
  return alpha * beta;
}

/**
 * Lock −1 with a free α: choose α ≠ 0, then
 *   β = odd / (α · ln(base))
 */
export function betaForMinusOne(
  alpha: number,
  base: number,
  odd: number = 1
): number | null {
  if (!(odd % 2)) return null;
  if (!Number.isFinite(alpha) || Math.abs(alpha) < 1e-15) return null;
  const u = Math.log(base);
  if (Math.abs(u) < 1e-12) return null;
  return odd / (alpha * u);
}

/**
 * Lock −1 with a free β: choose β ≠ 0, then
 *   α = odd / (β · ln(base))
 */
export function alphaForMinusOne(
  beta: number,
  base: number,
  odd: number = 1
): number | null {
  if (!(odd % 2)) return null;
  if (!Number.isFinite(beta) || Math.abs(beta) < 1e-15) return null;
  const u = Math.log(base);
  if (Math.abs(u) < 1e-12) return null;
  return odd / (beta * u);
}

export function alphaBetaForMinusOne(
  base: number,
  odd: number,
  share: number
): AlphaBeta | null {
  const product = kForMinusOne(base, odd);
  if (product == null || !Number.isFinite(product)) return null;
  return productToAlphaBeta(product, share);
}

export function curveSplit(alpha: number, beta: number, base: number): Pt {
  return curve(alpha * beta, base);
}

export function resultAtSplit(alpha: number, beta: number, base: number): string {
  return resultAt(alpha * beta, base);
}
