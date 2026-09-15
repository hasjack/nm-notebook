/**
 * e-walk: a number line spoken only in e, i, and π.
 *
 * Identity held fixed: base^(k · i · π) = −1
 *   ⇔  cos(k π ln base) + i sin(k π ln base) = −1
 *   ⇔  k · ln(base) = odd integer  (±1, ±3, ±5, …)
 *
 * Free mode: pick k, walk over base.
 * Lock mode: pick base (and branch odd), solve k = odd / ln(base).
 * Split mode: write k = α·β so base^(α · i · βπ); lock −1 ⇒ αβ·ln(base)=odd.
 */

export type Pt = { x: number; y: number; z: number };

export const ODDS = [-5, -3, -1, 1, 3, 5] as const;

export function curve(k: number, base: number): Pt {
  const ang = k * Math.PI * Math.log(base);
  return { x: base, y: Math.cos(ang), z: Math.sin(ang) };
}

/** base^(k i π) as a readable complex string. */
export function resultAt(k: number, base: number): string {
  const ang = k * Math.PI * Math.log(base);
  const re = Math.cos(ang);
  const im = Math.sin(ang);
  if (Math.abs(im) < 1e-8 && Math.abs(re + 1) < 1e-8) return "−1";
  if (Math.abs(im) < 1e-8 && Math.abs(re - 1) < 1e-8) return "1";
  if (Math.abs(re) < 1e-8) return `${im.toFixed(4)} i`;
  const sign = im >= 0 ? "+" : "−";
  return `${re.toFixed(4)} ${sign} ${Math.abs(im).toFixed(4)} i`;
}

/** Classic Euler readout at base e. */
export function resultAtE(k: number): string {
  return resultAt(k, Math.E);
}

/**
 * k that keeps base^(k i π) = −1 on a chosen odd branch.
 * Undefined at base = 1 (ln 1 = 0).
 */
export function kForMinusOne(base: number, odd: number = 1): number | null {
  if (!(odd % 2)) return null;
  const u = Math.log(base);
  if (Math.abs(u) < 1e-12) return null;
  return odd / u;
}

/** Bases where a fixed k still gives −1: base = e^(odd / k). */
export function basesForMinusOne(k: number, odds: readonly number[] = ODDS): number[] {
  if (Math.abs(k) < 1e-12) return [];
  return odds.map((odd) => Math.exp(odd / k));
}

/**
 * Sample the walk uniformly in ln(base) so angle advances evenly.
 * Point count scales with |k| to avoid lumpy straight-chord artefacts.
 */
export function walk(k: number, baseMin = 0.05, baseMax = 22): Pt[] {
  const uMin = Math.log(baseMin);
  const uMax = Math.log(baseMax);
  const turns = Math.abs(k) * (uMax - uMin);
  const n = Math.min(12000, Math.max(2500, Math.ceil(turns * 180)));
  const pts: Pt[] = [];
  for (let i = 0; i <= n; i++) {
    const u = uMin + ((uMax - uMin) * i) / n;
    pts.push(curve(k, Math.exp(u)));
  }
  return pts;
}

/** Sample the −1 locus in (ln base, k) for one odd branch. */
export function locusMinusOne(
  odd: number,
  uMin = Math.log(0.05),
  uMax = Math.log(22),
  n = 400
): { u: number[]; k: number[]; base: number[] } {
  const u: number[] = [];
  const k: number[] = [];
  const base: number[] = [];
  for (let i = 0; i <= n; i++) {
    const ui = uMin + ((uMax - uMin) * i) / n;
    if (Math.abs(ui) < 0.02) continue; // skip the singularity at base = 1
    u.push(ui);
    k.push(odd / ui);
    base.push(Math.exp(ui));
  }
  return { u, k, base };
}

export const MARKS = [
  { base: Math.E ** -3, label: "1/e³", ln: -3 },
  { base: Math.E ** -1, label: "1/e", ln: -1 },
  { base: 1, label: "1", ln: 0 },
  { base: Math.E, label: "e", ln: 1 },
  { base: Math.E ** 2, label: "e²", ln: 2 },
  { base: Math.E ** 3, label: "e³", ln: 3 },
] as const;

/* ── α / β split (k = α·β) ─────────────────────────────────────────── */

export type AlphaBeta = {
  alpha: number;
  beta: number;
  /** α·β — same role as free-mode k */
  product: number;
};

/**
 * Split a fixed product (= α·β = k) into (α, β) with share ∈ [0, 1].
 *
 * Geometric, sign-aware rule:
 *   α = sign(product) · |product|^share
 *   β = product / α   (= |product|^(1−share) ≥ 0 when product ≠ 0)
 *
 * Endpoints (product ≠ 0):
 *   share = 0 → α = ±1,           β = |product|
 *   share = ½ → |α| = |β| = √|P|, α carries the sign
 *   share = 1 → α = product,      β = 1
 *
 * So the dial trades magnitude between the “i” factor (α) and the “π”
 * factor (β) while keeping α·β = product exactly. Near product = 0 both
 * collapse toward 0.
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

/** α·β — the composite strength that enters the angle as k. */
export function productFromAlphaBeta(alpha: number, beta: number): number {
  return alpha * beta;
}

/**
 * Lock −1 with a free α: choose α ≠ 0, then
 *   β = odd / (α · ln(base))
 * so that α·β·ln(base) = odd.
 * Returns null at base→1 or α→0.
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
 * Lock −1 via product: product = k = odd / ln(base), then split with share.
 * Convenience wrapper used by the Split view.
 */
export function alphaBetaForMinusOne(
  base: number,
  odd: number,
  share: number
): AlphaBeta | null {
  const product = kForMinusOne(base, odd);
  if (product == null || !Number.isFinite(product)) return null;
  return productToAlphaBeta(product, share);
}

/** Angle for base^(α · i · βπ): same as curve(α·β, base). */
export function curveSplit(alpha: number, beta: number, base: number): Pt {
  return curve(alpha * beta, base);
}

export function resultAtSplit(alpha: number, beta: number, base: number): string {
  return resultAt(alpha * beta, base);
}
