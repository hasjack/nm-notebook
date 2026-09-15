export function fmt(x: number, d: number): string {
  return String(Number(x.toFixed(d)));
}

export function fmtBase(b: number): string {
  if (Math.abs(b - Math.E) < 0.01) return "e";
  if (Math.abs(b - Math.E ** 2) < 0.05) return "e²";
  if (Math.abs(b - Math.E ** 3) < 0.15) return "e³";
  if (Math.abs(b - Math.E ** -1) < 0.01) return "1/e";
  if (Math.abs(b - Math.E ** -3) < 0.01) return "1/e³";
  if (Math.abs(b - 1) < 0.02) return "1";
  return fmt(b, 3);
}

/** Map slider 0..1 → base in (0.05, 22) via ln, skipping a hole around 1. */
export function baseFromSlider(t: number): number {
  const uMin = Math.log(0.05);
  const uMax = Math.log(22);
  if (t < 0.5) {
    const s = t / 0.5;
    const u = uMin + s * (-0.08 - uMin);
    return Math.exp(u);
  }
  const s = (t - 0.5) / 0.5;
  const u = 0.08 + s * (uMax - 0.08);
  return Math.exp(u);
}

export function sliderFromBase(base: number): number {
  const u = Math.log(base);
  const uMin = Math.log(0.05);
  const uMax = Math.log(22);
  if (u < 0) {
    return (0.5 * (u - uMin)) / (-0.08 - uMin);
  }
  return 0.5 + (0.5 * (u - 0.08)) / (uMax - 0.08);
}
