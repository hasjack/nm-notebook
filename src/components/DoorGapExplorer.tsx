import { useEffect, useMemo, useRef, useState } from "react";
import { coverageLanes, doorOf, factorText, isExplorerPrime } from "../lib/doorCoverage";

export function DoorGapExplorer() {
  const [start, setStart] = useState(0);
  const [span, setSpan] = useState(500);
  const [lane, setLane] = useState(3);
  const [picked, setPicked] = useState(391);
  const [width, setWidth] = useState(640);
  const chart = useRef<HTMLDivElement>(null);
  useEffect(() => {
    const el = chart.current;
    if (!el) return;
    const observer = new ResizeObserver(([entry]) => setWidth(Math.max(260, entry.contentRect.width)));
    observer.observe(el);
    return () => observer.disconnect();
  }, []);
  const end = start + span;
  const visible = useMemo(() => coverageLanes.map(row => row.candidates.filter(p => p >= start && p <= end)), [start, end]);
  const selected = visible[lane].includes(picked) ? picked : visible[lane][0];
  const left = 76, right = width - 12;
  const x = (p: number) => left + 5 + (p - start) / span * (right - left - 10);
  const row = coverageLanes[lane];
  const previous = row.hires.findLast(p => p < selected);
  const next = row.hires.find(p => p > selected);
  const successful = selected !== undefined && isExplorerPrime(selected);
  const gap = selected === undefined ? "No candidates in this window."
    : successful ? `Next ${lane === 0 ? "prime" : "hire"}: ${next ?? "beyond the computed range"}${next ? ` · gap ${next - selected}` : ""}.`
      : previous && next ? `Between hires ${previous} and ${next}: gap ${next - previous}.`
        : `Before first hire ${next ?? "beyond the computed range"}.`;
  const tickCount = width < 450 ? 2 : 5;
  return (
    <section className="door-gap-explorer" aria-label="Interactive prime and door gaps">
      <div className="coverage-controls">
        <label>Window starts at<input type="number" min={0} max={9000} step={100} value={start}
          onChange={e => setStart(Math.min(9000, Math.max(0, Math.floor(Number(e.target.value) || 0))))} /></label>
        <label>Window width<select aria-label="Window width" value={span} onChange={e => setSpan(Number(e.target.value))}>
          <option value={200}>200</option><option value={500}>500</option><option value={1000}>1,000</option>
        </select></label>
        <button type="button" onClick={() => { setStart(3600); setSpan(1000); setLane(3); setPicked(3919); }}>Show 3,600–4,600</button>
      </div>
      <p className="figure-caption">● Prime · ○ Composite candidate · Shaded intervals separate consecutive hires; labels give full gap lengths, including intervals clipped by the window.</p>
      <div ref={chart}>
        <svg className="coverage-gap-chart" viewBox={`0 0 ${width} 380`} role="img" aria-labelledby="coverage-gap-title coverage-gap-desc">
          <title id="coverage-gap-title">Prime gaps and ingredient waiting zones</title>
          <desc id="coverage-gap-desc">Aligned lanes from {start} to {end}. Filled points are prime; hollow points are composite. Use the inspection controls below for keyboard access to every point.</desc>
          <rect x={left} y={28} width={right - left} height={300} className="coverage-frame" />
          {coverageLanes.map((r, i) => {
            const y = 56 + i * 60;
            return <g key={r.label}>
              {r.hires.slice(1).map((b, j) => {
                const a = r.hires[j], lo = Math.max(start, a), hi = Math.min(end, b);
                if (hi <= lo) return null;
                const w = x(hi) - x(lo);
                return <g key={a}>
                  <rect x={x(lo)} y={y - 16} width={w} height={32} className={j % 2 ? "coverage-zone alternate" : "coverage-zone"} />
                  {w > 58 && <text x={(x(lo) + x(hi)) / 2} y={y - 21} textAnchor="middle">{b - a}</text>}
                </g>;
              })}
              <line x1={left} x2={right} y1={y} y2={y} className="coverage-axis" />
              <text x={left - 10} y={y + 4} textAnchor="end">{r.label}</text>
              {visible[i].map(p => <circle key={p} cx={x(p)} cy={y} r={3.6}
                className={isExplorerPrime(p) ? "coverage-prime" : "coverage-composite"} />)}
              <rect x={left} y={y - 25} width={right - left} height={50} fill="transparent" className="coverage-hit"
                onClick={event => {
                  const bounds = event.currentTarget.ownerSVGElement!.getBoundingClientRect();
                  const cursorX = (event.clientX - bounds.left) * width / bounds.width;
                  const nearest = visible[i].reduce<number | undefined>((best, p) => best === undefined || Math.abs(x(p) - cursorX) < Math.abs(x(best) - cursorX) ? p : best, undefined);
                  if (nearest !== undefined) { setLane(i); setPicked(nearest); }
                }} />
            </g>;
          })}
          {selected !== undefined && <circle cx={x(selected)} cy={56 + lane * 60} r={8} className="coverage-selected" pointerEvents="none" />}
          {Array.from({ length: tickCount + 1 }, (_, i) => {
            const p = start + span * i / tickCount;
            return <g key={i}><line x1={x(p)} x2={x(p)} y1={328} y2={334} className="coverage-axis" />
              <text x={x(p)} y={351} textAnchor={i === 0 ? "start" : i === tickCount ? "end" : "middle"}>{p.toLocaleString("en-GB")}</text></g>;
          })}
          <text x={(left + right) / 2} y={376} textAnchor="middle">Number-line position</text>
          <text x={left} y={16}>Lane / gap length</text>
        </svg>
      </div>
      <div className="coverage-controls">
        <label>Inspect lane<select aria-label="Inspect lane" value={lane} onChange={e => setLane(Number(e.target.value))}>
          {coverageLanes.map((r, i) => <option key={r.label} value={i}>{r.label}</option>)}
        </select></label>
        <label>Inspect position<select aria-label="Inspect position" value={selected ?? ""} disabled={selected === undefined} onChange={e => setPicked(Number(e.target.value))}>
          {selected === undefined && <option value="">No candidates</option>}
          {visible[lane].map(p => <option key={p} value={p}>{p} · {isExplorerPrime(p) ? "prime" : "composite"}</option>)}
        </select></label>
      </div>
      <div aria-live="polite" className="coverage-inspection">
        {selected !== undefined && <p><strong>{selected}</strong>: {successful ? "prime" : `composite = ${factorText(selected)}`}
          {lane !== 0 && <>. Door {doorOf(selected)} = {factorText(doorOf(selected))}</>}.</p>}
        <p>{gap}</p>
      </div>
    </section>
  );
}
