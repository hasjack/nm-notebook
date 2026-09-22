import { Link } from "react-router-dom";
import { SwitchingAtlasExplorer } from "../components/SwitchingAtlasExplorer";

const CDN =
  "https://cdn.halfasecond.com/images/onGravity/quadratic-atlas/outputs";

export function AtlasPage() {
  return (
    <main className="page notes">
      <h1>Switching quadratic atlas</h1>
      <p className="lede">
        Carry a binary orientation through the real quadratic map and treat
        flips as diagnostics. Escape-time colouring is the old view; flip
        parity, first-flip, and occupancy show the switching skeleton. First
        published 15 April 2026 on{" "}
        <a href="https://halfasecond.com/notes/switching-quadratic-atlas-diagnostics">
          halfasecond.com
        </a>
        .
      </p>

      <h2>Family</h2>
      <p>
        Baseline: xₙ₊₁ = xₙ² + c. Switching family: xₙ₊₁ = σₙ xₙ² + c with
        σ ∈ {"{"}+1, −1{"}"}. Threshold rule (default):
      </p>
      <p>
        σₙ₊₁ = −σₙ if |xₙ₊₁| &gt; 1 + |b|κ, else σₙ.
      </p>
      <p>
        Here b = x₀. κ deforms the flip boundary. Fixed-sign references +x²+c
        and −x²+c keep the quadratic skeleton without switching. A sign–sin
        gate is in the explorer as a comparison rule.
      </p>

      <h2>Diagnostics</h2>
      <ul>
        <li>escape time — first iterate past the escape radius</li>
        <li>flip count / parity / final orientation</li>
        <li>first-flip iteration — immediate vs delayed vs never</li>
        <li>occupancy — fraction of steps in σ = +1 and σ = −1</li>
      </ul>
      <p>
        First-flip is the mechanism-facing panel: event-time curves where the
        orbit first hits the flip boundary.
      </p>

      <h2>Morphology</h2>
      <p>
        At κ = 0.6235 the switching atlas grows a left-hand wedge and nested
        right-hand bands. Neither wedge nor those bands sit in the two
        fixed-sign baselines, so they are switching-generated. Delayed
        first-flip contours look like a hitting-time / preimage skeleton of
        |x| = 1+|b|κ.
      </p>
      <figure>
        <img
          className="note-fig"
          src={`${CDN}/nm_atlas_orientation_ladder_kappa_0_6235.png`}
          alt="Fixed-sign baselines versus threshold-switching atlas at κ = 0.6235"
        />
        <figcaption className="hint">
          Comparison ladder at κ = 0.6235: preserving sign, reversing sign,
          threshold switching.
        </figcaption>
      </figure>
      <figure>
        <img
          className="note-fig"
          src={`${CDN}/nm_parity_atlas_kappa_0_6235.png`}
          alt="Flip diagnostics at κ = 0.6235"
        />
        <figcaption className="hint">
          Flip count, parity, final orientation, first-flip iteration.
        </figcaption>
      </figure>

      <h2>Explorer</h2>
      <SwitchingAtlasExplorer />

      <p>
        Same <code>(σ, p)</code> cut: <Link to="/toys/bell">Bell toy</Link>.
        Python:{" "}
        <a href="https://github.com/hasjack/OnGravity/tree/main/python/quadratic-atlas">
          OnGravity/python/quadratic-atlas
        </a>
        .
      </p>
    </main>
  );
}
