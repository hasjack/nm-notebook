import { Link } from "react-router-dom";
import { BellToyInteractive } from "../components/BellToy";

const CDN = "https://cdn.halfasecond.com/images/onGravity";

export function BellToyPage() {
  return (
    <main className="page notes">
      <h1>Progress-state Bell toy</h1>
      <p className="lede">
        A local hidden-variable toy built from sector and progress{" "}
        <code>(σ, p)</code>. Flip-on-overflow is the whole algebra. CHSH stays
        classical. First published 12 April 2026 on{" "}
        <a href="https://halfasecond.com/notes/natural-mathematics-bell-toy">
          halfasecond.com
        </a>
        .
      </p>

      <h2>State</h2>
      <p>
        σ ∈ {"{"}+1, −1{"}"} is the current orientation sector; p ∈ [0, 1) is
        progress through that sector. The binary readout is just M = σ.
      </p>
      <p>
        Given δ ≥ 0, set T = p + δ, n = ⌊T⌋, r = T mod 1. The new sector is σ
        if n is even and −σ if n is odd. Remainder r is kept. Several boundary
        crossings in one update only care about the parity of n.
      </p>
      <ul>
        <li>
          (−, 0.75) ⊕ 0.50 → (+, 0.25)
        </li>
        <li>
          (+, 0.10) ⊕ 0.20 → (+, 0.30)
        </li>
        <li>
          (+, 0.90) ⊕ 0.30 → (−, 0.20)
        </li>
        <li>
          (−, 0.30) ⊕ 2.10 → (−, 0.40)
        </li>
      </ul>

      <h2>Bell construction</h2>
      <p>
        A shared source draws σ₀ uniform in {"{"}±1{"}"}, p₀ uniform on [0, 1),
        λ uniform on [−π, π). Each wing gets a setting and a local increment
        δ(setting, λ). Outcomes are the updated sectors. Correlations E(x, y) =
        ⟨Aₓ Bᵧ⟩, and
      </p>
      <p>
        S = E(a,b) + E(a,b′) + E(a′,b) − E(a′,b′).
      </p>
      <p>
        Local rule: d = |wrap(setting − λ)|; δ = 0.85 if d &lt; w, else 0.20.
      </p>

      <h2>Lemma</h2>
      <p>
        If p₀ ∼ Unif[0, 1) and both δ live in [0, 1), then
      </p>
      <p>
        E[Aₓ Bᵧ | λ] = 1 − 2 |δ(x,λ) − δ(y,λ)|.
      </p>
      <p>
        A parity mismatch happens exactly when one wing overflows and the other
        does not; that set has measure |δₓ − δᵧ|. Averaging over λ gives the
        four CHSH channels. For the two-level rule, |δₓ − δᵧ| ∈ {"{"}0, 0.65{"}"}{" "}
        so E(x,y) = 1 − 1.3 P(δₓ ≠ δᵧ).
      </p>
      <p>
        Deterministic local outcomes, so |S| ≤ 2 by the usual theorem. The sweep
        only moves the toy inside the classical region.
      </p>

      <h2>Width sweep</h2>
      <p>
        w = π/6, π/5, π/4, π/3 gives S ≈ 1.46, 1.55, 1.68, 1.89. Three channels
        sit near 0.67; the rise is E(a′,b′) falling from 0.56 to 0.13 — the pair
        whose windows disagree most as functions of λ.
      </p>
      <figure>
        <img
          className="note-fig"
          src={`${CDN}/nm_progress_state_bell_toy.png`}
          alt="Four Bell correlations and CHSH score for a fixed window"
        />
        <figcaption className="hint">
          Figure 1 — representative correlations and CHSH at a fixed w.
        </figcaption>
      </figure>
      <figure>
        <img
          className="note-fig"
          src={`${CDN}/nm_progress_state_bell_width_sweep.png`}
          alt="CHSH versus response-window width"
        />
        <figcaption className="hint">
          Figure 2 — S versus w, approaching but not crossing 2.
        </figcaption>
      </figure>

      <h2>Interactive</h2>
      <BellToyInteractive />

      <p>
        Same algebra, different pictures:{" "}
        <Link to="/toys/atlas">switching atlas</Link>,{" "}
        <Link to="/physics">physics</Link>. Python:{" "}
        <a href="https://github.com/hasjack/OnGravity/tree/main/python/bell-toy">
          OnGravity/python/bell-toy
        </a>
        .
      </p>
    </main>
  );
}
