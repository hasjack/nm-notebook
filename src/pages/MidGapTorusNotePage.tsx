import { Link } from "react-router-dom";

/** Saturday note — PDF in public/paper/mid-gap-and-torus.pdf. */
export function MidGapTorusNotePage() {
  return (
    <main className="page paper-page">
      <h1>A midpoint identity for the complementary torus order</h1>
      <p className="lede paper-abstract">
        For an odd prime <em>p</em> ≠ 3, χ₃(<em>p</em>) = (−3/<em>p</em>) and{" "}
        <em>m</em>
        <sub>0</sub>(<em>p</em>) = <em>p</em> + χ₃(<em>p</em>). Then 1/<em>m</em>
        <sub>0</sub> − ½(1/(<em>p</em> − 1) + 1/(<em>p</em> + 1)) = −χ₃(<em>p</em>
        )/(<em>p</em>² − 1). Mid-gap is the identity; the offset ≈ 0.025988… is
        the series. Not an <em>H</em>(<em>X</em>) claim. Lab:{" "}
        <Link to="/hire-lab">Hire rate</Link>, <Link to="/torus">Torus</Link>.
      </p>

      <div className="paper-viewer">
        <iframe
          className="paper-frame"
          title="mid-gap-and-torus.pdf"
          src="/paper/mid-gap-and-torus.pdf?v=1790500714#view=FitH"
        />
      </div>

      <h2>Checked Lean</h2>
      <ul className="paper-lean">
        <li>
          <code>Hire/Doors.lean</code>
          <ul>
            <li>
              <code>mid_gap_m0</code>
            </li>
            <li>
              <code>chi3_eq_legendreSym_neg_three</code>
            </li>
          </ul>
        </li>
      </ul>
    </main>
  );
}
