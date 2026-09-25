import { Link } from "react-router-dom";
import { CubeCurvePlot } from "../components/CubeCurvePlot";
import "./DoorCoveragePage.css";

const fmt = (n: number) => n.toLocaleString("en-GB");

/** Lab: cube doors and opposite-sign sums. */
export function CubeDoorPage() {
  return (
    <main className="page notes lab-note-page door-coverage-page">
      <h1>Cube doors</h1>
      <p className="lede">
        How cubing enlarges a 3-free door, what happens when two cube doors are
        added, the fifth-power twin where 5 can sit in the door and accumulate,
        and a real-curve plot of y = (c³ − x³)<sup>1/3</sup> against nearby
        lattice mismatches R. Related:{" "}
        <Link to="/two-class">Two-class coverage</Link>,{" "}
        <Link to="/door-waits">Door waits</Link>,{" "}
        <Link to="/notes/hire-graph">Paper 1</Link>.
      </p>

      <h2>Cubing keeps the door</h2>
      <p>
        For an odd integer a with 3 ∤ a, write s = χ₃(a). Cubing preserves the
        remainder modulo 6, so a³ ≡ a (mod 6) and the sign of the door sticks:
      </p>
      <aside className="lab-theorem" aria-label="Cube door identity">
        <p className="lab-theorem-implies">
          m₀(a³) = m₀(a) · (a² − s a + 1).
        </p>
      </aside>
      <p>
        The second factor is odd and 3-free, and shares no prime factors with
        m₀(a). The cube’s door therefore keeps the same power of 2 as the
        original door; growth is entirely odd primes. The same neighbour formula
        for m₀ is used on odd composites here.
      </p>
      <div className="door-table-wrap">
        <table className="door-table">
          <thead>
            <tr>
              <th>Base</th>
              <th>Original door</th>
              <th>Cube’s door</th>
            </tr>
          </thead>
          <tbody>
            <tr>
              <td>5</td>
              <td>4 = 2²</td>
              <td>124 = 4 · 31</td>
            </tr>
            <tr>
              <td>7</td>
              <td>8 = 2³</td>
              <td>344 = 8 · 43</td>
            </tr>
            <tr>
              <td>11</td>
              <td>10 = 2 · 5</td>
              <td>1330 = 10 · 7 · 19</td>
            </tr>
            <tr>
              <td>13</td>
              <td>14 = 2 · 7</td>
              <td>2198 = 14 · 157</td>
            </tr>
          </tbody>
        </table>
      </div>


      <h2>Fifth-power doors</h2>
      <p>
        For odd a with 3 ∤ a, write s = χ₃(a), D = m₀(a), and
      </p>
      <aside className="lab-theorem" aria-label="Fifth-power door identity">
        <p className="lab-theorem-implies">
          m₀(a⁵) = D · H,  H = a⁴ − s a³ + a² − s a + 1.
        </p>
      </aside>
      <p>
        Cubing excluded 3 from the door, so the new factor stayed coprime to D.
        Fifth powers allow 5 in the door: gcd(D, H) = gcd(D, 5). Expanding H after
        a = −s + D gives H ≡ 5 (mod 25) when 5 ∣ D, and H ≡ 1 (mod 5) when 5 ∤ D.
        So v₅(H) is exactly 1 or 0:
      </p>
      <aside className="lab-theorem" aria-label="v5 ladder">
        <p className="lab-theorem-implies">
          v₅(m₀(a⁵)) = v₅(m₀(a)) + 1 if 5 ∣ m₀(a), else 0.
        </p>
      </aside>
      <p>
        Iterated fifth powering therefore builds a ladder. If the initial door
        carries 5ᵉ, the doors of a, a⁵, a²⁵, a¹²⁵, … carry exactly 5ᵉ, 5ᵉ⁺¹,
        5ᵉ⁺², 5ᵉ⁺³, … while the power of 2 stays put. Example: m₀(11) = 10 =
        2 · 5, and m₀(11⁵) = 161050 = 2 · 5² · 3221.
      </p>
      <p>
        Clean door dynamics — how an existing ingredient accumulates under
        powering. Not an FLT contradiction.
      </p>

      <h2>Adding two cubes</h2>
      <p>
        With s = χ₃(a) and t = χ₃(b),
      </p>
      <p className="lab-theorem-implies">
        m₀(a³) + m₀(b³) = a³ + b³ + s + t.
      </p>
      <p>
        Same signs: the corrections add to +2 or −2, and a³ + b³ ≡ ±2 (mod 9),
        which is not a cube residue for bases not divisible by 3. Opposite signs:
        the corrections cancel,
      </p>
      <aside className="lab-theorem" aria-label="Opposite-sign sum">
        <p className="lab-theorem-implies">
          a³ + b³ = m₀(a³) + m₀(b³).
        </p>
      </aside>
      <p>
        Example: 5³ + 7³ = 124 + 344 = 468. Each door is 3-free; the sum brings 3
        back.
      </p>

      <h2>Continuous curve vs lattice</h2>
      <p>
        Over reals, y = (c³ − x³)<sup>1/3</sup> balances cubes for every x in
        [0, c]. Integer points (a, b) miss that balance by R = a³ + b³ − c³. The
        plot keeps the continuous arc and the discrete hits distinct: reals have
        no doors.
      </p>
      <CubeCurvePlot />

      <h2>Factorisation of the sum</h2>
      <p>
        a³ + b³ = (a + b)(a² − a b + b²). Write A = a + b and B = a² − a b + b².
        For coprime a, b, any common prime of A and B divides 3: 3 is the only
        bridge between the factors. When 3 ∣ A and A · B is a cube,
      </p>
      <aside className="lab-theorem" aria-label="Cube forces boxed forms">
        <p className="lab-theorem-implies">
          a + b = 9 u³,  a² − a b + b² = 3 v³.
        </p>
      </aside>
      <p>
        Example: 5³ + 67³ = 72 · 4179 with 72 = 9 · 2³ and 4179 = 3 · 1393; 1393
        is not a cube.
      </p>

      <h2>Census through 997</h2>
      <p>
        All {fmt(55278)} unordered pairs of odd, 3-free bases from 5 through
        997:
      </p>
      <div className="door-table-wrap">
        <table className="door-table">
          <thead>
            <tr>
              <th>Filter</th>
              <th>Pairs remaining</th>
            </tr>
          </thead>
          <tbody>
            <tr>
              <td>Starting pairs</td>
              <td>{fmt(55278)}</td>
            </tr>
            <tr>
              <td>Opposite signs</td>
              <td>{fmt(27556)}</td>
            </tr>
            <tr>
              <td>Correct exponent of 3 for a cube</td>
              <td>{fmt(6375)}</td>
            </tr>
            <tr>
              <td>Correct exponents of both 2 and 3</td>
              <td>{fmt(867)}</td>
            </tr>
            <tr>
              <td>Actual cube sums</td>
              <td>0</td>
            </tr>
          </tbody>
        </table>
      </div>
      <p>
        Surviving example: 5³ + 67³ = 300888 = 2³ · 3³ · 7 · 199. The 2 and 3
        exponents fit a cube; the remaining primes do not.
      </p>
    </main>
  );
}
