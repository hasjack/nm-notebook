import { Link } from "react-router-dom";

export function GaussianDoorsPage() {
  return (
    <main className="page notes lab-note-page">
      <h1>Gaussian doors</h1>
      <p className="lede">
        Can a prime’s factored 3-free door be built as two squares, then the
        ±1 carried back as a representation by x²+3y²? Same m<sub>0</sub> as
        hire and zeta, different job: quadratic forms, not ownership and not
        Bernoulli denominators. Lab, not the hire graph.
      </p>

      <h2>19</h2>
      <p>
        19 stays prime in the Gaussian integers. It is not two squares. Its
        door is m<sub>0</sub>(19) = 20 = 4²+2². Keep 4, subtract one:
      </p>
      <p>
        19 = 4²+(2²−1) = 4²+3·1² = (4+√−3)(4−√−3).
      </p>
      <p>
        That factors 19 in Z[√−3], not in Z[i].
      </p>

      <h2>The conversion</h2>
      <p>
        For 3 &lt; p ≤ 100,000, take m<sub>0</sub>(p) = p+χ<sub>3</sub>(p).
        Ask whether the door is x²+y², and whether one can keep x and absorb
        the correction as y²−χ<sub>3</sub>(p) = 3b².
      </p>
      <aside className="lab-theorem" aria-label="Pell condition">
        <p>
          p ≡ 1 (mod 3): y² − 3b² = 1 (Pell).
        </p>
        <p className="lab-theorem-implies">
          p ≡ 2 (mod 3): y² + 1 = 3b², impossible mod 3.
        </p>
      </aside>
      <p>
        Pell solutions (y, b) = (2, 1), (7, 4), (26, 15), … give the
        conversions that work. Residues 5 and 11 (mod 12) cannot convert; that
        is the mod-3 obstruction, not a sampling gap.
      </p>
      <div className="door-table-wrap">
        <table className="door-table">
          <thead>
            <tr>
              <th>p (mod 12)</th>
              <th>tested</th>
              <th>a²+3b²</th>
              <th>door two squares</th>
              <th>fixed-x conversion</th>
            </tr>
          </thead>
          <tbody>
            <tr>
              <td>1</td>
              <td>2,374</td>
              <td>2,374</td>
              <td>716</td>
              <td>74</td>
            </tr>
            <tr>
              <td>5</td>
              <td>2,409</td>
              <td>0</td>
              <td>799</td>
              <td>0</td>
            </tr>
            <tr>
              <td>7</td>
              <td>2,410</td>
              <td>2,410</td>
              <td>792</td>
              <td>66</td>
            </tr>
            <tr>
              <td>11</td>
              <td>2,397</td>
              <td>0</td>
              <td>732</td>
              <td>0</td>
            </tr>
            <tr>
              <td>total</td>
              <td>9,590</td>
              <td>4,784</td>
              <td>3,039</td>
              <td>140</td>
            </tr>
          </tbody>
        </table>
      </div>
      <p>
        Residues 1 and 7 are 1 (mod 3), so every such prime already is
        a²+3b². The 140 conversions are a construction path, not 140 new
        representations. The 66 in class 7 are Gaussian primes (like 19) whose
        door still yields the x²+3y² form they already possess.
      </p>
      <div className="door-table-wrap">
        <table className="door-table">
          <thead>
            <tr>
              <th>p</th>
              <th>door</th>
              <th>carry back</th>
            </tr>
          </thead>
          <tbody>
            <tr>
              <td>19</td>
              <td>20 = 4²+2²</td>
              <td>19 = 4²+3·1²</td>
            </tr>
            <tr>
              <td>73</td>
              <td>74 = 5²+7²</td>
              <td>73 = 5²+3·4²</td>
            </tr>
            <tr>
              <td>97</td>
              <td>98 = 7²+7²</td>
              <td>97 = 7²+3·4²</td>
            </tr>
          </tbody>
        </table>
      </div>

      <h2>31 misses</h2>
      <p>
        m<sub>0</sub>(31) = 32 = 4²+4². Keep 4, subtract one: 16+15, and 15 is
        not three times a square. Still 31 = 2²+3·3². The representation
        exists; this route does not find it.
      </p>

      <h2>Strip 3 from the other neighbour</h2>
      <p>
        Separately: all 1,667 multiples of 4 up to 10,000 that are not
        divisible by 3. Take the 3-divisible neighbour, remove every factor of
        3, ask if two squares remain. General even doors, not zeta
        denominators.
      </p>
      <div className="door-table-wrap">
        <table className="door-table">
          <thead>
            <tr>
              <th>before → after</th>
              <th>count</th>
            </tr>
          </thead>
          <tbody>
            <tr>
              <td>no → yes</td>
              <td>467</td>
            </tr>
            <tr>
              <td>yes → yes</td>
              <td>170</td>
            </tr>
            <tr>
              <td>no → no</td>
              <td>1,030</td>
            </tr>
            <tr>
              <td>yes → no</td>
              <td>0</td>
            </tr>
          </tbody>
        </table>
      </div>
      <p>
        Removing all 3s cannot destroy a two-square representation. Removing
        one 3 is different: 45 = 3²+6², but 15 is not two squares.
      </p>
      <p>
        No speed-up over direct representation algorithms. No bound on the
        Gauss circle problem. Code:{" "}
        <code>analysis/gaussian-doors/experiment.py</code>. 3blue1brown:{" "}
        <a href="https://www.3blue1brown.com/lessons/leibniz-formula/">
          Pi hiding in prime regularities
        </a>
        .
      </p>
      <p className="home-actions">
        <Link className="nav-link" to="/zeta-doors">
          Zeta doors
        </Link>
        <Link className="nav-link" to="/hire">
          Introduction
        </Link>
      </p>
    </main>
  );
}
