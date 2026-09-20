import { useMemo } from "react";
import { Link } from "react-router-dom";

function primesUpTo(n: number): number[] {
  if (n < 2) return [];
  const sieve = new Uint8Array(n + 1);
  sieve.fill(1);
  sieve[0] = 0;
  sieve[1] = 0;
  for (let i = 2; i * i <= n; i++) {
    if (!sieve[i]) continue;
    for (let j = i * i; j <= n; j += i) sieve[j] = 0;
  }
  const out: number[] = [];
  for (let i = 2; i <= n; i++) if (sieve[i]) out.push(i);
  return out;
}

function oddPrimesTo(n: number): number[] {
  return primesUpTo(n).filter((p) => p % 2 === 1);
}

/** 3-free door neighbour: p + χ₃(p). */
function doorOf(p: number): number {
  if (p % 3 === 1) return p + 1;
  if (p % 3 === 2) return p - 1;
  return p; // p = 3: no door in this recipe
}

function factorParts(n: number): number[] {
  const parts: number[] = [];
  let x = Math.abs(n);
  for (let d = 2; d * d <= x; d++) {
    while (x % d === 0) {
      parts.push(d);
      x = Math.floor(x / d);
    }
  }
  if (x > 1) parts.push(x);
  return parts;
}

function factorOddPrimes(n: number): number[] {
  return [...new Set(factorParts(n).filter((q) => q !== 2))];
}

type DoorRow = {
  p: number;
  left: number;
  right: number;
  door: number | null;
  sacked: boolean;
  doorFactors: number[];
  sink: boolean;
};

function doorRowsTo(n: number): DoorRow[] {
  return oddPrimesTo(n).map((p) => {
    const left = p - 1;
    const right = p + 1;
    if (p === 3) {
      return {
        p,
        left,
        right,
        door: null,
        sacked: true,
        doorFactors: [],
        sink: false,
      };
    }
    const door = doorOf(p);
    const doorFactors = factorOddPrimes(door);
    return {
      p,
      left,
      right,
      door,
      sacked: false,
      doorFactors,
      sink: doorFactors.length === 0,
    };
  });
}

export function HirePage() {
  const doorRows = useMemo(() => doorRowsTo(100), []);

  return (
    <main className="page">
      <h1>Introduction</h1>
      <p className="lede">
        Non-primes are built from smaller primes. Odd primes sit one step off an
        even number — always <em>p</em>−1 or <em>p</em>+1 — so the factors live
        next door, not inside. The game is which neighbour you are allowed to
        open.
      </p>

      <section className="hire-beat">
        <h2>Neighbours through 100</h2>
        <p className="lede">
          For each odd prime, look at both even neighbours. One of them is always
          divisible by 3 (grey). The other is the <strong>door</strong> — free of
          3. Three itself is sacked: it never gets hired.
        </p>
        <div className="door-table-wrap">
          <table className="door-table">
            <thead>
              <tr>
                <th>p</th>
                <th>p−1</th>
                <th>p+1</th>
                <th>Door</th>
                <th>Odd factors of the door</th>
              </tr>
            </thead>
            <tbody>
              {doorRows.map((row) => (
                <tr
                  key={row.p}
                  className={row.sacked ? "door-row sacked" : "door-row"}
                >
                  <td>
                    <strong>{row.p}</strong>
                    {row.sacked ? (
                      <span className="door-tag">sacked</span>
                    ) : null}
                  </td>
                  <td className={row.left % 3 === 0 ? "by3" : "door-cell"}>
                    {row.left % 3 === 0 ? <s>{row.left}</s> : row.left}
                    {row.left % 3 === 0 ? (
                      <span className="door-tag muted">×3</span>
                    ) : null}
                  </td>
                  <td className={row.right % 3 === 0 ? "by3" : "door-cell"}>
                    {row.right % 3 === 0 ? <s>{row.right}</s> : row.right}
                    {row.right % 3 === 0 ? (
                      <span className="door-tag muted">×3</span>
                    ) : null}
                  </td>
                  <td>
                    {row.sacked ? (
                      <span className="door-tag">—</span>
                    ) : (
                      <>
                        <strong>{row.door}</strong>
                        {row.sink ? (
                          <span className="door-tag sink">2-power</span>
                        ) : null}
                      </>
                    )}
                  </td>
                  <td>
                    {row.sacked
                      ? "3 is never hired"
                      : row.sink
                        ? "only powers of 2 — a sink"
                        : row.doorFactors.join(" · ")}
                  </td>
                </tr>
              ))}
            </tbody>
          </table>
        </div>
        <p className="hint">
          Every odd prime sits between two even numbers. One neighbour is always
          a multiple of 3; the other is the 3-free door.
        </p>
      </section>

      <section className="hire-beat">
        <h2>First questions</h2>
        <p>
          Can a door be made from <strong>2 alone</strong>? Yes — that is a
          sink. Look at 5 → 4 and 7 → 8 in the table. Can it be 2 and 5 but not
          3? Yes — that is a longer walk or a fork.{" "}
          <Link to="/basins">Basins</Link> draws those drains; <Link to="/islands">Islands</Link> shows the last join; <Link to="/corridor">Corridor</Link> holds the thin M₃₁ rail; <Link to="/microscope">Microscope</Link> / <Link to="/certificates">Certificates</Link> cover the record sink and owner-floor receipts; <Link to="/hire-lab">Hire rate</Link> and <Link to="/hire-spectrum">Spectrum</Link> measure growth once doors open.
        </p>
      </section>

      <section className="hire-beat">
        <h2>Door</h2>
        <p>
          For <em>p</em> ≠ 3, the standing door is the even neighbour free of 3.
          The other neighbour is always divisible by 6.
        </p>
      </section>

      <section className="hire-beat">
        <h2>Hire set</h2>
        <p>
          Seed <em>S</em> with 2. Walk odd primes and pull in the odd prime
          factors of each door. Those names join <em>S</em>. Three never joins.
        </p>
      </section>

      <section className="hire-beat">
        <h2>Gold edges</h2>
        <p>
          A gold arc <em>p</em> → <em>q</em> means <em>q</em> divides the door
          of <em>p</em>. The hire-sun Laplacian <em>H</em> forgets direction:
          spokes to 2 plus those gold chords.
        </p>
      </section>

      <section className="hire-beat">
        <h2>Basins</h2>
        <p>
          Most primes drain toward power-of-two sinks. Forks are the early joins
          that braid those basins together.
        </p>
        <figure className="figure-block">
          <img
            src="/figures/hire/basins.png"
            alt="Basins: Fermat sinks, Mersenne sinks, and the first join"
          />
          <figcaption className="figure-caption">
            Fermat sinks at 2<sup>k</sup>+1, Mersenne at 2<sup>k</sup>−1.{" "}
            <Link className="beat-link" to="/basins">
              Full-page forks →
            </Link>
          </figcaption>
        </figure>
      </section>


      <section className="hire-beat">
        <h2>Where next</h2>
        <p>
          <Link className="beat-link" to="/basins">Basins →</Link>{" "}
          drain lattice and forks.{" "}
          <Link className="beat-link" to="/islands">Islands →</Link>{" "}
          last island at <em>X</em>
          <sup>*</sup>.{" "}
          <Link className="beat-link" to="/corridor">Corridor →</Link>{" "}
          thin M₃₁ certificates.{" "}
          <Link className="beat-link" to="/hire-spectrum">Spectrum →</Link>{" "}
          Hire-sun recipes and lab dials.{" "}
          <Link className="beat-link" to="/hire-lab">Hire rate →</Link>{" "}
          H(X) table through 2·10<sup>10</sup>.
        </p>
      </section>
    </main>
  );
}
