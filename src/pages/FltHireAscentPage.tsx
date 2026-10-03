import { Link } from "react-router-dom";
import { useMemo, useState } from "react";

const ascent = [
  { from: 5, to: 11, door: 10 },
  { from: 11, to: 23, door: 22 },
  { from: 23, to: 47, door: 46 },
];

const selectablePrimes = [5, 7, 11, 13, 17, 19, 23, 29];

function isPrime(n: number): boolean {
  if (n < 2) return false;
  if (n % 2 === 0) return n === 2;
  for (let d = 3; d * d <= n; d += 2) {
    if (n % d === 0) return false;
  }
  return true;
}

function chi3(n: number): 1 | -1 {
  return n % 3 === 1 ? 1 : -1;
}

function m0(p: number): number {
  return p - chi3(p);
}

function ownersOf(q: number): { owner: number; door: number }[] {
  const owners: { owner: number; door: number }[] = [];
  for (let p = q + 2; p < 400 && owners.length < 6; p += 2) {
    if (p === 3 || !isPrime(p)) continue;
    const door = m0(p);
    if (door % q === 0) owners.push({ owner: p, door });
  }
  return owners;
}

export function FltHireAscentPage() {
  const [selectedPrime, setSelectedPrime] = useState(5);
  const owners = useMemo(() => ownersOf(selectedPrime), [selectedPrime]);

  return (
    <main className="page notes lab-note-page">
      <h1>Climbing the hire graph</h1>
      <p className="lede">
        The hire graph naturally runs downward from an owner prime to the
        primes in its door. Reversing that view gives an ascent: start with a
        prime, then climb to a larger owner whose door contains it.
      </p>

      <section>
        <h2>A small climb</h2>
        <p>
          One visible chain is <code>5 → 11 → 23 → 47</code>. The doors are
          exactly the previous doubled neighbours:
        </p>
        <div className="door-table-wrap">
          <table className="door-table">
            <thead>
              <tr>
                <th>Prime q</th>
                <th>Owner p</th>
                <th>Door m₀(p)</th>
              </tr>
            </thead>
            <tbody>
              {ascent.map((row) => (
                <tr key={row.to}>
                  <td>{row.from}</td>
                  <td>{row.to}</td>
                  <td>{row.door}</td>
                </tr>
              ))}
            </tbody>
          </table>
        </div>
      </section>

      <section>
        <h2>Small owners</h2>
        <p>
          Pick a prime and read upward: these are small owner primes whose
          3-free door contains the selected prime.
        </p>
        <div className="segmented" aria-label="Prime selector">
          {selectablePrimes.map((q) => (
            <button
              key={q}
              type="button"
              className={selectedPrime === q ? "on" : ""}
              onClick={() => setSelectedPrime(q)}
            >
              {q}
            </button>
          ))}
        </div>
        <div className="door-table-wrap">
          <table className="door-table">
            <thead>
              <tr>
                <th>q</th>
                <th>Owner p</th>
                <th>Door m₀(p)</th>
              </tr>
            </thead>
            <tbody>
              {owners.map((row) => (
                <tr key={row.owner}>
                  <td>{selectedPrime}</td>
                  <td>{row.owner}</td>
                  <td>{row.door}</td>
                </tr>
              ))}
            </tbody>
          </table>
        </div>
      </section>

      <section>
        <h2>The missing bridge</h2>
        <p>
          Prime ownership alone does not transport a Fermat solution, a descent,
          or a contradiction between exponents. To connect this climb to FLT, we
          would need a theorem saying what mathematical structure travels up the
          ladder.
        </p>
        <aside className="lab-note-caveats" aria-label="Research question">
          <p>
            Research question: is there a useful object attached to an exponent
            or number ring that follows hire ownership upward?
          </p>
        </aside>
      </section>

      <section>
        <h2>How to read it</h2>
        <p>
          Treat this as a lab bench, not a proof claim. The checked Fermat
          descents are on <Link to="/flt">FLT</Link>; this page records a
          possible direction for experiments after the proofs are easier to
          review.
        </p>
      </section>
    </main>
  );
}
