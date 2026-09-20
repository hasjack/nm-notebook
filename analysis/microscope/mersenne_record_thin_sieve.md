# Thin sieve: first-owner multiplier floor for record Mersenne door

- Door: \(q = M_e = 2^e - 1\) with **\(e = 136279841\)** (GIMPS record / 52nd known Mersenne prime, \(41\,024\,320\) digits).
- Papers frozen: draft-only; no Lean edits; no git push of hire notes.
- Does **not** hunt \(\tau(q)\); never materializes \(q\) or \(41\)M-digit candidates.

## Hire door facts used

- \(e\) odd \(\Rightarrow\) \(q \equiv 1 \pmod{3}\) \(\Rightarrow\) \(m_0(q) = q+1 = 2^e\) (pure \(2\)-power sink).
- First-owner candidates: primes \(p = kq \pm 1\) with admissible \(k \equiv 2\) or \(4 \pmod{6}\) (so \(m_0(p)=kq\) is \(3\)-free):
  - \(k \equiv 2 \pmod{6}\) → class A: \(p = kq - 1\)
  - \(k \equiv 4 \pmod{6}\) → class B: \(p = kq + 1\)
- Elementary floor: \(\tau(q) \ge 2q-1\) \(\Rightarrow\) **\(K \ge 2\)**.

## Method

For each odd prime \(r \le R\):

1. \(q \bmod r = (2^e - 1) \bmod r\) via `pow(2,e,r)-1` (never build \(q\)).
2. Eliminate admissible \(k\) with \(k\cdot q \equiv \pm 1 \pmod{r}\) matching the class
   (i.e. candidate \(p = kq\pm 1 \equiv 0 \pmod{r}\)).
3. Equality \(kq\pm 1 = r\) is impossible for \(k\ge 2\) and \(r \le R \ll q\); no false kill.

**Certified floor:** walk admissible \(k = 2,4,8,10,\ldots\); every \(k\) hit by some \(r\le R\) is composite as an owner candidate.  
\(K_{\mathrm{cert}}\) = first admissible \(k\) that survives all \(r\le R\).  
Hence the first owner has multiplier \(k \ge K_{\mathrm{cert}}\), i.e. \(\tau(q) \ge K_{\mathrm{cert}}\cdot q - 1\) (class A) or \(K_{\mathrm{cert}}\cdot q + 1\) (class B) in size.

Sanity: on \(e=31\) with \(R=10^5\), recovers \(K_{\mathrm{cert}}=46\), matching the known first owner of \(M_{31}\).

## Results (record \(e\))

| \(R\) | \(K_{\mathrm{cert}}\) | ruled \(k < K_{\mathrm{cert}}\) | wall (box) |
|---:|---:|---:|---:|
| \(10^6\) | **28** | 9 | \(0.17\,\mathrm{s}\) |
| \(10^7\) | **28** | 9 | \(1.17\,\mathrm{s}\) |
| \(10^8\) | **28** | 9 | \(10.7\,\mathrm{s}\) |

Extended probe on the stubborn survivor \(k=28\) (class B, candidate \(p=28q+1\)) only:

| probe \(R\) | hit? | wall |
|---:|:---:|---:|
| \(10^9\) | no | \(\approx 10\,\mathrm{s}\) (C) |
| \(5\cdot 10^9\) | no | \(\approx 47\,\mathrm{s}\) (C) |

### Kill table (admissible \(k\le 50\), \(R=10^7\))

| \(k\) | class | first factor \(r\le 10^7\) |
|---:|:---:|---:|
| 2 | A | 375373 |
| 4 | B | 5 |
| 8 | A | 13 |
| 10 | B | 11 |
| 14 | A | 1181 |
| 16 | B | 7 |
| 20 | A | 79 |
| 22 | B | 103 |
| 26 | A | 5 |
| **28** | **B** | **survives** |
| 32 | A | 31 |
| 34 | B | 5 |
| 38 | A | 47 |
| 40 | B | 41 |
| 44 | A | 29 |
| 46 | B | 234131 |
| 50 | A | 757 |

## Certified claim

\[
\boxed{K_{\mathrm{cert}} = 28}
\]
at sieve bound \(R = 10^7\) (and still at \(R=10^8\)). Every admissible multiplier \(k\in\{2,4,8,10,14,16,20,22,26\}\) yields a composite \(kq\pm 1\) with an explicit prime factor \(\le R\). Therefore the first owner of \(q\) has multiplier \(\ge 28\).

Climb vs elementary floor: \(K: 2 \to 28\) (\(14\times\)).

## Caveats

1. **Plateau at 28:** \(28q+1\) has **no** prime factor \(\le 5\cdot 10^9\). A pure small-prime thin sieve cannot raise \(K_{\mathrm{cert}}\) further without finding a larger factor (or a different attack on \(28\cdot 2^{e}-27\)). This does **not** claim that \(k=28\) is an owner — only that it is \(5\cdot 10^9\)-factor-free.
2. Survivors of the sieve may still be composite (semiprime with huge factors). \(K_{\mathrm{cert}}\) is a **lower** bound only.
3. No search for \(\tau(q)\); no primality test on \(41\)M-digit candidates.

## Artifacts

- `drafts/mersenne_record_thin_sieve.py` — main sieve (`--e`, `--R`, `--kill-table`, `--validate-m31`)
- `drafts/mersenne_record_thin_sieve.md` — this note
- `drafts/mersenne_record_thin_sieve_k28_probe.c` — optional C probe for the \(k=28\) candidate
- Logs: `mersenne_record_thin_sieve_R1e6.log`, `_R1e7.log`, `_R1e8.log`, `_k28_R5e9.log`

## Paste-ready room takeaway

**Record \(M_{136279841}\) thin sieve: certified \(K_{\mathrm{cert}}=28\) at \(R=10^7\) (wall \(\approx 1.2\,\mathrm{s}\)); climb \(2\to 28\). Caveat: \(k=28\) (\(28q+1\)) has no factor \(\le 5\cdot 10^9\), so the thin sieve plateaus there — not a \(\tau\) hunt.**
