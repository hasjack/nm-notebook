# Top-ten owner-floor certificates \(K_{\mathrm{cert}}(q;B)\)

- Source list: PrimePages / t5k.org top ten (late 2026).
- Sieve bound: **\(B = 10^7\)** (primary). Optional confirms at \(B=10^8\) for ranks 2, 6, 9 (and spot-checks).
- Papers frozen. Hunt closed. No paper edits. No \(N_{28}\) PRP.
- Method identical to `mersenne_record_thin_sieve.py` (Mersenne record \(K_{\mathrm{cert}}=28\)).
- Never materializes \(q\); uses modular recipes for \(q \bmod r\).
- Sanity: \(M_{31}\) → \(K_{\mathrm{cert}}=46\) (15 kills at \(B=10^5\)), matching the known first owner.

## Hire door rules

- \(m_0(p) = p+1\) if \(p\equiv 1\pmod{3}\), else \(p-1\) (`Hire/Doors.lean`).
- First-owner candidates: primes \(p = kq\pm 1\) with admissible \(k\equiv 2\) or \(4\pmod{6}\) (so \(m_0(p)=kq\) is 3-free):
  - **class A:** \(p = kq - 1\) (needs \(p\equiv 1\pmod{3}\), i.e. \(kq\equiv 2\pmod{3}\))
  - **class B:** \(p = kq + 1\) (needs \(p\equiv 2\pmod{3}\), i.e. \(kq\equiv 1\pmod{3}\))
- **Class ↔ \(k\) depends on \(q \bmod 3\):**
  - \(q\equiv 1\pmod{3}\): \(k\equiv 2\to A\), \(k\equiv 4\to B\) (Mersenne / GU case)
  - \(q\equiv 2\pmod{3}\): \(k\equiv 2\to B\), \(k\equiv 4\to A\) (**flip**; without it, \(r=3\) falsely kills every admissible \(k\))
- For each odd prime \(r\le B\): eliminate admissible \(k\) with candidate \(\equiv 0\pmod{r}\).
- \(K_{\mathrm{cert}}\) = first admissible \(k\) that survives all \(r\le B\).
- Equality \(kq\pm 1 = r\) is impossible for \(k\ge 2\) and \(r\le B\ll q\); no false kills.

## Modular \(q \bmod r\) recipes

| form | recipe |
|---|---|
| Mersenne \(2^e-1\) | `(pow(2,e,r)-1) % r` |
| GFN \(b^{2^n}+1\) | `(pow(b,1<<n,r)+1) % r` |
| GU \(b^{2^n}-b^{2^{n-1}}+1\) | `(pow(b,1<<n,r)-pow(b,1<<(n-1),r)+1) % r` |

## Summary table (\(B=10^7\))

| rank | form | digits | \(q\bmod 3\) | \(K_{\mathrm{cert}}\) | #kills | wall | m0 note |
|---:|---|---:|---:|---:|---:|---:|---|
| 1 | `2^136279841-1` (Mersenne) | 41,024,320 | 1 | **28** | 9 | 1.17s (reused) | \(m_0=q+1=2^{136279841}\) (pure 2-power sink) |
| 2 | `2^82589933-1` (Mersenne) | 24,862,048 | 1 | **80** | 26 | 0.97s | \(m_0=q+1=2^{82589933}\) (pure 2-power sink) |
| 3 | `2^77232917-1` (Mersenne) | 23,249,425 | 1 | **14** | 4 | 0.93s | \(m_0=q+1=2^{77232917}\) (pure 2-power sink) |
| 4 | `2^74207281-1` (Mersenne) | 22,338,618 | 1 | **2** | 0 | 0.90s | \(m_0=q+1=2^{74207281}\) (pure 2-power sink) |
| 5 | `2^57885161-1` (Mersenne) | 17,425,170 | 1 | **14** | 4 | 0.91s | \(m_0=q+1=2^{57885161}\) (pure 2-power sink) |
| 6 | `2524190^2097152+1` (GFN) | 13,426,224 | 2 | **4** | 1 | 0.73s | \(m_0=q-1\) (not a 2-power sink) |
| 7 | `2^43112609-1` (Mersenne) | 12,978,189 | 1 | **10** | 3 | 0.90s | \(m_0=q+1=2^{43112609}\) (pure 2-power sink) |
| 8 | `2^42643801-1` (Mersenne) | 12,837,064 | 1 | **2** | 0 | 0.89s | \(m_0=q+1=2^{42643801}\) (pure 2-power sink) |
| 9 | `516693^2097152-516693^1048576+1` (GU) | 11,981,518 | 1 | **44** | 14 | 1.06s | \(m_0=q+1\) (not a 2-power sink) |
| 10 | `465859^2097152-465859^1048576+1` (GU) | 11,887,192 | 1 | **92** | 30 | 1.09s | \(m_0=q+1\) (not a 2-power sink) |

### Optional confirms at \(B=10^8\)

| rank | \(K\) at \(10^7\) | \(K\) at \(10^8\) | note |
|---:|---:|---:|---|
| 2 | 80 | **80** (same) | wall ≈ 9.3s |
| 6 | 4 | **4** (same) | wall ≈ 7.0s |
| 9 | 44 | **46** (raised) | \(k=44\) killed by \(r=43884101\); \(k=46\) survives |
| 10 | 92 | 92 (spot-check) | \(k=92\) has no factor \(\le 10^8\) |

Primary certificate remains \(B=10^7\). Rank 9's confirm shows the thin sieve can still climb with a larger bound.

## Door / sink ping

Sink (\(m_0\) pure \(2\)-power) occurs **only** for odd-exponent Mersennes (\(m_0(q)=q+1=2^e\)).

Non-Mersenne doors:

- rank 6 GFN: \(q\equiv 2\pmod{3}\) → \(m_0=q-1=2524190^{2097152}\) (high composite power; **not** a sink). Class ↔ \(k\) **flipped**.
- rank 9 GU: \(q\equiv 1\pmod{3}\) → \(m_0=q+1\) (not a 2-power sink).
- rank 10 GU: \(q\equiv 1\pmod{3}\) → \(m_0=q+1\) (not a 2-power sink).

## Kill tables (admissible \(k < K_{\mathrm{cert}}\), first factor \(r\le 10^7\))

### rank 1: `2^136279841-1` — \(K_{\mathrm{cert}}=28\), 9 kills (reused)

| \(k\) | class | first \(r\le 10^7\) |
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

### rank 2: `2^82589933-1` — \(K_{\mathrm{cert}}=80\), 26 kills

| \(k\) | class | first \(r\) |
|---:|:---:|---:|
| 2 | A | 37463 |
| 4 | B | 5 |
| 8 | A | 11 |
| 10 | B | 79 |
| 14 | A | 53 |
| 16 | B | 7 |
| 20 | A | 3359 |
| 22 | B | 31 |
| 26 | A | 5 |
| 28 | B | 56473 |
| 32 | A | 3203 |
| 34 | B | 5 |
| 38 | A | 29 |
| 40 | B | 17 |
| 44 | A | 59 |
| 46 | B | 157 |
| 50 | A | 41 |
| 52 | B | 89 |
| 56 | A | 5 |
| 58 | B | 7 |
| 62 | A | 17 |
| 64 | B | 5 |
| 68 | A | 7 |
| 70 | B | 13 |
| 74 | A | 11 |
| 76 | B | 113 |
| **80** | **A** | **survives** |

### rank 3: `2^77232917-1` — \(K_{\mathrm{cert}}=14\), 4 kills

| \(k\) | class | first \(r\) |
|---:|:---:|---:|
| 2 | A | 11 |
| 4 | B | 5 |
| 8 | A | 13 |
| 10 | B | 31 |
| **14** | **A** | **survives** |

### rank 4: `2^74207281-1` — \(K_{\mathrm{cert}}=2\), 0 kills

| \(k\) | class | first \(r\) |
|---:|:---:|---:|
| **2** | **A** | **survives** (elementary floor; no factor \(\le 10^7\)) |

### rank 5: `2^57885161-1` — \(K_{\mathrm{cert}}=14\), 4 kills

| \(k\) | class | first \(r\) |
|---:|:---:|---:|
| 2 | A | 193 |
| 4 | B | 5 |
| 8 | A | 13 |
| 10 | B | 11 |
| **14** | **A** | **survives** |

### rank 6: `2524190^2097152+1` (GFN, \(q\equiv 2\)) — \(K_{\mathrm{cert}}=4\), 1 kill

| \(k\) | class | first \(r\) |
|---:|:---:|---:|
| 2 | B | 7 |
| **4** | **A** | **survives** |

### rank 7: `2^43112609-1` — \(K_{\mathrm{cert}}=10\), 3 kills

| \(k\) | class | first \(r\) |
|---:|:---:|---:|
| 2 | A | 59 |
| 4 | B | 5 |
| 8 | A | 13 |
| **10** | **B** | **survives** |

### rank 8: `2^42643801-1` — \(K_{\mathrm{cert}}=2\), 0 kills

| \(k\) | class | first \(r\) |
|---:|:---:|---:|
| **2** | **A** | **survives** (elementary floor; no factor \(\le 10^7\)) |

### rank 9: `516693^2097152-516693^1048576+1` (GU) — \(K_{\mathrm{cert}}=44\), 14 kills

| \(k\) | class | first \(r\) |
|---:|:---:|---:|
| 2 | A | 37 |
| 4 | B | 5 |
| 8 | A | 23 |
| 10 | B | 11 |
| 14 | A | 13 |
| 16 | B | 7 |
| 20 | A | 1009 |
| 22 | B | 227 |
| 26 | A | 5 |
| 28 | B | 29 |
| 32 | A | 41 |
| 34 | B | 5 |
| 38 | A | 29017 |
| 40 | B | 31 |
| **44** | **A** | **survives at \(B=10^7\)**; killed by \(43884101\) at \(B=10^8\) |
| 46 | B | survives at \(B=10^8\) → confirm \(K_{\mathrm{cert}}(q;10^8)=46\) |

### rank 10: `465859^2097152-465859^1048576+1` (GU) — \(K_{\mathrm{cert}}=92\), 30 kills

| \(k\) | class | first \(r\) |
|---:|:---:|---:|
| 2 | A | 1249 |
| 4 | B | 5 |
| 8 | A | 11 |
| 10 | B | 421 |
| 14 | A | 83 |
| 16 | B | 7 |
| 20 | A | 277 |
| 22 | B | 61 |
| 26 | A | 5 |
| 28 | B | 137 |
| 32 | A | 37 |
| 34 | B | 5 |
| 38 | A | 523 |
| 40 | B | 251 |
| 44 | A | 13 |
| 46 | B | 3559 |
| 50 | A | 151 |
| 52 | B | 631 |
| 56 | A | 5 |
| 58 | B | 7 |
| 62 | A | 3919 |
| 64 | B | 5 |
| 68 | A | 7 |
| 70 | B | 253543 |
| 74 | A | 11 |
| 76 | B | 31 |
| 80 | A | 23827 |
| 82 | B | 773 |
| 86 | A | 5 |
| 88 | B | 1217 |
| **92** | **A** | **survives** |

## Caveats

1. \(K_{\mathrm{cert}}\) is a **lower** bound on the first-owner multiplier. Survivors may still be composite (large factors).
2. Ranks 4 and 8 sit at the elementary floor \(K=2\): thin sieve finds no factor \(\le 10^7\) of \(2q-1\).
3. No search for \(\tau(q)\); no primality tests on multi-million-digit candidates.
4. Rank 1 reused from the frozen Mersenne-record catalog (\(K_{\mathrm{cert}}=28\) at \(B=10^7\)).
5. Class ↔ \(k\) flip for \(q\equiv 2\pmod{3}\) is required (rank 6); the Mersenne-only script hard-coded the \(q\equiv 1\) assignment.

## Artifacts

- `drafts/top10_owner_floor_catalog.py` — script (`--B`, `--validate-m31`, `--confirm-B`, `--force-rank1`)
- `drafts/top10_owner_floor_catalog.md` — this note
- `drafts/top10_owner_floor_catalog.csv` — machine-readable rows + kill tables
- Sync copies: `analysis/microscope/`, `nm-notebook/analysis/microscope/`

## Paste-ready room takeaway

**Top-10 thin-sieve owner floors at \(B=10^7\):** #1 \(K=28\) (reused), #2 \(K=80\), #3 \(K=14\), #4 \(K=2\), #5 \(K=14\), #6 GFN \(K=4\) (\(q\equiv 2\), class flip), #7 \(K=10\), #8 \(K=2\), #9 GU \(K=44\) (→46 at \(B=10^8\)), #10 GU \(K=92\). Sink only on odd-exponent Mersennes. Kill receipts for every admissible \(k<K_{\mathrm{cert}}\). Papers frozen; hunt closed.
