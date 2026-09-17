# A discrete operator on the log-prime axis

Jack Pickett — redraft, 15 September 2026

This note keeps three things from an earlier experiment and drops the rest.

Kept:

1. The coordinate \(t_n = \log p_n\).
2. A self-adjoint discrete operator on that grid.
3. The working hypothesis that the primes and the Riemann spectrum share a clock.

Dropped: the composite-window “curvature” field copied from a gravity model; any affine map \(\gamma \approx a\lambda + b + c\log n\) presented as agreement; any claim that the eigenvalues *are* the non-trivial zeros.

## 1. Clock

The explicit formula reconstructs \(\psi(x)\) from waves \(x^{i\gamma} = e^{i\gamma\log x}\). The natural time for those waves is \(t = \log x\). The primes sit on that line as the point set

\[
t_n = \log p_n,\qquad n = 1,2,\dots,N.
\]

Gaps on this line are \(\log(p_{n+1}/p_n)\). Under the prime number theorem they have mean size \(\sim 1\), with fluctuations.

## 2. Operator

On a non-uniform grid \(t_0 < t_1 < \cdots < t_{N-1}\) let \(h_i = t_{i+1}-t_i\). The quadratic form

\[
Q(\psi) = \sum_{i=0}^{N-2}\frac{(\psi_{i+1}-\psi_i)^2}{h_i}
\]

is the discrete Dirichlet energy \(\int |\psi'|^2\,dt\). The associated symmetric tridiagonal matrix \(L\) has

\[
L_{i,i} = \frac{1}{h_{i-1}} + \frac{1}{h_i},\qquad
L_{i,i+1} = L_{i+1,i} = -\frac{1}{h_i}
\]

in the interior, with a large positive clamp on the two endpoints so the form stays positive-definite.

This \(L\) *is* the Hamiltonian. No extra potential. The geometry of how the primes sit on the log line is the whole input.

(If a potential is added later it should come from the prime density on this clock, e.g. a Weyl term built from \(e^{t}/t\), not from a window of composites and not from a gravity \(\kappa\).)

## 3. What to ask the spectrum

Compute the lowest \(K\) eigenvalues \(\lambda_1\le\cdots\le\lambda_K\) of \(L\).

Honest questions:

- How does \(\lambda_n\) grow with \(n\)? (Weyl: a 1D Laplacian on an interval of length \(T=\log p_N-\log 2\) has \(\lambda_n \sim (\pi n/T)^2\).)
- After unfolding to mean density one, what is the nearest-neighbour spacing distribution? Level repulsion or Poisson?
- How does that compare *qualitatively* with the unfolded \(\gamma_n\) (GUE) and with a Poisson control of the same length?

Not an honest question:

- After fitting \(\gamma_n \approx a\lambda_n + b\), how small is the relative error?

That last number measures the fit, not the operator.

## 4. What this is, and is not

This is a probe of the metric of \(\{\log p_n\}\). If the primes were equally spaced in \(t\), \(L\) would be the ordinary second-difference matrix and the spectrum would be a pure cosine chain. They are not equally spaced. The deviation of \(L\) from that chain *is* the arithmetic.

It is not Hilbert–Pólya. Hilbert–Pólya asks for a self-adjoint operator whose eigenvalues are the \(\gamma_n\) themselves. This \(L\) knows only the prime gaps. Those gaps already know the zeros through the explicit formula, so a resemblance in spacing statistics would not be independent evidence. It would be a consistency check that the log-prime point process is rigid in the way a chaotic 1D spectrum is rigid.

## 5. Relation to the discarded note

The discarded note used the same grid and the same discrete \(L\), then added a potential \(V = \beta\,k_n\) whose formula was the gravity-paper monomial \((\mathrm{local})^3\sqrt{\mathrm{density}}\) with “local” replaced by a composite window. That potential was not forced by \(\zeta\) or by the explicit formula. The subsequent affine map onto twenty zeros converted a sketch into a percentage. Both steps are removed here.

What remains is the clock, the operator, and a list of questions the spectrum is allowed to answer.
