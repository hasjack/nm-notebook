# Exponent 5 descent audit

This note follows the checked Lean statements in `Five.lean`. It is a guide to
the closure question: after one descent step, does the smaller auxiliary
solution satisfy every assumption needed to run the same construction again?

The final theorem is
`Hire.GoldenBridge.fermatLastTheoremFive_via_descent :
FermatLastTheoremFor 5`.

## Primitive entry branches

`no_coprime_integer_fifth_solution` reduces a primitive integer solution
`a^5 + b^5 = c^5` to the case where `5 | a + b`, using
`five_dvd_some_of_sum_fifth_powers`, `five_dvd_sum_of_fifth_solution`, and
`fifth_solution_coprime_output_right`.

`no_primitive_fifth_solution_five_dvd_sum` then splits on the parity of
`a + b`.

- Even sum, odd inputs:
  `no_primitive_fifth_solution_odd_inputs_five_dvd_sum` centers the inputs at
  `a + b = 10*r`, `a - b = 2*q`. The normalized equation is produced by
  `centered_fifth_powers_identity` and closed by
  `no_normalized_fifth_solution`.
- Odd sum:
  `no_primitive_fifth_solution_odd_sum_five_dvd_sum` centers the inputs at
  `a + b = 5*r`, `a - b = q`. The normalized equation is produced by
  `odd_output_normalized_equation` and closed by
  `no_odd_output_normalized_fifth_solution`.

## `FifthNormSolution`

### Entry

The even-sum branch reaches `no_normalized_fifth_solution` with:

- `r != 0`
- `IsCoprime q r`
- `not (5 : Z) | q`
- `Odd (q + r)`
- `(50*r) * (q^4 + 50*r^2*q^2 + 125*r^4) = z^5`

`fifthNormSolution_of_normalized_factors` constructs a
`FifthNormSolution` with:

- `A = q^2 + 25*r^2`
- `B = 10*r^2`
- `B = 400*t^5`
- `A^2 - 5*B^2 = v^5`

The entry conditions are supplied by:

- factor coprimality: `normalized_fifth_factors_coprime`
- norm-coordinate coprimality: `normalized_norm_pair_coprime`
- odd first coordinate: `normalized_norm_first_odd`
- 5-free first coordinate used inside the coprimality proof:
  `normalized_norm_first_five_free`

### Preservation

`fifthNormSolution_descent` turns any `S : FifthNormSolution` into
`S' : FifthNormSolution`. It first extracts root coordinates through:

- `fifthNormSolution_integer_root`
- `sqrtFive_root_coefficient_equations`
- `sqrtFive_root_coordinates_coprime`
- `sqrtFive_root_coordinate_parity`
- `sqrtFive_root_first_five_free`
- `sqrtFive_root_second_positive`

The actual construction is in `fifthNormSolution_descent_of_root`. The new
solution has:

- `A' = c^2 + 5*d^2`
- `B' = 2*d^2`
- `t' = 2*w^2`
- `B' = 400*(t')^5`
- `A'^2 - 5*(B')^2 = v^5`

Each field of the new structure is justified by a named lemma:

- coprime: `descent_new_pair_coprime`
- odd first coordinate: `descent_new_first_odd`
- even second coordinate: `descent_new_second_even`
- coefficient shape: `descent_coefficient_shape`
- norm equation: `descentNormFactor_identity`
- fifth-power allocation: `descent_fifth_power_allocation`
- allocation prerequisites: `descentNormFactor_coprime_coordinate`,
  `descentNormFactor_odd`, `five_not_dvd_descentNormFactor`, and
  `descentNormFactor_coprime_eighty`

### Decrease

`fifthNormSolution_descent_of_root` proves `S'.B < S.B`. The explicit
inequality is:

`2*d^2 < 5*d*descentNormFactor c d`

under `0 < d`, established by `descent_coefficient_strictly_decreases`.

`no_fifthNormSolution` converts this integer inequality into
`S'.B.natAbs < S.B.natAbs` using positivity of both second coordinates, and
then applies strong induction on `B.natAbs`.

### Closure

The closure loop is:

1. `fifthNormSolution_descent` produces another `FifthNormSolution`.
2. The new solution has smaller `B.natAbs`.
3. `no_fifthNormSolution` rules out the original solution by strong induction.

This answers the closure question for this branch: every preserved field is
part of the `FifthNormSolution` structure, so the same descent theorem applies
again to `S'`.

## `HalfFifthNormSolution`

### Entry

The odd-sum branch reaches `no_odd_output_normalized_fifth_solution` with:

- `r != 0`
- `IsCoprime q r`
- `not (5 : Z) | q`
- `Odd q`
- `Odd r`
- `(25*r) * (q^4 + 50*r^2*q^2 + 125*r^4) = 16*z^5`

`odd_output_initial_norm_coordinates` constructs initial norm coordinates:

- `Odd P`
- `2*P = q^2 + 25*r^2`
- `q^4 + 50*r^2*q^2 + 125*r^4 = 16*H`
- `P^2 - 5*(5*r^2)^2 = 4*H`

`no_odd_output_normalized_fifth_solution` then uses:

- factor coprimality: `odd_output_initial_factors_coprime`
- fifth-power allocation: `twenty_five_mul_fifth_power_allocation`
- norm-coordinate coprimality: `odd_output_initial_norm_pair_coprime`

to build a `HalfFifthNormSolution` with:

- `Q = 5*r^2`
- `Q = 25*u^5`
- `P^2 - 5*Q^2 = 4*v^5`

The primitive branch supplies its entry hypotheses through
`odd_output_coordinates_properties`.

### Preservation

`halfFifthNormSolution_descent` turns any
`S : HalfFifthNormSolution` into `S' : HalfFifthNormSolution`. It first extracts
root data using `halfFifthNormSolution_root_properties`, which supplies:

- `IsCoprime t s`
- `Odd t`
- `Odd s`
- `not (5 : Z) | t`
- `0 < s`
- `16*S.P = t*(t^4 + 50*t^2*s^2 + 125*s^4)`
- `16*S.Q = 5*s*descentNormFactor t s`

The new coordinates come from `half_descent_new_norm_coordinates`:

- `Odd P`
- `2*P = t^2 + 5*s^2`
- `descentNormFactor t s = 16*H`
- `P^2 - 5*(s^2)^2 = 4*H`

Each field of the new `HalfFifthNormSolution` is justified by:

- coprime: `half_descent_new_pair_coprime`
- odd first coordinate: `half_descent_new_norm_coordinates`
- odd second coordinate: the square of the odd root coordinate `s`
- coefficient shape: `half_descent_fifth_power_allocation`
- norm equation: `half_descent_new_norm_coordinates`, after rewriting with the
  allocated fifth power
- 5-free and coprimality prerequisites:
  `halfFifthNormSolution_five_not_dvd_first`,
  `descentNormFactor_coprime_coordinate`, and
  `five_not_dvd_descentNormFactor`

### Decrease

`halfFifthNormSolution_descent` proves `S'.Q < S.Q`. The explicit inequality is:

`s^2 < S.Q`

under `0 < s` and
`16*S.Q = 5*s*descentNormFactor t s`, established by
`half_norm_second_coordinate_decreases`.

`no_halfFifthNormSolution` converts this into
`S'.Q.natAbs < S.Q.natAbs` using positivity of both second coordinates, then
applies strong induction on `Q.natAbs`.

### Closure

The closure loop is:

1. `halfFifthNormSolution_descent` produces another
   `HalfFifthNormSolution`.
2. The new solution has smaller `Q.natAbs`.
3. `no_halfFifthNormSolution` rules out the original solution by strong
   induction.

Again, the preservation target is exactly the structure type, so every
condition needed for the next descent step is present on the smaller solution.
