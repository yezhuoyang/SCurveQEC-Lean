# SCurveQEC-Lean

A Lean 4 formalization of first-principles derivations for the S-curve model of
weight-conditional logical error rates in quantum error-correcting codes.

## Target Theorem (ultimate goal)

For a stabilizer code `𝒞` with `C` fault locations, distance `d`, and threshold
`t = ⌊(d-1)/2⌋`, decoded by a perfect MWPM decoder under the SID noise model,
there exist parameters `θ = (μ, α, β)` such that the weight-conditional logical
error rate `P_L^w(𝒞)` is approximated by the S-curve `f_t[θ](w)` with an
explicit error bound.

## Phased approach

We prove this in three phases of increasing difficulty.

- **Phase 1** — Structural properties: `P_L^w = 0` for `w ≤ t`, monotonicity,
  saturation, basic bounds.  *(All provable.)*
- **Phase 2** — Analytic properties: strict monotonicity, discrete log-concavity,
  existence of a unique inflection point.  *(Mostly provable; may specialize to
  surface code for the hardest step.)*
- **Phase 3** — S-curve approximation theorem.  *(Aspirational; may require
  refining the specific functional form.)*

## Companion paper

A LaTeX manuscript accompanies this formalization.  See the `paper/` directory.

## Building

```bash
lake build
```

Requires Lean 4 (see `lean-toolchain`) and mathlib4.

## Structure

```
SCurveQEC/
  Pauli.lean         -- Pauli group, weights
  Stabilizer.lean    -- Stabilizer codes, distance
  Decoder.lean       -- Perfect MWPM (black-box)
  ErrorRate.lean     -- P_L^w definition
  Basic.lean         -- Phase 1 theorems (1.A – 1.E)
```

## Status

- [ ] Phase 1: Structural properties
  - [ ] M1.1: Pauli
  - [ ] M1.2: Stabilizer
  - [ ] M1.3: Decoder
  - [ ] M1.4: ErrorRate
  - [ ] M1.5: Theorems 1.A – 1.E
- [ ] Phase 2: Analytic properties
- [ ] Phase 3: S-curve approximation
