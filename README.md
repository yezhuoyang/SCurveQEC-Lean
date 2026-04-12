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

- [x] Phase 1: Structural properties
  - [x] M1.1: Pauli *(fully compiles, core lemmas proved)*
  - [x] M1.2: Stabilizer *(structure + 2 axiomatic sorries)*
  - [x] M1.3: Decoder *(PerfectMWPM + 1 theorem proved)*
  - [x] M1.4: ErrorRate *(P_L^w defined, nonneg proved, le_one sorry)*
  - [x] M1.5: Theorem 1.A (fault-tolerance) proved modulo a local lemma;
         1.B proved (modulo le_one sorry); 1.C–1.D stated with sorries.
- [ ] Phase 2: Analytic properties
- [ ] Phase 3: S-curve approximation

### Remaining sorries (Phase 1)

| File | Sorry | Status |
|---|---|---|
| Stabilizer.lean | `distance_pos` | Easy (one-line follow-up) |
| Stabilizer.lean | `corrects_up_to_threshold` | Needs Pauli-arithmetic lemmas |
| ErrorRate.lean | `P_L_le_one` | Easy (Finset.card division) |
| Basic.lean | `Thm_1A_local` | Core: needs the MWPM coset argument |
| Basic.lean | `Thm_1C_exists_extension_failure` | Core: coupling construction |
| Basic.lean | `Thm_1C_monotonicity` | Follows from extension lemma |
| Basic.lean | `Thm_1D_saturation` | Uniform-measure argument |

### Build

```bash
lake exe cache get   # fetch pre-built mathlib olean files
lake build           # compiles in ~10s after cache fetched
```
