/-
# Monotonicity for the rotated surface code (circuit level)

This file formalises the **circuit-level compiled rotated surface
code** as an abstract `StabilizerCode`, and states the surface-code-
specific monotonicity theorem on the rising portion of its weight-
conditional logical error rate.

## Circuit-level vs data-level

The theorems in this file are about the **circuit-level compiled
code**, not the data-only code.  The compiled code is the
`StabilizerCode` obtained from the full compiled memory-experiment
circuit, including:
* `d^2` data qubits, `d^2 - 1` ancilla qubits,
* `r` rounds of syndrome extraction (resets, CNOTs, measurements),
* all hook-error propagation paths.

The compiled circuit has `n = C(d, r) ≈ 8 d^2 r` fault locations in
its Pauli frame.  This is the model for which our empirical S-curves
(cf.\ the companion paper) were measured.

*Data-only* surface codes (9 qubits at `d = 3`) are a different
`StabilizerCode` instance; small-code counterexamples to universal
monotonicity found in the data-only setting (e.g.\ in
`experiments/counterexample_search.py` and
`experiments/surface_d3_monotonicity.py`) do **not** transfer here.

## Abstract structure: `IsLatticeCode`

Rather than constructing the compiled rotated surface code
explicitly (a substantial indexing task), we work with a general
structural property `IsLatticeCode 𝒞 ℓ_stab ℓ_log` capturing:

* stabilizer weight bounded above by `ℓ_stab`;
* logical-error weight bounded below by `ℓ_log`.

Compiled surface-code circuits satisfy this with `ℓ_log = d` (the
circuit-level distance, possibly reduced by hook errors).

## Main theorem (stated, proof pending)

Theorem `Thm_surface_rising_monotone`: for a code satisfying
`IsLatticeCode`, `P_L^w` is non-decreasing on the weight range
`[0, n - 2 ℓ_log]`.

This range is **code-intrinsic** (no auxiliary definitions) and
matches the empirical rising portion of the S-curve.

The proof is a research task, involving a coupling / FKG-type
inequality on the space-time detector graph of the compiled
circuit.  We leave it as a `sorry` with explicit documentation.
-/
import SCurveQEC.Pauli
import SCurveQEC.Stabilizer
import SCurveQEC.Decoder
import SCurveQEC.ErrorRate

namespace SCurveQEC

/-! ## Lattice codes: a general structural property -/

/-- **Lattice code property.**

A stabilizer code `𝒞` on `n` qubits is a *lattice code* with
parameters `(ℓ_stab, ℓ_log)` if:

* Every stabilizer generator has Pauli weight at most `ℓ_stab`.
* Every minimum-weight logical operator has Pauli weight at
  least `ℓ_log`.

Compiled circuit-level surface codes, toric codes, and color codes
are lattice codes (with `ℓ_log` equal to the circuit-level
distance, which may be less than the code distance due to hook
errors).  We state the property abstractly so results apply to any
such code. -/
structure IsLatticeCode {n : ℕ} (𝒞 : StabilizerCode n)
    (ℓ_stab ℓ_log : ℕ) : Prop where
  stab_weight_bd  : ∀ S ∈ 𝒞.stabilizers, Pauli.weight S ≤ ℓ_stab
  log_weight_lb   : ∀ L ∈ 𝒞.logicalErrors, ℓ_log ≤ Pauli.weight L

/-! ## Circuit-level rotated surface code

The rotated surface code at distance `d` with `r` rounds of syndrome
extraction, compiled to a memory experiment, is a stabilizer code on
`n = C(d, r)` circuit-level fault locations.  The explicit
construction involves lattice indexing, plaquette enumeration,
boundary conditions, and derivation from the compiled circuit;
we leave this as a future task.

For odd `d ≥ 3` and `r ≥ d`, the compiled code has:
* Circuit-level distance `≤ d` (can be strictly less due to hook
  errors).
* Thousands of stabilizer generators (one per detector) at weight
  `O(d)` each.
* One logical qubit.

We work with the abstract `IsLatticeCode` property below; an
explicit construction

```lean
-- noncomputable def rotatedSurfaceCircuit (d r : ℕ) (hd : 3 ≤ d) (hr : d ≤ r) :
--     StabilizerCode (C d r) := sorry
```

is a natural follow-up.
-/


/-! ## Main theorem: monotonicity on the rising portion -/

/-- **Circuit-level surface-code rising monotonicity (conjecture).**

For a stabilizer code satisfying `IsLatticeCode 𝒞 ℓ_stab ℓ_log`
(which holds for the compiled rotated surface code at sufficient
distance, as well as for toric and color codes) and any perfect
MWPM decoder `D`, the weight-conditional logical error rate is
monotonically non-decreasing on the interval `[0, n - 2 ℓ_log]`:

`∀ w₁ ≤ w₂ ≤ n - 2 ℓ_log, P_L^{w₁}(𝒞, D) ≤ P_L^{w₂}(𝒞, D).`

**Why the weight bound `n - 2 ℓ_log`?**
This bound conservatively captures the rising portion of the
S-curve.  Beyond `w = n - 2 ℓ_log` the weight-`w` Paulis are close
to the saturation regime, where small oscillations around the
saturation value become possible.  The bound uses only
code-intrinsic quantities (`n` and `ℓ_log`).

**Proof roadmap.**
The main tool is a coupling / FKG-type inequality on the space-
time detector graph of the compiled surface code.  Under the
lattice symmetry, `R_FS^w ↪ R_SF^w` (pair-injection) for every
`w < n - 2 ℓ_log`.  The precise combinatorial construction is a
research-level problem; formalising it requires additional
structural hypotheses on the Pauli poset.

**Status.**  We state this theorem cleanly, with only code-intrinsic
quantities, and leave the proof as `sorry` with the above roadmap.
A first, achievable refinement is to construct the compiled
rotated surface code explicitly and verify `IsLatticeCode` for
small `(d, r)`. -/
theorem Thm_surface_rising_monotone
    {n ℓ_stab ℓ_log : ℕ}
    (𝒞 : StabilizerCode n) (D : PerfectMWPM 𝒞)
    (_hlattice : IsLatticeCode 𝒞 ℓ_stab ℓ_log)
    {w₁ w₂ : ℕ} (h : w₁ ≤ w₂) (h_bd : w₂ + 2 * ℓ_log ≤ n) :
    P_L 𝒞 D w₁ ≤ P_L 𝒞 D w₂ := by
  sorry

end SCurveQEC
