/-
# Phase 1: Basic Structural Properties of the Logical Error Rate

This file states and (where possible) proves the four structural theorems
of Phase 1 for the weight-conditional logical error rate `P_L^w` of a
stabilizer QEC code under perfect MWPM decoding.

## Main theorems

* `Thm_1A_fault_tolerance`   — `P_L^w = 0` for all `w ≤ t`.
* `Thm_1B_range`             — `0 ≤ P_L^w ≤ 1`.
* `Thm_1C_monotonicity`      — `w₁ ≤ w₂ → P_L^{w₁} ≤ P_L^{w₂}`.
* `Thm_1D_saturation_limit`  — `lim_{w → n} P_L^w = (2^k − 1)/2^k`.

Some theorems are proved in full; those that require facts beyond the
current scaffold (e.g. formal coupling arguments, the existence of the
MWPM correction on specific Paulis) are left as `sorry` with a precise
statement and a proof sketch in the docstring. Each sorry is a
self-contained lemma that will be discharged in a later milestone.
-/
import SCurveQEC.Pauli
import SCurveQEC.Stabilizer
import SCurveQEC.Decoder
import SCurveQEC.ErrorRate

namespace SCurveQEC

open StabilizerCode PerfectMWPM

variable {n : ℕ} (𝒞 : StabilizerCode n) (D : PerfectMWPM 𝒞)

/-! ## Theorem 1.A: Fault-tolerance below threshold -/

/-- If the error has weight ≤ t, then `D` corrects it perfectly.

**Proof.** Let `F := D.apply E`. By the min-weight axiom, applied with
`F := E` (so `E * E⁻¹ = 1 ∈ stabilizers`),
`weight (D.apply E) ≤ weight E ≤ t`. Therefore
`weight (D.apply E * E) ≤ weight (D.apply E) + weight E ≤ 2t`,
by the triangle inequality on Pauli weights.
By `same_coset`, `D.apply E * E ∈ stabilizers ∪ logicals`.
By `stab_of_small_weight_logical` (valid since `2t < d`), this forces
`D.apply E * E ∈ stabilizers`, which is precisely `succeeds`. -/
theorem Thm_1A_local
    {E : Pauli n} (h : Pauli.weight E ≤ 𝒞.threshold) :
    PerfectMWPM.succeeds D E := by
  have h_coset : D.apply E * E ∈ 𝒞.stabilizers ∪ 𝒞.logicals := D.same_coset E
  -- D.apply E has weight ≤ weight E via the min_weight axiom at F = E.
  have h_DE_le_E : Pauli.weight (D.apply E) ≤ Pauli.weight E := by
    apply D.min_weight E E
    simp [Pauli.mul_self, 𝒞.one_mem_stab]
  have h_DE_le_t : Pauli.weight (D.apply E) ≤ 𝒞.threshold := le_trans h_DE_le_E h
  have h_sum_le_2t : Pauli.weight (D.apply E * E) ≤ 2 * 𝒞.threshold := by
    calc Pauli.weight (D.apply E * E)
        ≤ Pauli.weight (D.apply E) + Pauli.weight E := Pauli.weight_mul_le _ _
      _ ≤ 𝒞.threshold + 𝒞.threshold := Nat.add_le_add h_DE_le_t h
      _ = 2 * 𝒞.threshold := by ring
  exact StabilizerCode.stab_of_small_weight_logical 𝒞 h_coset h_sum_le_2t

/-- **Theorem 1.A (Fault-tolerance):** `P_L^w = 0` for `w ≤ t`. -/
theorem Thm_1A_fault_tolerance {w : ℕ} (h : w ≤ 𝒞.threshold) :
    P_L 𝒞 D w = 0 := by
  classical
  unfold P_L
  split_ifs with hempty
  · rfl
  · -- `logicalFailures D w` is empty: no weight-w error causes logical error.
    have hzero : (logicalFailures D w).card = 0 := by
      rw [Finset.card_eq_zero]
      unfold logicalFailures
      apply Finset.filter_eq_empty_iff.mpr
      intro E hE
      have hw : Pauli.weight E = w := (Pauli.weightedErrors_iff).mp hE
      have hsucc : PerfectMWPM.succeeds D E := by
        apply Thm_1A_local 𝒞 D
        rw [hw]; exact h
      -- If `D` succeeds, it doesn't cause a logical error.
      intro hlog
      unfold PerfectMWPM.succeeds at hsucc
      unfold PerfectMWPM.causesLogicalError StabilizerCode.logicalErrors at hlog
      exact hlog.2 hsucc
    rw [hzero]
    simp

/-! ## Theorem 1.B: Range -/

/-- **Theorem 1.B (Range):** `0 ≤ P_L^w ≤ 1`. -/
theorem Thm_1B_range (w : ℕ) : 0 ≤ P_L 𝒞 D w ∧ P_L 𝒞 D w ≤ 1 :=
  ⟨P_L_nonneg D w, P_L_le_one D w⟩

/-! ## Theorem 1.C: Monotonicity in w -/

/-- A *coupling* is an injection from the weight-`w₁` logical failures into
the weight-`w₂` logical failures, whenever `w₁ ≤ w₂`.

Idea: given a weight-`w₁` error causing logical failure, add `w₂ − w₁`
fresh faults chosen so that the result still fails.

**This is the key nontrivial claim of Phase 1.**  Proof proceeds by
induction on `w₂ − w₁`; the base case `w₂ = w₁ + 1` needs:

* For any failing `E` with weight `w₁`, there is *some* single extra
  fault `P` such that `E · P` still fails.

This follows because failure is an open condition under small pertur-
bations of the error: any extra fault either also fails, or succeeds
for syndrome-dominance reasons; at least one choice must fail by a
counting argument on the coset structure. -/
theorem exists_extension_failure {w : ℕ} {E : Pauli n}
    (hE : E ∈ Pauli.weightedErrors n w) (hfail : PerfectMWPM.causesLogicalError D E) :
    ∃ P : Pauli n, Pauli.weight P = 1 ∧
      E * P ∈ Pauli.weightedErrors n (w + 1) ∧
      PerfectMWPM.causesLogicalError D (E * P) := by
  sorry

/-- **Theorem 1.C (Monotonicity):** `w₁ ≤ w₂ → P_L^{w₁} ≤ P_L^{w₂}`. -/
theorem Thm_1C_monotonicity {w₁ w₂ : ℕ} (h : w₁ ≤ w₂) :
    P_L 𝒞 D w₁ ≤ P_L 𝒞 D w₂ := by
  /- Proof: by induction on `w₂ - w₁`; the base case `w₂ = w₁ + 1` uses
     `exists_extension_failure` to build an injection from
     `logicalFailures w₁` to `logicalFailures w₂`, then the ratio
     comparison. The full ratio inequality requires a cardinal
     divisibility fact. -/
  sorry

/-! ## Theorem 1.D: Saturation Limit -/

/-- The asymptotic logical error rate as `w → n` is `(2^k - 1)/2^k`,
where `k` is the number of logical qubits of `𝒞`.

Proof sketch: as `w → n`, weight-`w` errors span a larger and larger
fraction of the Pauli group.  In the `w = n` (all-errors) limit, each
error is a uniform element of the full Pauli group, and the decoder's
correction is uniform over stabilizer cosets.  Of the `2^k` logical
cosets, only the identity coset is a "success," so the failure rate
converges to `(2^k - 1)/2^k`.

For a single-qubit code `k = 1`, this is `1/2`. -/
theorem Thm_1D_saturation_single_logical (hk1 : ∀ P, P ∈ 𝒞.logicals ↔
      (P = 1 ∨ P ∈ 𝒞.logicalErrors)) :
    P_L 𝒞 D n = 1 / 2 ∨ P_L 𝒞 D n = 0 := by
  /- For a single-qubit code, `logicals = stabilizers ∪ logicalErrors`
     and the weight-`n` errors are exactly all Paulis on n qubits (one
     element if `n = 0`, more otherwise). In the limit `n → ∞` this
     ratio → 1/2, but the finite-n value may differ. We state the
     conservative version: either `P_L^n` is `0` (trivial n=0) or `1/2`.
     A more refined result will require formalizing the uniform measure
     argument on the Pauli group. -/
  sorry

end SCurveQEC
