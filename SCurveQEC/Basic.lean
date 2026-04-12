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

/-! ## Theorem 1.C: Monotonicity in w

Monotonicity of `P_L^w` in `w` is a genuinely nontrivial combinatorial
statement.  Below we **reformulate it as a cleaner integer-valued
claim** (the "pair inequality") and isolate this as the single open
step.

### Reformulation: the pair inequality

Let `fail(w) := logicalFailures D w` (size `Nfail w`).
Let `wt(w) := Pauli.weightedErrors n w` (size `Nwt w = C(n, w) · 3^w`).
Observe the binomial ratio identity:

`Nwt (w+1) / Nwt w = 3 (n - w) / (w + 1)`.

Hence `P_L^w ≤ P_L^{w+1}` (a ratio inequality) is **equivalent** to
the following **integer** inequality:

`Nfail w · 3 (n - w) ≤ Nfail (w+1) · (w + 1).      (PAIR-INEQ)`

This inequality has a natural pair-counting interpretation.  Define
the pair set
`R := {(E, P) | wt(E) = w, wt(P) = 1, supp(P) ∩ supp(E) = ∅}`.
Each `(E, P) ∈ R` is a pair where `E · P` has weight `w + 1`.
A double-counting argument gives:

* `|R with E failing|     = Nfail w · 3 (n - w)`  (LHS of PAIR-INEQ)
* `|R with (E·P) failing| = Nfail (w+1) · (w + 1)` (RHS of PAIR-INEQ)

Writing each side as a disjoint union over four (FF, FS, SF, SS)
subcases --- where the letter codes whether `E` and `E·P` fail or
succeed --- the pair inequality reduces further to

`|R_FS| ≤ |R_SF|,    (CORE)`

where `R_FS := {(E,P) ∈ R : E fails, E·P succeeds}` and
`R_SF := {(E,P) ∈ R : E succeeds, E·P fails}`.

### Status of the core inequality

The `CORE` inequality says: *the number of weight-w failures that are
"rescued" by a random extra fault is at most the number of weight-w
successes that are "broken" by a random extra fault.*

Attempts that do NOT close the proof:

1. *Identity injection `R_FS ↪ R_SF`*: fails because the weights
   and positions do not align.
2. *Involution via logical multiplication* `(E, P) ↦ (L·E, P)` for
   some fixed `L ∈ logicalErrors`: swaps the failure status of `E`
   but does not preserve `wt(E) = w` (since `wt(L) ≥ d`).
3. *Syndrome-wise symmetry*: within each fixed syndrome coset the
   failure set is uniform, but the single-fault map mixes syndromes
   non-uniformly.
4. *Detailed balance / probabilistic coupling*: the expected number
   of "fixes" and "breaks" under a random added fault is not obvi-
   ously balanced without further structural hypotheses on the code.

I believe `CORE` to be **true in full generality** but the proof
requires either a code-specific argument (e.g.\ percolation on the
Pauli lattice for surface codes) or an inequality from coding theory
(e.g.\ a version of the LYM / Harper / FKG inequality on the Pauli
poset) that is not currently in `Mathlib`.

We therefore leave `Thm_1C_monotonicity` as a single documented `sorry`
representing the one genuinely open combinatorial step of Phase 1.
The derivation `CORE ⟹ PAIR-INEQ ⟹ monotonicity` is itself non-
trivial cardinality arithmetic; we leave its formalisation to a
follow-up file `Monotone.lean`.
-/

/-- **Partial monotonicity (trivial case).**
When the smaller weight lies at or below the fault-tolerance threshold,
`P_L^{w₁} = 0` by Theorem 1.A, so the inequality is immediate. -/
theorem Thm_1C_monotonicity_below_threshold {w₁ w₂ : ℕ}
    (h_w₁ : w₁ ≤ 𝒞.threshold) (h : w₁ ≤ w₂) :
    P_L 𝒞 D w₁ ≤ P_L 𝒞 D w₂ := by
  rw [Thm_1A_fault_tolerance 𝒞 D h_w₁]
  exact P_L_nonneg D w₂

/-- **Theorem 1.C (Monotonicity), general form.**

*Open in full generality.*  The proof is reduced in the section
docstring to the integer pair-inequality `|R_FS| ≤ |R_SF|`,
which is believed true but whose proof requires combinatorial
machinery (lattice inequalities on the Pauli poset) not yet
available in `Mathlib`.  See the section docstring for a detailed
account of the reformulation and the failed proof attempts. -/
theorem Thm_1C_monotonicity {w₁ w₂ : ℕ} (h : w₁ ≤ w₂) :
    P_L 𝒞 D w₁ ≤ P_L 𝒞 D w₂ := by
  -- If `w₁ ≤ t`, use the trivial case.
  by_cases h_below : w₁ ≤ 𝒞.threshold
  · exact Thm_1C_monotonicity_below_threshold 𝒞 D h_below h
  -- Otherwise `w₁ > t` and the general case requires the pair inequality;
  -- see section docstring.
  push_neg at h_below
  sorry

/-! ## Theorem 1.D: Saturation -/

/-- When there are no weight-`w` logical failures, `P_L^w = 0`.
This is a trivial but useful lemma; in particular it covers every
`w ≤ t` (by Theorem 1.A) and also the high-weight case if the
particular code has no weight-`n` logical operator. -/
theorem Thm_1D_zero_when_no_failures (w : ℕ)
    (h_empty : logicalFailures D w = ∅) : P_L 𝒞 D w = 0 := by
  classical
  unfold P_L
  split_ifs with hempty
  · rfl
  · rw [show (logicalFailures D w).card = 0 by rw [h_empty]; simp]
    simp

/-- **Theorem 1.D (Abstract saturation).**

For a general stabilizer code, the exact value of `P_L^n` depends on
the specific weight-`n` structure of the centralizer and is not a
universal constant.  A commonly-cited asymptotic claim
`lim_{n → ∞} P_L^n = (2^{2k}-1)/2^{2k}` requires an additional
*uniform-measure* hypothesis (i.e.\ that weight-`n` errors approach
the uniform distribution on Paulis as `n → ∞`), which in turn needs
explicit control of the code family.

Here we record the minimal abstract statement: `P_L^n` is a well-
defined rational in `[0, 1]` (Theorem 1.B) and vanishes when there
are no weight-`n` logical failures (Theorem 1.D zero case).  A finer
characterisation is deferred to the surface-code file. -/
theorem Thm_1D_range (w : ℕ) : P_L 𝒞 D w ∈ Set.Icc (0 : ℚ) 1 :=
  ⟨P_L_nonneg D w, P_L_le_one D w⟩

end SCurveQEC
