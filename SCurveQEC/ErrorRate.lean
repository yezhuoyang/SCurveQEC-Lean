/-
# Weight-Conditional Logical Error Rate

This file defines `P_L^w`: the probability that a uniformly random weight-`w`
Pauli error causes the decoder to produce a logical error.

We use Finset-based counting (ratio of Finset cardinalities). We then prove
Phase 1 theorems about this ratio.

## Main definitions

* `weightedErrors 𝒞 w` — the Finset of weight-`w` Paulis on `n` qubits.
* `logicalFailures D w` — the Finset of weight-`w` Paulis on which the
  decoder `D` produces a logical error.
* `P_L 𝒞 D w` — the ratio `|logicalFailures| / |weightedErrors|`, as a rational.
-/
import SCurveQEC.Pauli
import SCurveQEC.Stabilizer
import SCurveQEC.Decoder
import Mathlib.Data.Rat.Defs

namespace SCurveQEC

open StabilizerCode

variable {n : ℕ}

namespace Pauli

/-- The set of all weight-`w` Paulis on `n` qubits. -/
noncomputable def weightedErrors (n w : ℕ) : Finset (Pauli n) :=
  Pauli.ofWeight n w

theorem weightedErrors_iff {n w : ℕ} {E : Pauli n} :
    E ∈ weightedErrors n w ↔ Pauli.weight E = w := by
  unfold weightedErrors
  exact mem_ofWeight

end Pauli

/-- The Finset of weight-`w` errors on which `D` produces a logical error.

We use `Classical.dec` to obtain a `DecidablePred` instance; since the
definition is `noncomputable` this is fine. -/
noncomputable def logicalFailures {n : ℕ} {𝒞 : StabilizerCode n}
    (D : PerfectMWPM 𝒞) (w : ℕ) : Finset (Pauli n) := by
  classical
  exact (Pauli.weightedErrors n w).filter
    (fun E => PerfectMWPM.causesLogicalError D E)

open Classical in
/-- The weight-conditional logical error rate `P_L^w`. -/
noncomputable def P_L {n : ℕ} (𝒞 : StabilizerCode n) (D : PerfectMWPM 𝒞)
    (w : ℕ) : ℚ :=
  if h : (Pauli.weightedErrors n w).card = 0 then 0
  else
    (logicalFailures D w).card / (Pauli.weightedErrors n w).card

theorem P_L_nonneg {𝒞 : StabilizerCode n} (D : PerfectMWPM 𝒞) (w : ℕ) :
    0 ≤ P_L 𝒞 D w := by
  unfold P_L
  split_ifs
  · rfl
  · positivity

theorem P_L_le_one {𝒞 : StabilizerCode n} (D : PerfectMWPM 𝒞) (w : ℕ) :
    P_L 𝒞 D w ≤ 1 := by
  classical
  unfold P_L
  split_ifs with h
  · norm_num
  · -- logicalFailures is a subset of weightedErrors, so its card is ≤.
    have hsub : logicalFailures D w ⊆ Pauli.weightedErrors n w := by
      intro E hE
      unfold logicalFailures at hE
      exact (Finset.mem_filter.mp hE).1
    have hcard : (logicalFailures D w).card ≤ (Pauli.weightedErrors n w).card :=
      Finset.card_le_card hsub
    rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero h)]
    exact_mod_cast hcard

end SCurveQEC
