/-
# The pair-inequality reduction

This file provides the **general reduction** from an integer pair-
cardinality inequality to the rational monotonicity of `P_L^w`:

If at every `w`,
`|fail(w)| · |wt(w+1)| ≤ |fail(w+1)| · |wt(w)|`,
then `P_L^w ≤ P_L^{w+1}`.

This is a purely arithmetic reduction (no QEC content beyond the
definitions).  The *hard* combinatorial task --- proving the pair
inequality itself for a specific code family --- is isolated as a
hypothesis that can be verified per code.

## Main definitions and theorems

* `PairCardIneq 𝒞 D w`: the integer inequality at step `w → w+1`.
* `monotone_step_via_cards`: the rational-arithmetic lemma.
* `monotone_step_of_PairCardIneq`: the step version for `P_L`.
* `monotone_of_PairCardIneq`: the chained version for all `w₁ ≤ w₂`.

-/
import SCurveQEC.Pauli
import SCurveQEC.Stabilizer
import SCurveQEC.Decoder
import SCurveQEC.ErrorRate

namespace SCurveQEC

open StabilizerCode PerfectMWPM

variable {n : ℕ}

/-! ## The abstract pair-cardinality inequality -/

/-- The integer pair-cardinality inequality at step `w → w+1`.
`|fail(w)| · |wt(w+1)| ≤ |fail(w+1)| · |wt(w)|`. -/
def PairCardIneq (𝒞 : StabilizerCode n) (D : PerfectMWPM 𝒞) (w : ℕ) : Prop :=
  (logicalFailures D w).card * (Pauli.weightedErrors n (w + 1)).card ≤
  (logicalFailures D (w + 1)).card * (Pauli.weightedErrors n w).card

/-! ## Rational-arithmetic reduction -/

/-- **Rational-arithmetic lemma.**
From the integer pair inequality between cardinalities, the ratio
inequality on rationals follows. -/
theorem monotone_step_via_cards
    {Nf_w Nf_w1 Nwt_w Nwt_w1 : ℕ}
    (h_pos_w  : 0 < Nwt_w)
    (h_pos_w1 : 0 < Nwt_w1)
    (h_card   : Nf_w * Nwt_w1 ≤ Nf_w1 * Nwt_w) :
    (Nf_w : ℚ) / (Nwt_w : ℚ) ≤ (Nf_w1 : ℚ) / (Nwt_w1 : ℚ) := by
  have hw : (0 : ℚ) < (Nwt_w : ℚ) := by exact_mod_cast h_pos_w
  have hw1 : (0 : ℚ) < (Nwt_w1 : ℚ) := by exact_mod_cast h_pos_w1
  rw [div_le_div_iff₀ hw hw1]
  exact_mod_cast h_card

/-! ## Main step reduction -/

/-- **Step reduction.**
If both weights have non-empty weight-sets, and the integer pair
inequality holds at step `w → w+1`, then `P_L^w ≤ P_L^{w+1}`. -/
theorem monotone_step_of_PairCardIneq
    {𝒞 : StabilizerCode n} {D : PerfectMWPM 𝒞} {w : ℕ}
    (h_w_pos  : 0 < (Pauli.weightedErrors n w).card)
    (h_w1_pos : 0 < (Pauli.weightedErrors n (w + 1)).card)
    (h_pair   : PairCardIneq 𝒞 D w) :
    P_L 𝒞 D w ≤ P_L 𝒞 D (w + 1) := by
  classical
  unfold P_L
  have hw_ne  : (Pauli.weightedErrors n w).card ≠ 0 := Nat.pos_iff_ne_zero.mp h_w_pos
  have hw1_ne : (Pauli.weightedErrors n (w + 1)).card ≠ 0 := Nat.pos_iff_ne_zero.mp h_w1_pos
  simp only [hw_ne, hw1_ne]
  exact monotone_step_via_cards h_w_pos h_w1_pos h_pair

/-! ## Chained (general) monotonicity -/

/-- **General monotonicity.**
If the pair inequality holds at every step in `[w₁, w₂)`, and all
weight-sets in this range are non-empty, then `P_L^{w₁} ≤ P_L^{w₂}`. -/
theorem monotone_of_PairCardIneq
    {𝒞 : StabilizerCode n} {D : PerfectMWPM 𝒞}
    {w₁ w₂ : ℕ}
    (h : w₁ ≤ w₂)
    (h_pos : ∀ w, w₁ ≤ w → w ≤ w₂ → 0 < (Pauli.weightedErrors n w).card)
    (h_pair : ∀ w, w₁ ≤ w → w < w₂ → PairCardIneq 𝒞 D w) :
    P_L 𝒞 D w₁ ≤ P_L 𝒞 D w₂ := by
  induction h with
  | refl => rfl
  | @step w h_le ih =>
    have h_pos' : ∀ u, w₁ ≤ u → u ≤ w → 0 < (Pauli.weightedErrors n u).card :=
      fun u hu1 hu2 => h_pos u hu1 (le_trans hu2 (Nat.le_succ w))
    have h_pair' : ∀ u, w₁ ≤ u → u < w → PairCardIneq 𝒞 D u :=
      fun u hu1 hu2 => h_pair u hu1 (lt_trans hu2 (Nat.lt_succ_self w))
    have ih' : P_L 𝒞 D w₁ ≤ P_L 𝒞 D w := ih h_pos' h_pair'
    have h_w_pos  : 0 < (Pauli.weightedErrors n w).card :=
      h_pos w h_le (Nat.le_succ w)
    have h_w1_pos : 0 < (Pauli.weightedErrors n (w + 1)).card :=
      h_pos (w + 1) (le_trans h_le (Nat.le_succ w)) (le_refl _)
    have h_step_pair : PairCardIneq 𝒞 D w :=
      h_pair w h_le (Nat.lt_succ_self w)
    have h_step : P_L 𝒞 D w ≤ P_L 𝒞 D (w + 1) :=
      monotone_step_of_PairCardIneq h_w_pos h_w1_pos h_step_pair
    exact le_trans ih' h_step

end SCurveQEC
