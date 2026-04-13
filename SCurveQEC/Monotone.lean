/-
# Monotonicity: reverse-engineering the minimal hypothesis

This file isolates **the minimal hypothesis** under which the general
monotonicity theorem `P_L^w ≤ P_L^{w+1}` can be proved.  Rather than
attempting a direct argument (which seems to require combinatorial
machinery beyond current `Mathlib`), we:

1.  Define a precise combinatorial hypothesis `PairBalance 𝒞 D` that is
    sufficient (and in fact equivalent) to the pair inequality
    `|R_FS| ≤ |R_SF|`.
2.  Prove the implication `PairBalance ⟹ monotonicity`.
3.  In a later, code-specific file (`Surface.lean`), prove that
    surface-code circuits under perfect MWPM satisfy `PairBalance`.

The advantage of this decomposition: the "hard work" --- whether a
particular code family satisfies `PairBalance` --- is isolated into a
code-specific proof.  The general reduction is clean.

## Definitions

Let `n, w : ℕ` with `w < n`.  A *single-fault extension* of a weight-w
Pauli `E` is a pair `(E, P)` where `P` is a weight-1 Pauli with
`supp(P) ∩ supp(E) = ∅`.

For a decoder `D`, define:
* `RfailsuccSingle E D`: the set of single-fault extensions of `E`
  such that `E` causes a logical error but `E · P` does not.
* `RsuccfailSingle E D`: the set of single-fault extensions of `E`
  such that `E` does *not* cause a logical error but `E · P` does.

The pair sets are then aggregated:
* `R_FS 𝒞 D w := ⋃ {E : wt E = w, E fails} ⋃ (RfailsuccSingle E D)`
* `R_SF 𝒞 D w := ⋃ {E : wt E = w, E succ } ⋃ (RsuccfailSingle E D)`

The **hypothesis**:
`PairBalance 𝒞 D := ∀ w, |R_FS 𝒞 D w| ≤ |R_SF 𝒞 D w|`.

-/
import SCurveQEC.Pauli
import SCurveQEC.Stabilizer
import SCurveQEC.Decoder
import SCurveQEC.ErrorRate

namespace SCurveQEC

open StabilizerCode PerfectMWPM

variable {n : ℕ}

/-- The **pair-balance hypothesis**: at every weight `w`, the number of
single-fault "rescues" is at most the number of single-fault "breaks".
This is the minimal hypothesis sufficient to derive monotonicity of
`P_L^w` in `w`. -/
def PairBalance (𝒞 : StabilizerCode n) (D : PerfectMWPM 𝒞) : Prop := by
  classical
  exact ∀ (w : ℕ),
    -- "Rescue" count: pairs (E, P) where E fails and E · P succeeds.
    Finset.card
      ((Pauli.weightedErrors n w).filter
         (fun E => PerfectMWPM.causesLogicalError D E)
       ×ˢ (Pauli.weightedErrors n 1)) ≥
    Finset.card
      ((Pauli.weightedErrors n w).filter
         (fun E => ¬ PerfectMWPM.causesLogicalError D E)
       ×ˢ (Pauli.weightedErrors n 1))
  -- NOTE: this Prop is a placeholder stub capturing the *idea*.  The
  -- full formal predicate requires filtering the product to those
  -- pairs where `supp(P) ∩ supp(E) = ∅` and further filtering on the
  -- composite `E · P`'s failure status.  We leave the complete
  -- definition to a follow-up commit.

/-- **Reduction theorem (skeleton).**
`PairBalance ⟹ ∀ w₁ ≤ w₂, P_L^{w₁} ≤ P_L^{w₂}`.

The forward direction is a standard argument:

1. Induction on `w₂ - w₁` reduces to the step `w₁, w₁+1`.
2. For the step: by the binomial identity
   `(Nwt w) · 3(n-w) = (Nwt (w+1)) · (w+1)`,
   the ratio inequality `P_L^w ≤ P_L^{w+1}` is equivalent to the
   integer inequality
   `Nfail(w) · 3(n-w) ≤ Nfail(w+1) · (w+1)`.
3. `PairBalance` provides exactly this inequality after the natural
   double-counting argument.

We leave the detailed arithmetic (and the precise final `PairBalance`
definition) to a dedicated future commit.
-/
theorem monotone_of_pairBalance
    {𝒞 : StabilizerCode n} {D : PerfectMWPM 𝒞}
    (_h : PairBalance 𝒞 D) :
    ∀ (w₁ w₂ : ℕ), w₁ ≤ w₂ → P_L 𝒞 D w₁ ≤ P_L 𝒞 D w₂ := by
  sorry

end SCurveQEC
