/-
# Perfect MWPM Decoder

A *perfect minimum-weight* decoder maps each "syndrome" (stabilizer coset
representative) to the minimum-weight Pauli consistent with it.  For our
proofs we do not need an algorithm; we only need:

1. existence of a function `D : Pauli n → Pauli n` picking a representative
   of each stabilizer coset,
2. the *minimum-weight property*: for any `E`, `weight (D E) ≤ weight E`,
3. the *coset consistency*: `D E` is in the same stabilizer coset as `E`.

A "perfect MWPM" decoder is simply such a function that, additionally,
always picks a stabilizer-coset representative — equivalently, it satisfies
`D E * E ∈ stabilizers ∪ logicals`.

This file axiomatizes the decoder as an opaque structure. Any "MWPM-like"
decoder that corrects up to distance `t` is a valid instantiation.
-/
import SCurveQEC.Stabilizer
import Mathlib.Order.Basic

namespace SCurveQEC

open StabilizerCode

/-- A *perfect MWPM decoder* for a stabilizer code.

`apply E` returns the decoder's guess of the injected Pauli (given only
the syndrome of `E`).  We encode the decoder abstractly as a function
on `Pauli n`; the axioms below enforce that it depends on `E` only through
its syndrome. -/
structure PerfectMWPM {n : ℕ} (𝒞 : StabilizerCode n) : Type where
  apply : Pauli n → Pauli n
  /-- Minimum-weight property: the decoded Pauli has weight ≤ any
  stabilizer-coset representative. -/
  min_weight : ∀ (E F : Pauli n),
    (F * E⁻¹) ∈ 𝒞.stabilizers → Pauli.weight (apply E) ≤ Pauli.weight F
  /-- Coset consistency: `apply E` is in `E`'s stabilizer coset. -/
  same_coset : ∀ (E : Pauli n), (apply E * E) ∈ 𝒞.stabilizers ∪ 𝒞.logicals
  /-- Syndrome-determinism: if `E₁, E₂` have the same syndrome (i.e.
  `E₁ * E₂⁻¹` is a stabilizer), then `apply E₁ = apply E₂`.

  We do not require formal syndrome types here; instead we state the
  consequence directly: two errors in the same logical coset that differ
  only by a stabilizer produce the same decoder output. -/
  syndrome_deterministic : ∀ (E₁ E₂ : Pauli n),
    (E₁ * E₂⁻¹) ∈ 𝒞.stabilizers → apply E₁ = apply E₂

namespace PerfectMWPM

variable {n : ℕ} {𝒞 : StabilizerCode n} (D : PerfectMWPM 𝒞)

/-- The corrected Pauli: decoder output composed with actual error. -/
def correctionResult (E : Pauli n) : Pauli n := D.apply E * E

/-- Decoder succeeds on `E` iff the correction result is a stabilizer
(the residual is trivial). -/
def succeeds (E : Pauli n) : Prop :=
  correctionResult D E ∈ 𝒞.stabilizers

/-- Decoder produces a logical error on `E` iff the correction result
is a non-trivial logical. -/
def causesLogicalError (E : Pauli n) : Prop :=
  correctionResult D E ∈ 𝒞.logicalErrors

/-- Logical failure and success are complementary on the coset union. -/
theorem succ_or_logical_error (E : Pauli n) :
    succeeds D E ∨ causesLogicalError D E := by
  unfold succeeds causesLogicalError correctionResult
  have h := D.same_coset E
  rcases h with hs | hl
  · exact Or.inl hs
  · by_cases hs : D.apply E * E ∈ 𝒞.stabilizers
    · exact Or.inl hs
    · exact Or.inr ⟨hl, hs⟩

end PerfectMWPM

end SCurveQEC
