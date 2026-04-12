/-
# Stabilizer Codes

A stabilizer code is specified abstractly by:
* a number of physical qubits `n`,
* a subset `stabilizers ⊆ Pauli n` that is an abelian subgroup (its elements
  mutually commute and it contains `1`),
* the logical Pauli group `logicals`, the centralizer of the stabilizer modulo
  the stabilizer itself.

For our results we only need the *distance*:
`d(𝒞) = min { weight P | P ∈ logicals \ stabilizers }`,
and the *fault-tolerance threshold* `t = ⌊(d-1)/2⌋`.

We keep the definition minimal and abstract: the decoder and error-rate
theorems below do not refer to stabilizers individually, only to the
distance and to which Paulis are "logical" (cause a logical error).
-/
import SCurveQEC.Pauli
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic

namespace SCurveQEC

/-- A stabilizer QEC code on `n` physical qubits, given abstractly by:

* `stabilizers` — a set of Paulis (closed under multiplication, commuting,
  containing `1`);
* `logicals`    — the centralizer of `stabilizers`, so that
  `logicals \ stabilizers` is the set of Paulis that, if undetected,
  cause a logical error.

The minimal data we need for our theorems are axioms:
* stabilizers contain `1`;
* `logicals` is non-empty beyond stabilizers (`distance ≥ 1`);
* distance is well-defined.
-/
structure StabilizerCode (n : ℕ) : Type where
  stabilizers : Set (Pauli n)
  logicals    : Set (Pauli n)
  /-- Stabilizers contain identity. -/
  one_mem_stab : (1 : Pauli n) ∈ stabilizers
  /-- Stabilizers are contained in logicals (trivial logicals). -/
  stab_subset_log : stabilizers ⊆ logicals
  /-- There exists at least one non-stabilizer logical (distance is finite). -/
  exists_nontrivial_logical : ∃ P, P ∈ logicals ∧ P ∉ stabilizers

namespace StabilizerCode

variable {n : ℕ} (𝒞 : StabilizerCode n)

/-- The set of "logical-error" Paulis: logicals that are not stabilizers. -/
def logicalErrors : Set (Pauli n) :=
  𝒞.logicals \ 𝒞.stabilizers

/-- A Pauli `E` causes a logical error when composed with the decoder's
correction `C` iff `C * E` is a non-trivial logical. -/
def isLogicalError (P : Pauli n) : Prop :=
  P ∈ 𝒞.logicalErrors

/-- Code distance: the minimum weight of a non-trivial logical operator. -/
noncomputable def distance : ℕ :=
  sInf ((Pauli.weight '' 𝒞.logicalErrors) : Set ℕ)

/-- Fault-tolerance threshold: `⌊(d-1)/2⌋`. -/
noncomputable def threshold : ℕ := (𝒞.distance - 1) / 2

/-- For brevity. -/
noncomputable def t : ℕ := 𝒞.threshold

/-- Basic: distance is at least 1 (there is a non-stabilizer logical with
non-zero weight; if it has weight 0 it would be `1`, which is a stabilizer). -/
theorem distance_pos : 0 < 𝒞.distance := by
  sorry

/-- The fundamental decoding property: if `wt E ≤ t`, then `E` lies in the
stabilizer coset (i.e. `E` is either a stabilizer or within distance
`t` of one). This is what makes the code able to correct. -/
theorem corrects_up_to_threshold {E : Pauli n} (h : Pauli.weight E ≤ 𝒞.threshold) :
    E ∈ 𝒞.stabilizers ∨ E ∉ 𝒞.logicals := by
  sorry

end StabilizerCode

end SCurveQEC
