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

/-- Any Pauli in `logicalErrors` has weight at least the distance.
This is essentially the definition of `distance` as an infimum. -/
theorem distance_le_weight_of_logicalError {E : Pauli n} (h : E ∈ 𝒞.logicalErrors) :
    𝒞.distance ≤ Pauli.weight E := by
  unfold distance
  have hmem : Pauli.weight E ∈ (Pauli.weight '' 𝒞.logicalErrors) :=
    Set.mem_image_of_mem _ h
  exact Nat.sInf_le hmem

/-- A Pauli with weight 0 is the identity. -/
theorem eq_one_of_weight_zero {P : Pauli n} (h : Pauli.weight P = 0) : P = 1 := by
  funext i
  unfold Pauli.weight at h
  have hsupp : Pauli.support P = ∅ := Finset.card_eq_zero.mp h
  unfold Pauli.support at hsupp
  have hi : i ∉ (Finset.univ.filter fun i => P i ≠ SinglePauli.I) := by
    rw [hsupp]; simp
  simp [Finset.mem_filter] at hi
  simp [hi]

/-- Basic: distance is at least 1. If distance were 0, the infimum would be
attained by some logical error of weight 0 (which must be `1`), but `1` is
a stabilizer — contradiction. -/
theorem distance_pos : 0 < 𝒞.distance := by
  unfold distance
  obtain ⟨P, hP_log, hP_nstab⟩ := 𝒞.exists_nontrivial_logical
  have hP_err : P ∈ 𝒞.logicalErrors := ⟨hP_log, hP_nstab⟩
  have hne : (Pauli.weight '' 𝒞.logicalErrors).Nonempty :=
    ⟨Pauli.weight P, Set.mem_image_of_mem _ hP_err⟩
  -- sInf of a nonempty subset of ℕ is in the set.
  have hmem := Nat.sInf_mem hne
  obtain ⟨Q, hQ_err, hQ_wt⟩ := hmem
  -- Suppose sInf = 0 for contradiction: then weight Q = 0, so Q = 1 ∈ stabilizers.
  rw [← hQ_wt]
  by_contra hzero
  push_neg at hzero
  have hwq : Pauli.weight Q = 0 := Nat.le_zero.mp hzero
  have hQ1 : Q = 1 := eq_one_of_weight_zero hwq
  rw [hQ1] at hQ_err
  exact hQ_err.2 𝒞.one_mem_stab

/-- The threshold is strictly less than the distance: `2t + 1 ≤ d`. -/
theorem two_threshold_lt_distance : 2 * 𝒞.threshold < 𝒞.distance := by
  unfold threshold
  have h := 𝒞.distance_pos
  omega

/-- The key fault-tolerance lemma: if a Pauli has weight ≤ 2 * threshold,
and it is in `stabilizers ∪ logicals`, then it is in `stabilizers`. -/
theorem stab_of_small_weight_logical {P : Pauli n}
    (h_log_or_stab : P ∈ 𝒞.stabilizers ∪ 𝒞.logicals)
    (h_wt : Pauli.weight P ≤ 2 * 𝒞.threshold) :
    P ∈ 𝒞.stabilizers := by
  rcases h_log_or_stab with hs | hl
  · exact hs
  · by_contra hns
    have h_err : P ∈ 𝒞.logicalErrors := ⟨hl, hns⟩
    have h_d_le : 𝒞.distance ≤ Pauli.weight P :=
      distance_le_weight_of_logicalError 𝒞 h_err
    have h_2t_lt : 2 * 𝒞.threshold < 𝒞.distance := 𝒞.two_threshold_lt_distance
    omega

end StabilizerCode

end SCurveQEC
