/-
Copyright (c) 2026. All rights reserved.

# Pauli Operators

This file defines Pauli operators on `n` qubits and their basic algebraic
structure. We use the standard Pauli enum representation; the global phase
factor (±1, ±i) is suppressed throughout, since logical error rates are
phase-independent.

## Main definitions

* `SinglePauli`      — the four single-qubit Paulis `{I, X, Y, Z}`.
* `SinglePauli.mul`  — multiplication table (up to global phase).
* `Pauli n`          — an n-qubit Pauli as a map `Fin n → SinglePauli`.
* `Pauli.weight P`   — number of positions where `P` acts non-trivially.
* `Pauli.mul P Q`    — pointwise multiplication.
* `Pauli.ofWeight n w` — the set of weight-`w` Paulis on `n` qubits.

-/
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace SCurveQEC

/-! ## Single-qubit Paulis -/

/-- A single-qubit Pauli operator, with global phase suppressed. -/
inductive SinglePauli : Type
  | I : SinglePauli
  | X : SinglePauli
  | Y : SinglePauli
  | Z : SinglePauli
  deriving DecidableEq, Inhabited, Repr

namespace SinglePauli

/-- All four Paulis. -/
def all : List SinglePauli := [I, X, Y, Z]

instance : Fintype SinglePauli where
  elems := ⟨{I, X, Y, Z}, by decide⟩
  complete := by intro P; cases P <;> decide

/-- Pauli multiplication (up to global phase). -/
def mul : SinglePauli → SinglePauli → SinglePauli
  | I, P => P
  | P, I => P
  | X, X => I
  | Y, Y => I
  | Z, Z => I
  | X, Y => Z
  | Y, X => Z
  | Y, Z => X
  | Z, Y => X
  | Z, X => Y
  | X, Z => Y

instance : Mul SinglePauli := ⟨mul⟩
instance : One SinglePauli := ⟨I⟩

@[simp] theorem one_def : (1 : SinglePauli) = I := rfl

@[simp] theorem mul_I (P : SinglePauli) : P * I = P := by cases P <;> rfl
@[simp] theorem I_mul (P : SinglePauli) : I * P = P := by cases P <;> rfl

@[simp] theorem mul_self (P : SinglePauli) : P * P = I := by cases P <;> rfl

/-- The weight of a single-qubit Pauli: 0 if `I`, else 1. -/
def weight : SinglePauli → ℕ
  | I => 0
  | _ => 1

@[simp] theorem weight_I : weight I = 0 := rfl
@[simp] theorem weight_X : weight X = 1 := rfl
@[simp] theorem weight_Y : weight Y = 1 := rfl
@[simp] theorem weight_Z : weight Z = 1 := rfl

/-- Whether two single-qubit Paulis commute. -/
def commutes : SinglePauli → SinglePauli → Bool
  | I, _ => true
  | _, I => true
  | P, Q => decide (P = Q)

end SinglePauli

/-! ## n-qubit Paulis -/

/-- An n-qubit Pauli operator (modulo global phase): a function from qubit
index to `SinglePauli`. -/
def Pauli (n : ℕ) : Type := Fin n → SinglePauli

namespace Pauli

variable {n : ℕ}

instance : DecidableEq (Pauli n) := fun _ _ => by
  unfold Pauli; infer_instance

instance : Fintype (Pauli n) := by unfold Pauli; infer_instance

instance : Inhabited (Pauli n) := ⟨fun _ => SinglePauli.I⟩

/-- The all-identity (unit) element. -/
def one : Pauli n := fun _ => SinglePauli.I

instance : One (Pauli n) := ⟨one⟩

@[simp] theorem one_apply (i : Fin n) : (1 : Pauli n) i = SinglePauli.I := rfl

/-- Pointwise multiplication of Paulis. -/
def mul (P Q : Pauli n) : Pauli n := fun i => P i * Q i

instance : Mul (Pauli n) := ⟨mul⟩

@[simp] theorem mul_apply (P Q : Pauli n) (i : Fin n) :
    (P * Q) i = P i * Q i := rfl

@[simp] theorem mul_one (P : Pauli n) : P * 1 = P := by
  funext i; simp [mul_apply]

@[simp] theorem one_mul (P : Pauli n) : 1 * P = P := by
  funext i; simp [mul_apply]

@[simp] theorem mul_self (P : Pauli n) : P * P = 1 := by
  funext i; simp [mul_apply]

/-- Every Pauli is its own inverse. -/
instance : Inv (Pauli n) := ⟨id⟩

@[simp] theorem inv_apply (P : Pauli n) (i : Fin n) : P⁻¹ i = P i := rfl

@[simp] theorem mul_inv_self (P : Pauli n) : P * P⁻¹ = 1 := mul_self P
@[simp] theorem inv_mul_self (P : Pauli n) : P⁻¹ * P = 1 := mul_self P

/-- The support of a Pauli: positions where it is not `I`. -/
def support (P : Pauli n) : Finset (Fin n) :=
  Finset.univ.filter fun i => P i ≠ SinglePauli.I

/-- The weight of an n-qubit Pauli: the size of its support. -/
def weight (P : Pauli n) : ℕ := (support P).card

@[simp] theorem support_one : support (1 : Pauli n) = ∅ := by
  simp [support]

@[simp] theorem weight_one : weight (1 : Pauli n) = 0 := by
  simp [weight, support_one]

theorem weight_le (P : Pauli n) : weight P ≤ n := by
  unfold weight
  calc (support P).card ≤ (Finset.univ : Finset (Fin n)).card :=
        Finset.card_le_univ _
    _ = n := by simp

/-- The set of Paulis of weight exactly `w`. -/
def ofWeight (n w : ℕ) : Finset (Pauli n) :=
  (Finset.univ : Finset (Pauli n)).filter (fun P => weight P = w)

theorem mem_ofWeight {n w : ℕ} {P : Pauli n} :
    P ∈ ofWeight n w ↔ weight P = w := by
  simp [ofWeight]

/-! ### Triangle inequality on weights -/

/-- The support of a product is contained in the union of supports. -/
theorem support_mul_subset (P Q : Pauli n) :
    support (P * Q) ⊆ support P ∪ support Q := by
  intro i hi
  simp only [support, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_union, mul_apply] at hi ⊢
  -- Contrapositive: if P i = I and Q i = I then (P*Q) i = I * I = I.
  by_contra hne
  push_neg at hne
  obtain ⟨hP, hQ⟩ := hne
  apply hi
  rw [hP, hQ]
  rfl

/-- **Triangle inequality** for Pauli weights. -/
theorem weight_mul_le (P Q : Pauli n) :
    weight (P * Q) ≤ weight P + weight Q := by
  unfold weight
  calc (support (P * Q)).card
      ≤ (support P ∪ support Q).card :=
        Finset.card_le_card (support_mul_subset P Q)
    _ ≤ (support P).card + (support Q).card := Finset.card_union_le _ _

end Pauli

end SCurveQEC
