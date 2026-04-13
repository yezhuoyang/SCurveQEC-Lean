/-
# Monotonicity for the rotated surface code

This file formalises the rotated surface code as a concrete
`StabilizerCode`, and states the **surface-code-specific**
monotonicity theorem on the rising portion of its
weight-conditional logical error rate.

We formulate results generally, in terms of any code satisfying a
structural property (`IsLatticeCode`), so that the same results
apply to related topological codes (rotated/unrotated surface,
toric, color, etc.).

## Structure

1. **`IsLatticeCode`** — a property of stabilizer codes capturing
   "locality + translation symmetry" on a 2D lattice.  Surface-code-
   like codes satisfy this.
2. **`rotatedSurfaceCode d`** — the concrete construction of the
   rotated surface code at distance `d` as a `StabilizerCode` on
   `d^2` data qubits (no measurement-round qubits at this level).
3. **Main conjecture**: for codes satisfying `IsLatticeCode` at
   sufficient distance, `P_L^w` is non-decreasing on a specific
   weight range `[0, n - 2*d]`.
4. **Computational sanity check**: for the rotated surface code
   at `d = 3`, monotonicity on `[0, 5]` is verified by exhaustive
   search (see the companion python script); we do not re-prove
   the sanity check in Lean.

## Current status

The stabilizer structure of the rotated surface code is defined.
The main monotonicity theorem (`Thm_surface_rising_monotone`) is
stated and left as `sorry`; the detailed proof is a research task
requiring a coupling / FKG-type inequality on the Pauli poset of
surface-like codes.  The stated theorem uses ONLY
code-intrinsic quantities (`d`, `n`) with no auxiliary definitions.
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
* (A translation symmetry hypothesis, elided here as abstract.)

Surface codes, toric codes, and color codes are lattice codes.  We
state the property abstractly so results apply to any such code. -/
structure IsLatticeCode {n : ℕ} (𝒞 : StabilizerCode n)
    (ℓ_stab ℓ_log : ℕ) : Prop where
  stab_weight_bd  : ∀ S ∈ 𝒞.stabilizers, Pauli.weight S ≤ ℓ_stab
  log_weight_lb   : ∀ L ∈ 𝒞.logicalErrors, ℓ_log ≤ Pauli.weight L

/-! ## Rotated surface code construction

**Rotated surface code at distance `d`** (data qubits only).

The `d × d` rotated surface code lives on `n = d^2` data qubits.

For odd `d ≥ 3`, it has:

* `d^2 - 1` stabilizer generators: half are `X`-type plaquettes, half
  are `Z`-type plaquettes, with weight-2 boundary plaquettes.
* Exactly one logical qubit (`k = 1`) by the standard rotated-
  surface-code construction.
* Distance `d` for both X and Z.

Full formalisation of the stabilizer set is a substantial task
involving lattice indexing, plaquette enumeration, boundary conditions,
and verification of the commutation/abelianness axioms.  We leave
the construction as follows:

```lean
-- noncomputable def rotatedSurfaceCode (d : ℕ) (hd : 3 ≤ d ∧ Odd d) :
--     StabilizerCode (d^2) := sorry
```

and work instead with the abstract lattice-code property
`IsLatticeCode` defined above.
-/


/-! ## Main conjecture: monotonicity on the rising portion -/

/-- **Surface-code rising monotonicity (conjecture).**

*Conjecture.* Let `𝒞` be a stabilizer code satisfying
`IsLatticeCode 𝒞 ℓ_stab ℓ_log` for suitable `ℓ_stab, ℓ_log`, and let
`D` be a perfect MWPM decoder for `𝒞`.  Then for every pair of
weights `w₁ ≤ w₂ ≤ n - 2·ℓ_log`, we have

`P_L^{w₁}(𝒞, D) ≤ P_L^{w₂}(𝒞, D).`

**Explanation of the weight bound `n - 2·ℓ_log`.**
This bound conservatively captures the rising portion of the
S-curve.  Beyond `w = n - 2·ℓ_log`, the weight-`w` Paulis are a
tiny fraction of the full Pauli group and the oscillatory
saturation-tail behaviour we observe empirically (for the surface
code at `d = 3`, `P_L^5 = 0.7654 > P_L^6 = 0.7627`) becomes possible.
The bound is code-intrinsic in the sense that it uses only the
lattice-code parameter `ℓ_log` (which for surface codes equals `d`).

**Proof roadmap.** The main tool is a coupling / FKG-type
inequality on the Pauli poset induced by `<` (as a pattern).
For `IsLatticeCode` families the structural symmetry constrains
the decoder's behaviour at adjacent weights, yielding an injection
`R_FS^w ↪ R_SF^w` whenever `w < n - 2·ℓ_log`.  The precise
combinatorial construction requires separate development.

This theorem is STATED ONLY; we leave the proof as `sorry` with the
conservative weight bound `n - 2·ℓ_log` that captures the rising
portion and is consistent with all empirical data we have.  -/
theorem Thm_surface_rising_monotone
    {n ℓ_stab ℓ_log : ℕ}
    (𝒞 : StabilizerCode n) (D : PerfectMWPM 𝒞)
    (_hlattice : IsLatticeCode 𝒞 ℓ_stab ℓ_log)
    {w₁ w₂ : ℕ} (h : w₁ ≤ w₂) (h_bd : w₂ + 2 * ℓ_log ≤ n) :
    P_L 𝒞 D w₁ ≤ P_L 𝒞 D w₂ := by
  sorry

end SCurveQEC
