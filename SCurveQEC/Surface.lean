/-
# Monotonicity for the surface code (circuit-level noise)

This file contains the **surface-code-specific** proof that
`PairBalance` (Monotone.lean) holds for the compiled memory-
experiment circuit of a `d × d` rotated surface code with
`r` rounds of syndrome extraction.

The subtlety is that we work at the **circuit level**: the Paulis
live on *all* qubits in the compiled circuit --- data qubits
AND syndrome qubits across all measurement rounds. This is NOT
the data-qubit-only code with distance `d`; instead, the
circuit-level code has a different structure with contributions
from syndrome qubit errors and hook errors.

## Setup

We model the compiled surface code as an abstract `StabilizerCode`
on `C(d, r)` qubits, where `C(d, r) ≈ 8 d^2 r` (from the paper
companion analysis).  The *circuit-level distance* may be less than
`d` due to hook errors.

## The surface-code-specific lemma

For the compiled surface code circuit:

* There is a *translation symmetry* of the detector graph that acts
  on Paulis by weight-preserving permutations.  Specifically, the
  surface has translation invariance in space (within the bulk) and
  time (across measurement rounds).

* Under this symmetry, the failure set is a union of orbits.
  Combined with the local-decoder structure of MWPM on the detector
  graph, this gives an explicit map `R_FS → R_SF` that is an
  injection, proving `PairBalance`.

## Current status

This file is a stub.  The definitions and proofs are outlined here;
the formalisation is a substantial undertaking, involving:

1. Formalising the rotated-surface-code stabilizer structure as a
   `StabilizerCode`.
2. Formalising the compiled circuit's fault locations (including
   syndrome-qubit errors).
3. Proving the translation-symmetry lemmas on Paulis.
4. Using the symmetry to construct the injection `R_FS → R_SF`.

Each step is a (sub-)paper's worth of work.  We leave this as a
declared roadmap.
-/
import SCurveQEC.Pauli
import SCurveQEC.Stabilizer
import SCurveQEC.Decoder
import SCurveQEC.ErrorRate
import SCurveQEC.Monotone

namespace SCurveQEC

-- The rotated surface code circuit will be formalised here.
-- This file is currently a stub; see the file docstring for the roadmap.

end SCurveQEC
