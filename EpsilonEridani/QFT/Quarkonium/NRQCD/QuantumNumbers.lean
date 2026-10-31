/-
Copyright (c) 2026 The EpsilonEridani contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The EpsilonEridani contributors
-/
module

public import Mathlib.Algebra.Ring.CharZero
public import Mathlib.Algebra.Ring.Int.Units
public import Mathlib.Algebra.Ring.Parity

/-!
# The `J^{PC}` quantum numbers attainable by a quark-antiquark pair

A neutral meson that is its own antiparticle carries three conserved quantum numbers: its total
angular momentum `J`, its parity `P` and its charge-conjugation eigenvalue `C`, the last two being
signs. A quark-antiquark pair in the state `²ˢ⁺¹L_J`, with orbital angular momentum `L` and total
spin `S`, has

* `P = (-1)^(L+1)`: the orbital factor `(-1)^L` times the opposite intrinsic parities of a
  fermion and its antifermion;
* `C = (-1)^(L+S)`: exchanging the quark and the antiquark gives the orbital factor `(-1)^L`, the
  spin-exchange factor `(-1)^(S+1)`, and a factor `-1` from anticommuting the two fermion fields;

and, since each constituent has spin `1/2`, `S ∈ {0, 1}` with `|L - S| ≤ J ≤ L + S`. In this module
the two sign formulas are the definition of `QuantumNumbers.qqbar`; their derivation from the
transformation of the quark and antiquark fields is not part of it.

This module records which `J^{PC}` arise this way. The predicate `QuantumNumbers.QqbarAttainable`
asks for an `(L, S)` reproducing a given assignment. The search for `(L, S)` is bounded by
`L ≤ J + 1`, and the predicate is characterised in closed form, which also decides it: an
assignment is attainable exactly when it is that of a spin singlet (`C = -P` with
`P = (-1)^(J+1)`) or of a spin triplet (`C = P`, except for `0^{--}`). The complement is therefore
not empty; its members with `J ≤ 3` are `0^{--}`, `0^{+-}`, `1^{-+}`, `2^{+-}` and `3^{-+}`,
derived here from the predicate rather than listed as data, and every `J` carries the unattainable
assignment `P = (-1)^J`, `C = -P`.

Parity and charge-conjugation eigenvalues are stored in `ℤˣ`, so that they are signs by
construction and the predicate is decidable arithmetic.

## Main definitions

* `QuantumNumbers`: a `J^{PC}` assignment.
* `QuantumNumbers.qqbar L S J`: the `J^{PC}` of a quark-antiquark pair in the state `²ˢ⁺¹L_J`.
* `QuantumNumbers.QqbarAttainable`: the assignment is that of some quark-antiquark state.

## Main results

* `QuantumNumbers.qqbar_P_mul_C`: `CP = (-1)^(S+1)` depends on the spin alone.
* `QuantumNumbers.qqbarAttainable_qqbar`: every state `²ˢ⁺¹L_J` with `S ≤ 1` and
  `|L - S| ≤ J ≤ L + S` has attainable quantum numbers.
* `QuantumNumbers.qqbarAttainable_iff_exists_le`: the search for `(L, S)` is bounded by `J + 1`.
* `QuantumNumbers.qqbarAttainable_iff`: the closed-form characterisation by spin singlets and spin
  triplets, from which the `DecidablePred` instance is built, and
  `QuantumNumbers.not_qqbarAttainable_iff` for its complement.
* `QuantumNumbers.not_qqbarAttainable_mk_neg_one_pow`: for every `J` the assignment
  `P = (-1)^J`, `C = -P` is not attainable; `QuantumNumbers.not_qqbarAttainable_one_neg_one_one`
  is its case `1^{-+}`.
* `QuantumNumbers.not_qqbarAttainable_and_J_le_three_iff`: the unattainable assignments with
  `J ≤ 3` are exactly `0^{--}`, `0^{+-}`, `1^{-+}`, `2^{+-}` and `3^{-+}`.

## References

* Particle Data Group, S. Navas et al., *Review of Particle Physics*, Phys. Rev. D 110 (2024)
  030001, review "Quark model", Section 15.2.
* N. Brambilla et al., *Heavy quarkonium physics*, CERN-2005-005, arXiv:hep-ph/0412158,
  Chapter 3.
-/

public section

namespace EpsilonEridani.QFT.Quarkonium

/-- A `J^{PC}` assignment: a total angular momentum `J`, a parity eigenvalue `P` and a
charge-conjugation eigenvalue `C`, the eigenvalues being signs. -/
@[ext]
structure QuantumNumbers where
  /-- The total angular momentum `J`. -/
  J : ℕ
  /-- The parity eigenvalue `P`. -/
  P : ℤˣ
  /-- The charge-conjugation eigenvalue `C`. -/
  C : ℤˣ

-- The derived decision procedure is exposed so that `decide` can evaluate equalities of concrete
-- assignments in importing modules.
@[expose] section

deriving instance DecidableEq for QuantumNumbers

end

namespace QuantumNumbers

/-! ### The quantum numbers of a quark-antiquark state -/

/-- The `J^{PC}` of a quark-antiquark pair with orbital angular momentum `L`, total spin `S` and
total angular momentum `J`: `P = (-1)^(L+1)` and `C = (-1)^(L+S)`. -/
def qqbar (L S J : ℕ) : QuantumNumbers := ⟨J, (-1) ^ (L + 1), (-1) ^ (L + S)⟩

@[simp]
theorem qqbar_J (L S J : ℕ) : (qqbar L S J).J = J := (rfl)

@[simp]
theorem qqbar_P (L S J : ℕ) : (qqbar L S J).P = (-1) ^ (L + 1) := (rfl)

@[simp]
theorem qqbar_C (L S J : ℕ) : (qqbar L S J).C = (-1) ^ (L + S) := (rfl)

/-- The product `CP` of a quark-antiquark state is `(-1)^(S+1)`, fixed by the spin alone: `+1` for
a spin triplet and `-1` for a spin singlet. -/
theorem qqbar_P_mul_C (L S J : ℕ) : (qqbar L S J).P * (qqbar L S J).C = (-1) ^ (S + 1) := by
  simp only [qqbar_P, qqbar_C, ← pow_add]
  rw [show L + 1 + (L + S) = S + 1 + 2 * L by omega, pow_add, pow_mul]
  simp

/-! ### Attainability -/

/-- A `J^{PC}` assignment is attainable by a quark-antiquark pair when some orbital angular
momentum `L` and total spin `S ≤ 1`, coupled to `J` (`|L - S| ≤ J ≤ L + S`), give it the parity
`(-1)^(L+1)` and the charge-conjugation eigenvalue `(-1)^(L+S)`. -/
def QqbarAttainable (q : QuantumNumbers) : Prop :=
  ∃ L S : ℕ, S ≤ 1 ∧ L ≤ q.J + S ∧ q.J ≤ L + S ∧ S ≤ L + q.J ∧ qqbar L S q.J = q

theorem qqbarAttainable_def (q : QuantumNumbers) :
    q.QqbarAttainable ↔
      ∃ L S : ℕ, S ≤ 1 ∧ L ≤ q.J + S ∧ q.J ≤ L + S ∧ S ≤ L + q.J ∧ qqbar L S q.J = q :=
  Iff.rfl

/-- The quark-antiquark state `²ˢ⁺¹L_J` has attainable quantum numbers. -/
theorem qqbarAttainable_qqbar {L S J : ℕ} (hS : S ≤ 1) (hL : L ≤ J + S) (hJ : J ≤ L + S)
    (hS' : S ≤ L + J) : (qqbar L S J).QqbarAttainable :=
  ⟨L, S, hS, hL, hJ, hS', rfl⟩

/-- The search for `(L, S)` is bounded: `L ≤ J + 1` and `S ≤ 1`. -/
theorem qqbarAttainable_iff_exists_le (q : QuantumNumbers) :
    q.QqbarAttainable ↔
      ∃ L ≤ q.J + 1, ∃ S ≤ 1, L ≤ q.J + S ∧ q.J ≤ L + S ∧ S ≤ L + q.J ∧ qqbar L S q.J = q := by
  constructor
  · rintro ⟨L, S, hS, hL, hJ, hS', h⟩
    exact ⟨L, by omega, S, hS, hL, hJ, hS', h⟩
  · rintro ⟨L, -, S, hS, hL, hJ, hS', h⟩
    exact ⟨L, S, hS, hL, hJ, hS', h⟩

/-! ### The closed-form characterisation -/

private theorem eq_neg_one_pow_or (u : ℤˣ) (n : ℕ) : u = (-1) ^ n ∨ u = (-1) ^ (n + 1) := by
  rw [pow_succ, mul_neg_one]
  rcases Int.units_eq_one_or u with rfl | rfl <;>
    rcases Int.units_eq_one_or ((-1 : ℤˣ) ^ n) with h | h <;> rw [h] <;> decide

/-- A `J^{PC}` assignment is attainable by a quark-antiquark pair exactly when it is that of a spin
singlet (`L = J`, `C = -P`, `P = (-1)^(J+1)`) or of a spin triplet (`C = P`), the triplet excluding
`0^{--}`. -/
theorem qqbarAttainable_iff (q : QuantumNumbers) :
    q.QqbarAttainable ↔
      (q.C = -q.P ∧ q.P = (-1) ^ (q.J + 1)) ∨ (q.C = q.P ∧ (q.J ≠ 0 ∨ q.P = 1)) := by
  obtain ⟨J, p, c⟩ := q
  simp only [qqbarAttainable_def, QuantumNumbers.ext_iff, qqbar_J, qqbar_P, qqbar_C, true_and]
  constructor
  · rintro ⟨L, S, hS, hL, hJ, hS', rfl, rfl⟩
    obtain rfl | rfl : S = 0 ∨ S = 1 := by omega
    · -- a spin singlet has `L = J`
      obtain rfl : L = J := by omega
      left
      simp [pow_succ]
    · right
      refine ⟨rfl, ?_⟩
      -- a spin triplet with `J = 0` has `L = 1`
      rcases Nat.eq_zero_or_pos J with rfl | hJ0
      · obtain rfl : L = 1 := by omega
        right
        decide
      · exact Or.inl hJ0.ne'
  · rintro (⟨rfl, rfl⟩ | ⟨hc, hP⟩)
    · -- the spin singlet `¹J_J`
      exact ⟨J, 0, Nat.zero_le 1, by omega, by omega, by omega, rfl, by
        simp [pow_succ]⟩
    · subst c
      rcases eq_neg_one_pow_or p J with rfl | rfl
      · -- the spin triplet `³(J+1)_J`
        exact ⟨J + 1, 1, le_rfl, by omega, by omega, by omega, by simp [pow_succ]⟩
      · -- the spin triplet `³J_J`, which needs `J ≠ 0`
        have hJ0 : J ≠ 0 := by
          rintro rfl
          exact absurd (hP.resolve_left (by simp)) (by decide)
        exact ⟨J, 1, le_rfl, by omega, by omega, by omega, rfl, rfl⟩

/-- Attainability is decided by the closed form of `qqbarAttainable_iff`, which compares the
signs `P` and `C` with `±(-1)^J`. -/
instance : DecidablePred QqbarAttainable := fun q =>
  decidable_of_iff' _ (qqbarAttainable_iff q)

/-- An assignment is not attainable by a quark-antiquark pair exactly when `P = (-1)^J` and
`C = -P`, or it is `0^{--}`. -/
theorem not_qqbarAttainable_iff (q : QuantumNumbers) :
    ¬ q.QqbarAttainable ↔ (q.C = -q.P ∧ q.P = (-1) ^ q.J) ∨ (q.J = 0 ∧ q.P = -1 ∧ q.C = -1) := by
  obtain ⟨J, p, c⟩ := q
  rw [qqbarAttainable_iff]
  dsimp only
  rcases Nat.eq_zero_or_pos J with rfl | hJ
  · rcases Int.units_eq_one_or p with rfl | rfl <;>
      rcases Int.units_eq_one_or c with rfl | rfl <;> decide
  · rcases eq_neg_one_pow_or p J with rfl | rfl <;>
      obtain rfl | rfl := eq_or_ne c ((-1 : ℤˣ) ^ J) |>.imp_right Int.units_ne_iff_eq_neg.1 <;>
      simp [pow_succ, hJ.ne']

/-- For every `J`, the assignment `P = (-1)^J`, `C = -P` is not attainable by a quark-antiquark
pair: `0^{+-}`, `1^{-+}`, `2^{+-}`, `3^{-+}`, and so on. -/
theorem not_qqbarAttainable_mk_neg_one_pow (J : ℕ) :
    ¬ (⟨J, (-1) ^ J, -(-1) ^ J⟩ : QuantumNumbers).QqbarAttainable :=
  (not_qqbarAttainable_iff _).2 (Or.inl ⟨rfl, rfl⟩)

/-- `1^{-+}` is not attainable by a quark-antiquark pair. -/
theorem not_qqbarAttainable_one_neg_one_one : ¬ (⟨1, -1, 1⟩ : QuantumNumbers).QqbarAttainable := by
  decide

/-- The assignments with `J ≤ 3` that no quark-antiquark pair attains are exactly `0^{--}`,
`0^{+-}`, `1^{-+}`, `2^{+-}` and `3^{-+}`. -/
theorem not_qqbarAttainable_and_J_le_three_iff (q : QuantumNumbers) :
    ¬ q.QqbarAttainable ∧ q.J ≤ 3 ↔
      q = ⟨0, -1, -1⟩ ∨ q = ⟨0, 1, -1⟩ ∨ q = ⟨1, -1, 1⟩ ∨ q = ⟨2, 1, -1⟩ ∨ q = ⟨3, -1, 1⟩ := by
  constructor
  · obtain ⟨J, p, c⟩ := q
    rintro ⟨h, hJ⟩
    obtain rfl | rfl | rfl | rfl : J = 0 ∨ J = 1 ∨ J = 2 ∨ J = 3 := by dsimp only at hJ; omega
    all_goals rcases Int.units_eq_one_or p with rfl | rfl <;>
      rcases Int.units_eq_one_or c with rfl | rfl <;> revert h <;> decide
  · rintro (rfl | rfl | rfl | rfl | rfl) <;> decide

end QuantumNumbers

end EpsilonEridani.QFT.Quarkonium
