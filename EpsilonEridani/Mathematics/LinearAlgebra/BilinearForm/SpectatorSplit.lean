/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Splitting off the spectators of a pair of vectors

For a bilinear form `g` on a vector space `V` over a field `K` and a pair of vectors `(a, b)`,
a *spectator* is a vector `g`-orthogonal to both. This file records two properties of the pair
in terms of its spectators.

## Main definitions

* `LinearMap.BilinForm.IsSpectatorSplit g a b`: every vector is a combination of `a` and `b` plus
  a spectator.
* `LinearMap.BilinForm.IsAnisotropicSpectator g a b`: no non-zero spectator is `g`-null.

## Main statements

* `LinearMap.BilinForm.isSpectatorSplit_of_gramDet_ne_zero`: a pair with non-zero Gram
  determinant splits `V`, by Cramer's rule.
* `LinearMap.BilinForm.IsSpectatorSplit.symm`, `IsAnisotropicSpectator.symm`: both properties are
  independent of the order of the pair.
-/

@[expose] public section

namespace LinearMap.BilinForm

open LinearMap (BilinForm)

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The pair `(a, b)` splits `V`: every vector is a combination of `a` and `b` plus a spectator,
a vector `g`-orthogonal to both. -/
structure IsSpectatorSplit (g : BilinForm K V) (a b : V) : Prop where
  /-- Every vector is a combination of `a` and `b` plus a spectator `g`-orthogonal to both. -/
  span : ∀ v : V, ∃ (x y : K) (u : V), g a u = 0 ∧ g b u = 0 ∧ v = x • a + y • b + u

/-- The splitting does not depend on the order of the pair. -/
lemma IsSpectatorSplit.symm {g : BilinForm K V} {a b : V} (h : g.IsSpectatorSplit a b) :
    g.IsSpectatorSplit b a where
  span v := by
    obtain ⟨x, y, u, hau, hbu, rfl⟩ := h.span v
    exact ⟨y, x, u, hbu, hau, by abel⟩

/-- Two vectors with non-zero Gram determinant split `V`: the coefficients of `v` solve the
linear system `g a v = x g a a + y g a b`, `g b v = x g b a + y g b b` by Cramer's rule, and the
remainder is `g`-orthogonal to both. -/
lemma isSpectatorSplit_of_gramDet_ne_zero (g : BilinForm K V) {a b : V}
    (h : g a a * g b b - g a b * g b a ≠ 0) : g.IsSpectatorSplit a b := by
  have h' : g b b * g a a - g a b * g b a ≠ 0 := by rwa [mul_comm (g b b)]
  refine ⟨fun v => ?_⟩
  set x := (g a v * g b b - g a b * g b v) / (g a a * g b b - g a b * g b a)
  set y := (g a a * g b v - g b a * g a v) / (g a a * g b b - g a b * g b a)
  refine ⟨x, y, v - x • a - y • b, ?_, ?_, by abel⟩
  · simp only [map_sub, map_smul, smul_eq_mul, x, y]
    field_simp [h']
    ring
  · simp only [map_sub, map_smul, smul_eq_mul, x, y]
    field_simp [h']
    ring

/-- No non-zero spectator of the pair `(a, b)` — a vector `g`-orthogonal to both — is `g`-null,
so the reflection in it (`LinearMap.BilinForm.reflection`) reverses it. -/
def IsAnisotropicSpectator (g : BilinForm K V) (a b : V) : Prop :=
  ∀ u : V, g a u = 0 → g b u = 0 → u ≠ 0 → g u u ≠ 0

/-- Anisotropy of the spectators does not depend on the order of the pair. -/
lemma IsAnisotropicSpectator.symm {g : BilinForm K V} {a b : V}
    (h : g.IsAnisotropicSpectator a b) : g.IsAnisotropicSpectator b a :=
  fun u hbu hau hu => h u hau hbu hu

end LinearMap.BilinForm
