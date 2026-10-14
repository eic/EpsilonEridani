/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.RingTheory.PowerSeries.Substitution

/-!
# The substitution group of formal power series

The power series `F = u X + c₁ X² + c₂ X³ + ⋯` without constant term and with invertible linear
coefficient `u` form a group under substitution, `(F * G)(X) = F(G(X))`, whose inverse is
Mathlib's compositional inverse `PowerSeries.substInvOfIsUnit`. This file builds that group
(`EpsilonEridani.SubstGroup`) and the homomorphism `F ↦ u` to the units of the
coefficient ring, whose kernel is the subgroup of substitutions tangent to the identity.

It also records the finite form of the coefficients of a substitution without constant term.
Mathlib's `PowerSeries.coeff_subst'` writes the coefficients of `f.subst b`, the series `f(b)`,
as a `finsum` over all powers of `b`; when `b` has no constant term only the powers `b ^ d` with
`d ≤ n` contribute to the coefficient of `X ^ n`.

## Main definitions

* `EpsilonEridani.SubstGroup R`: the group of power series `u X + O(X²)` with `u` a unit, under
  substitution.
* `EpsilonEridani.SubstGroup.linearCoeff`: the homomorphism `F ↦ F'(0)` to `Rˣ`.
* `EpsilonEridani.SubstGroup.rescale u`: the linear substitution `X ↦ u X`.

## Main statements

* `PowerSeries.coeff_subst_eq_sum_range`: `[Xⁿ] f(b) = ∑_{d ≤ n} [X^d] f • [Xⁿ] b ^ d`.
* `PowerSeries.coeff_one_subst`: the chain rule `[X] f(b) = [X] f • [X] b`.

## References

* S. A. Jennings, *Substitution groups of formal power series*, Canad. J. Math. **6** (1954)
  325.
-/

@[expose] public section

noncomputable section

namespace PowerSeries

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- The coefficient of `X ^ n` in `f(b)`, for `b` without constant term, is the finite sum
`∑_{d ≤ n} [X^d] f • [Xⁿ] b ^ d`: the powers `b ^ d` with `d > n` are divisible by `X ^ (n + 1)`. -/
theorem coeff_subst_eq_sum_range {b : S⟦X⟧} (hb : constantCoeff b = 0) (f : R⟦X⟧) (n : ℕ) :
    coeff n (f.subst b) = ∑ d ∈ Finset.range (n + 1), coeff d f • coeff n (b ^ d) := by
  rw [coeff_subst' (HasSubst.of_constantCoeff_zero' hb),
    finsum_eq_sum_of_support_subset _ (s := Finset.range (n + 1))]
  intro d hd
  rw [Function.mem_support] at hd
  rw [Finset.coe_range, Set.mem_Iio]
  by_contra h
  exact hd (by rw [X_pow_dvd_iff.mp (pow_dvd_pow_of_dvd (X_dvd_iff.mpr hb) d) n (by omega),
    smul_zero])

/-- The linear coefficient of a substitution without constant term is the product of the linear
coefficients: `[X] f(b) = [X] f • [X] b`. -/
theorem coeff_one_subst {b : S⟦X⟧} (hb : constantCoeff b = 0) (f : R⟦X⟧) :
    coeff 1 (f.subst b) = coeff 1 f • coeff 1 b := by
  simp [coeff_subst_eq_sum_range hb, Finset.sum_range_succ, coeff_one]

end PowerSeries

open PowerSeries

namespace EpsilonEridani

/-- A power series `u X + c₁ X² + c₂ X³ + ⋯` without constant term whose linear coefficient `u`
is a unit: an element of the group of such series under substitution. -/
@[ext]
structure SubstGroup (R : Type*) [CommRing R] where
  /-- The underlying power series. -/
  toPowerSeries : R⟦X⟧
  /-- The series has no constant term. -/
  constantCoeff_toPowerSeries : constantCoeff toPowerSeries = 0
  /-- The linear coefficient is a unit. -/
  isUnit_coeff_one_toPowerSeries : IsUnit (coeff 1 toPowerSeries)

namespace SubstGroup

variable {R : Type*} [CommRing R]

attribute [simp] constantCoeff_toPowerSeries

/-- An element of the substitution group can be substituted into any power series. -/
lemma hasSubst (F : SubstGroup R) : HasSubst F.toPowerSeries :=
  HasSubst.of_constantCoeff_zero' F.constantCoeff_toPowerSeries

/-- The identity substitution `X`. -/
instance : One (SubstGroup R) :=
  ⟨⟨X, constantCoeff_X, by simp [coeff_X]⟩⟩

/-- Composition of substitutions: `(F * G)(X) = F(G(X))`. -/
instance : Mul (SubstGroup R) :=
  ⟨fun F G => ⟨F.toPowerSeries.subst G.toPowerSeries,
    constantCoeff_subst_eq_zero G.constantCoeff_toPowerSeries _ F.constantCoeff_toPowerSeries,
    by rw [coeff_one_subst G.constantCoeff_toPowerSeries, smul_eq_mul]
       exact F.isUnit_coeff_one_toPowerSeries.mul G.isUnit_coeff_one_toPowerSeries⟩⟩

/-- The compositional inverse. -/
instance : Inv (SubstGroup R) :=
  ⟨fun F => ⟨F.toPowerSeries.substInvOfIsUnit F.isUnit_coeff_one_toPowerSeries,
    constantCoeff_substInvOfIsUnit _ _, by simp⟩⟩

@[simp]
lemma toPowerSeries_one : (1 : SubstGroup R).toPowerSeries = X := (rfl)

@[simp]
lemma toPowerSeries_mul (F G : SubstGroup R) :
    (F * G).toPowerSeries = F.toPowerSeries.subst G.toPowerSeries := (rfl)

lemma toPowerSeries_inv (F : SubstGroup R) :
    F⁻¹.toPowerSeries =
      F.toPowerSeries.substInvOfIsUnit F.isUnit_coeff_one_toPowerSeries := (rfl)

/-- `F⁻¹(F(X)) = X`. -/
@[simp]
lemma subst_toPowerSeries_inv_left (F : SubstGroup R) :
    F⁻¹.toPowerSeries.subst F.toPowerSeries = X :=
  subst_substInvOfIsUnit_left _ F.constantCoeff_toPowerSeries _

/-- `F(F⁻¹(X)) = X`. -/
@[simp]
lemma subst_toPowerSeries_inv_right (F : SubstGroup R) :
    F.toPowerSeries.subst F⁻¹.toPowerSeries = X :=
  subst_substInvOfIsUnit_right _ F.constantCoeff_toPowerSeries _

/-- The power series without constant term and with invertible linear coefficient form a group
under substitution. -/
instance : Group (SubstGroup R) where
  mul_assoc F G H := by
    ext1
    simp [subst_comp_subst_apply G.hasSubst H.hasSubst]
  one_mul F := by
    ext1
    simp [subst_X F.hasSubst]
  mul_one F := by
    ext1
    simp [X_subst]
  inv_mul_cancel F := by
    ext1
    simp only [toPowerSeries_mul, subst_toPowerSeries_inv_left, toPowerSeries_one]

/-- The linear coefficient `F'(0)`, a homomorphism to the units: by the chain rule the linear
coefficients of a composite multiply. -/
def linearCoeff : SubstGroup R →* Rˣ where
  toFun F := F.isUnit_coeff_one_toPowerSeries.unit
  map_one' := by
    ext
    simp [coeff_X]
  map_mul' F G := by
    ext
    simp [coeff_one_subst G.constantCoeff_toPowerSeries]

@[simp]
lemma coe_linearCoeff (F : SubstGroup R) :
    (linearCoeff F : R) = coeff 1 F.toPowerSeries := (rfl)

/-- The linear coefficient of the inverse substitution is the inverse of the linear
coefficient. -/
@[simp]
lemma coeff_one_toPowerSeries_inv (F : SubstGroup R) :
    coeff 1 F⁻¹.toPowerSeries = ((linearCoeff F)⁻¹ : Rˣ) := by
  rw [toPowerSeries_inv]
  exact coeff_one_substInvOfIsUnit _ _

lemma mem_ker_linearCoeff_iff {F : SubstGroup R} :
    F ∈ linearCoeff.ker ↔ coeff 1 F.toPowerSeries = 1 := by
  rw [MonoidHom.mem_ker, Units.ext_iff, coe_linearCoeff, Units.val_one]

/-- The linear substitution `X ↦ u X`, whose action by substitution is `PowerSeries.rescale u`. -/
def rescale (u : Rˣ) : SubstGroup R :=
  ⟨C (u : R) * X, by simp, by simp⟩

@[simp]
lemma toPowerSeries_rescale (u : Rˣ) : (rescale u).toPowerSeries = C (u : R) * X := (rfl)

@[simp]
lemma linearCoeff_rescale (u : Rˣ) : linearCoeff (rescale u) = u := by
  ext
  simp

@[simp]
lemma rescale_one : rescale (1 : Rˣ) = 1 := by
  ext1
  simp

@[simp]
lemma rescale_mul (u v : Rˣ) : rescale (u * v) = rescale u * rescale v := by
  ext1
  simp only [toPowerSeries_mul, toPowerSeries_rescale]
  rw [← smul_eq_C_mul X (v : R), ← PowerSeries.rescale_eq_subst, ← rescale_X, ← rescale_X,
    rescale_rescale, Units.val_mul]

@[simp]
lemma rescale_inv (u : Rˣ) : rescale u⁻¹ = (rescale u)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← rescale_mul, inv_mul_cancel, rescale_one])

end SubstGroup

end EpsilonEridani
