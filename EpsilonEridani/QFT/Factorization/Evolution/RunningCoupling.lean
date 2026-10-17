/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import EpsilonEridani.QFT.QCD.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Topology.Algebra.Order.Field

/-!
# The one-loop running coupling

The renormalisation-group equation for the strong coupling, truncated at one loop, is the scalar
autonomous equation

`da/dt = -β₀ a²`,

with `t = log (Q² / μ₀²)` the logarithm of the scale in units of a reference scale `μ₀`, `a` the
coupling in the normalisation `a = α_s / (4π)` in which `β₀ = (11/3) C_A - (4/3) T_F n_f` is
`EpsilonEridani.QFT.QCD.beta0`, and the sign fixed so that `β₀ > 0` is asymptotic freedom.

`oneLoopCoupling β₀ a₀ t = a₀ / (1 + β₀ a₀ t)` is its solution with `a (0) = a₀`. This file proves
that it is a solution (`hasDerivAt_oneLoopCoupling`), that it is the only one through a nonzero
initial value (`IsOneLoopRGSolution.eq_oneLoopCoupling`), and the three qualitative facts the
truncation is used for: the coupling decreases with the scale and tends to zero
(`strictAntiOn_oneLoopCoupling`, `tendsto_oneLoopCoupling_atTop_zero`) at the rate
`a(t) = 1/(β₀ t) + O(t⁻²)` (`isBigO_oneLoopCoupling_sub_inv`), and it blows up at the finite time
`landauTime β₀ a₀ = -(β₀ a₀)⁻¹` below which no solution extends at all
(`tendsto_oneLoopCoupling_nhdsGT_landauTime`,
`IsOneLoopRGSolution.add_landauTime_notMem`). The last is a property of the truncation, not of
QCD.

`landauTime` is the `Λ` parameter of the one-loop coupling, expressed in the evolution variable:
it is a derived quantity, not an independent one, and it does not depend on which scale is taken
as the reference (`landauTime_oneLoopCoupling`, and `landauScaleSq_oneLoopCoupling` for the
scale `Λ² = μ₀² exp (landauTime β₀ a₀)` itself). Eliminating `a₀` in favour of it turns the
solution into the familiar `a(Q²) = 1 / (β₀ log (Q² / Λ²))` (`oneLoopCoupling_log_eq_inv`).

The coupling here is `a₄` as a function of the evolution variable `t`, not `α_s` as a function of
`Q²`; it is a different object from `EpsilonEridani.QFT.QCD.oneLoopAlphaS`, which is a regularised
proxy, total in `Q²` and `Λ²` by construction and therefore not a solution of the equation above.

## References

* D. J. Gross and F. Wilczek, *Ultraviolet behavior of non-abelian gauge theories*, Phys. Rev.
  Lett. 30 (1973) 1343.
* H. D. Politzer, *Reliable perturbative results for strong interactions?*, Phys. Rev. Lett. 30
  (1973) 1346.
* J. C. Collins, *Foundations of Perturbative QCD*, Cambridge University Press (2011), ch. 3.
-/

public section

noncomputable section

open Asymptotics Filter Set Topology

namespace EpsilonEridani
namespace QFT
namespace Factorization
namespace Evolution

variable {β₀ a₀ s t μ₀sq μ₁sq Q2 : ℝ}

/-! ### The solution and its Landau time -/

/-- The one-loop running coupling `a₀ / (1 + β₀ a₀ t)`: the solution of `da/dt = -β₀ a²` taking
the value `a₀` at `t = 0`, where `t = log (Q² / μ₀²)` and the coupling is normalised as
`a = α_s / (4π)`. -/
def oneLoopCoupling (β₀ a₀ t : ℝ) : ℝ := a₀ / (1 + β₀ * a₀ * t)

theorem oneLoopCoupling_def (β₀ a₀ t : ℝ) :
    oneLoopCoupling β₀ a₀ t = a₀ / (1 + β₀ * a₀ * t) :=
  (rfl)

@[simp]
theorem oneLoopCoupling_zero (β₀ a₀ : ℝ) : oneLoopCoupling β₀ a₀ 0 = a₀ := by
  rw [oneLoopCoupling_def]
  norm_num

/-- The Landau time of the one-loop coupling: the value `-(β₀ a₀)⁻¹` of the evolution variable at
which the denominator of `oneLoopCoupling β₀ a₀` vanishes. This is the `Λ` parameter of the
one-loop coupling in the evolution variable, as a quantity derived from the reference value `a₀`
rather than an independent parameter; see `landauScaleSq` for the scale itself. -/
def landauTime (β₀ a₀ : ℝ) : ℝ := -(β₀ * a₀)⁻¹

theorem landauTime_def (β₀ a₀ : ℝ) : landauTime β₀ a₀ = -(β₀ * a₀)⁻¹ :=
  (rfl)

/-- The denominator of the one-loop coupling vanishes at the Landau time. -/
theorem one_add_mul_landauTime_eq_zero (hβ : β₀ ≠ 0) (ha : a₀ ≠ 0) :
    1 + β₀ * a₀ * landauTime β₀ a₀ = 0 := by
  rw [landauTime_def, mul_neg, mul_inv_cancel₀ (mul_ne_zero hβ ha)]
  norm_num

/-- For a positive `β₀` and a positive reference value the Landau time is negative: the one-loop
coupling diverges at a finite scale *below* the reference scale. -/
theorem landauTime_neg (hβ : 0 < β₀) (ha : 0 < a₀) : landauTime β₀ a₀ < 0 := by
  rw [landauTime_def, neg_lt_zero]
  exact inv_pos.2 (mul_pos hβ ha)

/-- For a positive `β₀ a₀` the denominator of the one-loop coupling is positive exactly above the
Landau time. -/
theorem landauTime_lt_iff (h : 0 < β₀ * a₀) :
    landauTime β₀ a₀ < t ↔ 0 < 1 + β₀ * a₀ * t := by
  have h0 : β₀ * a₀ ≠ 0 := ne_of_gt h
  have key : β₀ * a₀ * landauTime β₀ a₀ = -1 := by
    rw [landauTime_def, mul_neg, mul_inv_cancel₀ h0]
  constructor
  · intro ht
    have := mul_lt_mul_of_pos_left ht h
    rw [key] at this
    linarith
  · intro ht
    by_contra hcon
    have := mul_le_mul_of_nonneg_left (not_lt.1 hcon) h.le
    rw [key] at this
    linarith

/-- The one-loop coupling with the reference value eliminated in favour of the Landau time:
`a(t) = 1 / (β₀ (t - t_Λ))`. -/
theorem oneLoopCoupling_eq_inv (hβ : β₀ ≠ 0) (ha : a₀ ≠ 0) (t : ℝ) :
    oneLoopCoupling β₀ a₀ t = (β₀ * (t - landauTime β₀ a₀))⁻¹ := by
  have key : β₀ * (t + (β₀ * a₀)⁻¹) = (1 + β₀ * a₀ * t) / a₀ := by
    field_simp
    ring
  rw [oneLoopCoupling_def, landauTime_def, sub_neg_eq_add, key, inv_div]

/-! ### The renormalisation-group equation -/

/-- `IsOneLoopRGSolution β₀ s f` says that `f` solves the one-loop renormalisation-group equation
`da/dt = -β₀ a²` at every point of `s`, where `t = log (Q² / μ₀²)`. The solutions are exactly the
one-loop couplings of `oneLoopCoupling`, by `isOneLoopRGSolution_oneLoopCoupling` and
`IsOneLoopRGSolution.eq_oneLoopCoupling`. -/
def IsOneLoopRGSolution (β₀ : ℝ) (s : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ t ∈ s, HasDerivAt f (-β₀ * f t ^ 2) t

/-- **The one-loop renormalisation-group equation.** Away from its Landau time, the one-loop
coupling satisfies `da/dt = -β₀ a²`. -/
theorem hasDerivAt_oneLoopCoupling (β₀ a₀ : ℝ) (h : 1 + β₀ * a₀ * t ≠ 0) :
    HasDerivAt (oneLoopCoupling β₀ a₀) (-β₀ * oneLoopCoupling β₀ a₀ t ^ 2) t := by
  have hd : HasDerivAt (fun u : ℝ => 1 + β₀ * a₀ * u) (β₀ * a₀) t := by
    simpa using ((hasDerivAt_id t).const_mul (β₀ * a₀)).const_add 1
  have key : (0 * (1 + β₀ * a₀ * t) - a₀ * (β₀ * a₀)) / (1 + β₀ * a₀ * t) ^ 2
      = -β₀ * oneLoopCoupling β₀ a₀ t ^ 2 := by
    rw [oneLoopCoupling_def]
    field_simp
    ring
  have hdiv := (hasDerivAt_const t a₀).div hd h
  rw [key] at hdiv
  exact hdiv

/-- The one-loop coupling solves the one-loop renormalisation-group equation off its Landau
time. -/
theorem isOneLoopRGSolution_oneLoopCoupling (β₀ a₀ : ℝ) :
    IsOneLoopRGSolution β₀ {t | 1 + β₀ * a₀ * t ≠ 0} (oneLoopCoupling β₀ a₀) :=
  fun _ ht => hasDerivAt_oneLoopCoupling β₀ a₀ ht

/-- A solution of the one-loop renormalisation-group equation on an open interval that is nonzero
somewhere on the interval is nonzero everywhere on it: a coupling obeying the one-loop equation
cannot reach zero at a finite scale. -/
theorem IsOneLoopRGSolution.ne_zero {A B t₀ : ℝ} {f : ℝ → ℝ}
    (hf : IsOneLoopRGSolution β₀ (Ioo A B) f) (ht₀ : t₀ ∈ Ioo A B) (h₀ : f t₀ ≠ 0) :
    ∀ t ∈ Ioo A B, f t ≠ 0 := by
  intro t₁ ht₁ hzero
  -- Work on a compact interval `[a, b] ⊆ Ioo A B` whose interior contains `t₀` and `t₁`.
  obtain ⟨a, haA, ha⟩ := exists_between (lt_min ht₀.1 ht₁.1)
  obtain ⟨b, hb, hbB⟩ := exists_between (max_lt ht₀.2 ht₁.2)
  have hsub : Icc a b ⊆ Ioo A B := fun u hu =>
    ⟨lt_of_lt_of_le haA hu.1, lt_of_le_of_lt hu.2 hbB⟩
  have ht₀' : t₀ ∈ Ioo a b :=
    ⟨lt_of_lt_of_le ha (min_le_left _ _), lt_of_le_of_lt (le_max_left _ _) hb⟩
  have ht₁' : t₁ ∈ Ioo a b :=
    ⟨lt_of_lt_of_le ha (min_le_right _ _), lt_of_le_of_lt (le_max_right _ _) hb⟩
  have hcont : ContinuousOn f (Icc a b) := fun u hu =>
    (hf u (hsub hu)).continuousAt.continuousWithinAt
  -- `f` is bounded on `[a, b]`, and on a bounded set `x ↦ -β₀ x²` is Lipschitz, so Mathlib's
  -- uniqueness for Lipschitz right-hand sides applies with the zero solution.
  obtain ⟨R, hR⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  have hR0 : 0 ≤ R := le_trans (norm_nonneg _) (hR t₀ (Ioo_subset_Icc_self ht₀'))
  have hmem : ∀ u ∈ Icc a b, f u ∈ Icc (-R) R := fun u hu =>
    mem_Icc.2 (abs_le.1 (by simpa only [Real.norm_eq_abs] using hR u hu))
  have hlip : LipschitzOnWith (Real.toNNReal (2 * |β₀| * R)) (fun x : ℝ => -β₀ * x ^ 2)
      (Icc (-R) R) := by
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro x hx y hy
    have hx' : |x| ≤ R := abs_le.2 ⟨(mem_Icc.1 hx).1, (mem_Icc.1 hx).2⟩
    have hy' : |y| ≤ R := abs_le.2 ⟨(mem_Icc.1 hy).1, (mem_Icc.1 hy).2⟩
    have hfac : -β₀ * x ^ 2 - -β₀ * y ^ 2 = -β₀ * (x + y) * (x - y) := by ring
    rw [Real.coe_toNNReal _ (mul_nonneg (by positivity) hR0), Real.dist_eq, Real.dist_eq, hfac,
      abs_mul]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    rw [abs_mul, abs_neg]
    calc |β₀| * |x + y| ≤ |β₀| * (|x| + |y|) :=
          mul_le_mul_of_nonneg_left (abs_add_le x y) (abs_nonneg β₀)
      _ ≤ |β₀| * (R + R) := by
          exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg β₀)
      _ = 2 * |β₀| * R := by ring
  have heq := ODE_solution_unique_of_mem_Icc (v := fun _ x => -β₀ * x ^ 2)
    (s := fun _ => Icc (-R) R) (f := f) (g := fun _ => 0) (fun _ _ => hlip) ht₁' hcont
    (fun u hu => hf u (hsub (Ioo_subset_Icc_self hu)))
    (fun u hu => hmem u (Ioo_subset_Icc_self hu)) continuousOn_const
    (fun u _ => by simpa using hasDerivAt_const u (0 : ℝ))
    (fun _ _ => mem_Icc.2 ⟨by linarith, hR0⟩) (by simpa using hzero)
  exact h₀ (heq (Ioo_subset_Icc_self ht₀'))

/-- The reciprocal of a solution of the one-loop renormalisation-group equation is affine in the
evolution variable with slope `β₀`. This is the separation of variables behind
`IsOneLoopRGSolution.eq_oneLoopCoupling`. -/
theorem IsOneLoopRGSolution.inv_eq {A B t₀ : ℝ} {f : ℝ → ℝ}
    (hf : IsOneLoopRGSolution β₀ (Ioo A B) f) (ht₀ : t₀ ∈ Ioo A B) (h₀ : f t₀ ≠ 0) :
    ∀ t ∈ Ioo A B, (f t)⁻¹ = (f t₀)⁻¹ + β₀ * (t - t₀) := by
  have hne := hf.ne_zero ht₀ h₀
  have hinv : ∀ t ∈ Ioo A B, HasDerivAt (fun u => (f u)⁻¹) β₀ t := by
    intro t ht
    have h := (hf t ht).inv (hne t ht)
    have hfne := hne t ht
    have key : -(-β₀ * f t ^ 2) / f t ^ 2 = β₀ := by field_simp
    rwa [key] at h
  have haff : ∀ u : ℝ, HasDerivAt (fun v => (f t₀)⁻¹ + β₀ * (v - t₀)) β₀ u := fun u => by
    simpa using (((hasDerivAt_id u).sub_const t₀).const_mul β₀).const_add ((f t₀)⁻¹)
  exact fun t ht => isOpen_Ioo.eqOn_of_deriv_eq isPreconnected_Ioo
    (fun u hu => (hinv u hu).differentiableAt.differentiableWithinAt)
    (fun u _ => (haff u).differentiableAt.differentiableWithinAt)
    (fun u hu => ((hinv u hu).deriv).trans ((haff u).deriv).symm) ht₀ (by simp) ht

/-- **Uniqueness of the one-loop running coupling.** A solution of `da/dt = -β₀ a²` on an open
interval that is nonzero at a point `t₀` of the interval is the one-loop coupling with reference
value its own value at `t₀`. Together with `isOneLoopRGSolution_oneLoopCoupling` this determines
the one-loop coupling completely. -/
theorem IsOneLoopRGSolution.eq_oneLoopCoupling {A B t₀ : ℝ} {f : ℝ → ℝ}
    (hf : IsOneLoopRGSolution β₀ (Ioo A B) f) (ht₀ : t₀ ∈ Ioo A B) (h₀ : f t₀ ≠ 0) :
    ∀ t ∈ Ioo A B, f t = oneLoopCoupling β₀ (f t₀) (t - t₀) := by
  intro t ht
  have h := hf.inv_eq ht₀ h₀ t ht
  have hkey : (f t₀)⁻¹ + β₀ * (t - t₀) = (1 + β₀ * f t₀ * (t - t₀)) / f t₀ := by
    field_simp
  rw [hkey] at h
  rw [oneLoopCoupling_def, ← inv_inv (f t), h, inv_div]

/-- **The one-loop solution does not extend past its Landau time.** A solution of `da/dt = -β₀ a²`
on an open interval, nonzero at a point `t₀` of the interval, does not have the Landau time of its
value at `t₀` in that interval: the truncated equation has no solution there, so the divergence of
`tendsto_oneLoopCoupling_nhdsGT_landauTime` cannot be removed by continuing the solution
differently. -/
theorem IsOneLoopRGSolution.add_landauTime_notMem {A B t₀ : ℝ} {f : ℝ → ℝ}
    (hf : IsOneLoopRGSolution β₀ (Ioo A B) f) (hβ : β₀ ≠ 0) (ht₀ : t₀ ∈ Ioo A B) (h₀ : f t₀ ≠ 0) :
    t₀ + landauTime β₀ (f t₀) ∉ Ioo A B := by
  intro hmem
  have hne := hf.ne_zero ht₀ h₀ _ hmem
  have h := hf.inv_eq ht₀ h₀ _ hmem
  refine hne (inv_eq_zero.1 ?_)
  rw [h, landauTime_def]
  field_simp
  ring

/-! ### Asymptotic freedom -/

/-- Above its Landau time, a one-loop coupling with `β₀ > 0` and positive reference value is
positive. -/
theorem oneLoopCoupling_pos (hβ : 0 < β₀) (ha : 0 < a₀) (ht : landauTime β₀ a₀ < t) :
    0 < oneLoopCoupling β₀ a₀ t := by
  rw [oneLoopCoupling_def]
  exact div_pos ha ((landauTime_lt_iff (mul_pos hβ ha)).1 ht)

/-- **The one-loop coupling decreases with the scale.** For `β₀ > 0` and a positive reference
value, the coupling is strictly decreasing in `t = log (Q² / μ₀²)` above its Landau time. -/
theorem strictAntiOn_oneLoopCoupling (hβ : 0 < β₀) (ha : 0 < a₀) :
    StrictAntiOn (oneLoopCoupling β₀ a₀) (Ioi (landauTime β₀ a₀)) := by
  intro x hx y _ hxy
  have hβa := mul_pos hβ ha
  rw [oneLoopCoupling_def, oneLoopCoupling_def]
  refine div_lt_div_of_pos_left ha ((landauTime_lt_iff hβa).1 hx) ?_
  have := mul_lt_mul_of_pos_left hxy hβa
  linarith

/-- **Asymptotic freedom at one loop.** For `β₀ > 0` and a positive reference value, the one-loop
coupling tends to zero as the scale grows. -/
theorem tendsto_oneLoopCoupling_atTop_zero (hβ : 0 < β₀) (ha : 0 < a₀) :
    Tendsto (oneLoopCoupling β₀ a₀) atTop (𝓝 0) := by
  have h : Tendsto (fun u : ℝ => 1 + β₀ * a₀ * u) atTop atTop :=
    tendsto_atTop_add_const_left _ 1 (tendsto_id.const_mul_atTop (mul_pos hβ ha))
  exact Tendsto.congr (fun u => (oneLoopCoupling_def β₀ a₀ u).symm) (h.const_div_atTop a₀)

/-- The exact remainder of the leading asymptotics `1 / (β₀ t)` of the one-loop coupling. -/
theorem oneLoopCoupling_sub_inv (hβ : β₀ ≠ 0) (ht : t ≠ 0) (h : 1 + β₀ * a₀ * t ≠ 0) :
    oneLoopCoupling β₀ a₀ t - (β₀ * t)⁻¹ = -(β₀ * t * (1 + β₀ * a₀ * t))⁻¹ := by
  -- `field_simp` commutes the two factors in the denominator, so it needs `h` in that form.
  have h' : 1 + a₀ * β₀ * t ≠ 0 := by rwa [mul_comm a₀ β₀]
  rw [oneLoopCoupling_def]
  field_simp
  ring

/-- **The rate of asymptotic freedom.** For `β₀ > 0` and a positive reference value the one-loop
coupling is `1 / (β₀ t) + O(t⁻²)`: the leading behaviour is independent of the reference value,
which enters first at second order. -/
theorem isBigO_oneLoopCoupling_sub_inv (hβ : 0 < β₀) (ha : 0 < a₀) :
    (fun t => oneLoopCoupling β₀ a₀ t - (β₀ * t)⁻¹) =O[atTop] fun t : ℝ => (t ^ 2)⁻¹ := by
  rw [isBigO_iff]
  refine ⟨(β₀ ^ 2 * a₀)⁻¹, ?_⟩
  filter_upwards [eventually_gt_atTop 0] with t ht
  have hβt : 0 < β₀ * t := mul_pos hβ ht
  have hD : 0 < 1 + β₀ * a₀ * t := by
    have := mul_pos (mul_pos hβ ha) ht
    linarith
  have hpos : (0 : ℝ) < β₀ ^ 2 * a₀ * t ^ 2 :=
    mul_pos (mul_pos (pow_pos hβ 2) ha) (pow_pos ht 2)
  rw [oneLoopCoupling_sub_inv hβ.ne' ht.ne' hD.ne', Real.norm_eq_abs, Real.norm_eq_abs, abs_neg,
    abs_of_nonneg (inv_nonneg.2 (mul_pos hβt hD).le), abs_of_nonneg (inv_nonneg.2 (by positivity)),
    ← mul_inv, inv_le_inv₀ (mul_pos hβt hD) hpos]
  nlinarith

/-- **The Landau pole of the one-loop coupling.** For `β₀ > 0` and a positive reference value the
one-loop coupling diverges as the Landau time is approached from above. -/
theorem tendsto_oneLoopCoupling_nhdsGT_landauTime (hβ : 0 < β₀) (ha : 0 < a₀) :
    Tendsto (oneLoopCoupling β₀ a₀) (𝓝[>] landauTime β₀ a₀) atTop := by
  have hmap : Tendsto (fun u => β₀ * (u - landauTime β₀ a₀)) (𝓝[>] landauTime β₀ a₀) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have hc : Continuous fun u : ℝ => β₀ * (u - landauTime β₀ a₀) :=
        continuous_const.mul (continuous_id.sub continuous_const)
      simpa using (hc.tendsto (landauTime β₀ a₀)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with u hu
      exact mul_pos hβ (sub_pos.2 hu)
  exact Tendsto.congr (fun u => (oneLoopCoupling_eq_inv hβ.ne' ha.ne' u).symm)
    (tendsto_inv_nhdsGT_zero.comp hmap)

/-! ### Changing the reference scale -/

/-- **Changing the reference scale.** Re-referencing the one-loop coupling at `t = s`, with the
value it takes there, gives the same function of the evolution variable. -/
theorem oneLoopCoupling_oneLoopCoupling_sub (h : 1 + β₀ * a₀ * s ≠ 0) :
    oneLoopCoupling β₀ (oneLoopCoupling β₀ a₀ s) (t - s) = oneLoopCoupling β₀ a₀ t := by
  have key : (1 : ℝ) + β₀ * oneLoopCoupling β₀ a₀ s * (t - s)
      = (1 + β₀ * a₀ * t) / (1 + β₀ * a₀ * s) := by
    rw [oneLoopCoupling_def]
    field_simp
    ring
  rw [oneLoopCoupling_def, key, oneLoopCoupling_def β₀ a₀ s, oneLoopCoupling_def β₀ a₀ t]
  rcases eq_or_ne (1 + β₀ * a₀ * t) 0 with ht | ht
  · simp [ht]
  · rw [div_div_div_cancel_right₀ h]

/-- **The Landau time does not depend on the reference scale.** Re-referencing the one-loop
coupling at `t = s` shifts its Landau time by exactly `s`, so the time at which the coupling
diverges is the same in both parametrisations. -/
theorem landauTime_oneLoopCoupling (hβ : β₀ ≠ 0) (ha : a₀ ≠ 0) (s : ℝ) :
    s + landauTime β₀ (oneLoopCoupling β₀ a₀ s) = landauTime β₀ a₀ := by
  have key : (β₀ * oneLoopCoupling β₀ a₀ s)⁻¹ = (1 + β₀ * a₀ * s) / (β₀ * a₀) := by
    rw [oneLoopCoupling_def, mul_div_assoc', inv_div]
  rw [landauTime_def, landauTime_def, key]
  field_simp
  ring

/-! ### The scale form -/

/-- The Landau scale `Λ² = μ₀² exp (t_Λ)` of the one-loop coupling with reference value `a₀` at
the reference scale `μ₀²`: the scale at which the one-loop coupling diverges. -/
def landauScaleSq (β₀ a₀ μ₀sq : ℝ) : ℝ := μ₀sq * Real.exp (landauTime β₀ a₀)

theorem landauScaleSq_def (β₀ a₀ μ₀sq : ℝ) :
    landauScaleSq β₀ a₀ μ₀sq = μ₀sq * Real.exp (landauTime β₀ a₀) :=
  (rfl)

/-- The Landau scale of a positive reference scale is positive. -/
theorem landauScaleSq_pos (β₀ a₀ : ℝ) (hμ : 0 < μ₀sq) : 0 < landauScaleSq β₀ a₀ μ₀sq := by
  rw [landauScaleSq_def]
  positivity

/-- **The one-loop coupling in terms of its Landau scale.** Eliminating the reference value in
favour of `Λ²` turns the solution into `a(Q²) = 1 / (β₀ log (Q² / Λ²))`. -/
theorem oneLoopCoupling_log_eq_inv (hβ : β₀ ≠ 0) (ha : a₀ ≠ 0) (hμ : 0 < μ₀sq) (hQ : 0 < Q2) :
    oneLoopCoupling β₀ a₀ (Real.log (Q2 / μ₀sq))
      = (β₀ * Real.log (Q2 / landauScaleSq β₀ a₀ μ₀sq))⁻¹ := by
  have hlog : Real.log (Q2 / landauScaleSq β₀ a₀ μ₀sq)
      = Real.log (Q2 / μ₀sq) - landauTime β₀ a₀ := by
    rw [landauScaleSq_def, Real.log_div hQ.ne' (by positivity),
      Real.log_mul hμ.ne' (Real.exp_ne_zero _), Real.log_exp, Real.log_div hQ.ne' hμ.ne']
    ring
  rw [oneLoopCoupling_eq_inv hβ ha, hlog]

/-- **The Landau scale does not depend on the reference scale.** Re-referencing the one-loop
coupling at the scale `μ₁²`, with the value it takes there, leaves `Λ²` unchanged. -/
theorem landauScaleSq_oneLoopCoupling (hβ : β₀ ≠ 0) (ha : a₀ ≠ 0) (hμ₀ : 0 < μ₀sq)
    (hμ₁ : 0 < μ₁sq) :
    landauScaleSq β₀ (oneLoopCoupling β₀ a₀ (Real.log (μ₁sq / μ₀sq))) μ₁sq
      = landauScaleSq β₀ a₀ μ₀sq := by
  have hshift := landauTime_oneLoopCoupling hβ ha (Real.log (μ₁sq / μ₀sq))
  have hL : landauTime β₀ (oneLoopCoupling β₀ a₀ (Real.log (μ₁sq / μ₀sq)))
      = landauTime β₀ a₀ - Real.log (μ₁sq / μ₀sq) := by linarith
  rw [landauScaleSq_def, landauScaleSq_def, hL, Real.exp_sub,
    Real.exp_log (div_pos hμ₁ hμ₀)]
  field_simp

/-! ### The QCD coupling -/

section QCD

open EpsilonEridani.QFT.QCD

/-- **The one-loop coupling of an `SU(N_c)` gauge theory decreases with the scale**, in the
asymptotically free flavour window `2 n_f < 11 N_c`; for `N_c = 3` this is `n_f < 16.5`, so every
physical flavour number. -/
theorem strictAntiOn_oneLoopCoupling_beta0_suN {nC nF : ℝ} (h : 2 * nF < 11 * nC)
    (ha : 0 < a₀) :
    StrictAntiOn (oneLoopCoupling (beta0 (suNColorFactors nC nF)) a₀)
      (Ioi (landauTime (beta0 (suNColorFactors nC nF)) a₀)) :=
  strictAntiOn_oneLoopCoupling (isAsymptoticallyFree_suNColorFactors nC nF h) ha

/-- **Asymptotic freedom of an `SU(N_c)` gauge theory at one loop**, in the flavour window
`2 n_f < 11 N_c`. -/
theorem tendsto_oneLoopCoupling_beta0_suN_atTop_zero {nC nF : ℝ} (h : 2 * nF < 11 * nC)
    (ha : 0 < a₀) :
    Tendsto (oneLoopCoupling (beta0 (suNColorFactors nC nF)) a₀) atTop (𝓝 0) :=
  tendsto_oneLoopCoupling_atTop_zero (isAsymptoticallyFree_suNColorFactors nC nF h) ha

end QCD

end Evolution
end Factorization
end QFT
end EpsilonEridani
