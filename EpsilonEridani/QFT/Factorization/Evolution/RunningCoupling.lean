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
import Mathlib.Analysis.Calculus.Deriv.Pow
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
that it is a solution (`hasDerivAt_oneLoopCoupling`), that on an open connected set a solution
which is nonzero at one point of the set is one of these
(`IsOneLoopRGSolution.eqOn_oneLoopCoupling`), and the three qualitative facts the truncation is
used for: the coupling decreases with the scale and tends to zero
(`strictAntiOn_oneLoopCoupling`, `tendsto_oneLoopCoupling_atTop_zero`) at the rate
`a(t) = 1/(β₀ t) + O(t⁻²)` (`isBigO_oneLoopCoupling_sub_inv`), and it blows up at the finite value
`landauLogScale β₀ a₀ = -(β₀ a₀)⁻¹` of the evolution variable, through which no solution of the
truncated equation continues (`tendsto_oneLoopCoupling_nhdsGT_landauLogScale`,
`IsOneLoopRGSolution.add_landauLogScale_notMem`). The last is a property of the truncation, not of
QCD.

`landauLogScale` is the `Λ` parameter of the one-loop coupling, expressed in the evolution
variable: it is a derived quantity, not an independent one, and it does not depend on which scale
is taken as the reference (`add_landauLogScale_oneLoopCoupling`, and
`landauScaleSq_oneLoopCoupling` for the scale `Λ² = μ₀² exp (landauLogScale β₀ a₀)` itself).
Eliminating `a₀` in favour of it turns the solution into the familiar
`a(Q²) = 1 / (β₀ log (Q² / Λ²))` (`oneLoopCoupling_log_eq_inv`).

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

@[expose] public section

noncomputable section

open Asymptotics Filter Set Topology

namespace EpsilonEridani
namespace QFT
namespace Factorization
namespace Evolution

variable {β₀ a₀ t u μ₀sq μ₁sq Q2 : ℝ} {s : Set ℝ} {f : ℝ → ℝ}

/-! ### The solution and its Landau log-scale -/

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

/-- The Landau log-scale of the one-loop coupling: the value `-(β₀ a₀)⁻¹` of the evolution
variable at which the denominator of `oneLoopCoupling β₀ a₀` vanishes. This is the `Λ` parameter
of the one-loop coupling in the evolution variable, as a quantity derived from the reference value
`a₀` rather than an independent parameter; see `landauScaleSq` for the scale itself. -/
def landauLogScale (β₀ a₀ : ℝ) : ℝ := -(β₀ * a₀)⁻¹

theorem landauLogScale_def (β₀ a₀ : ℝ) : landauLogScale β₀ a₀ = -(β₀ * a₀)⁻¹ :=
  (rfl)

/-- The denominator of the one-loop coupling vanishes at the Landau log-scale. -/
theorem one_add_mul_landauLogScale_eq_zero (h : β₀ * a₀ ≠ 0) :
    1 + β₀ * a₀ * landauLogScale β₀ a₀ = 0 := by
  rw [landauLogScale_def, mul_neg, mul_inv_cancel₀ h]
  norm_num

/-- For a positive `β₀` and a positive reference value the Landau log-scale is negative: the
one-loop coupling diverges at a finite scale *below* the reference scale. -/
theorem landauLogScale_neg (hβ : 0 < β₀) (ha : 0 < a₀) : landauLogScale β₀ a₀ < 0 := by
  rw [landauLogScale_def, neg_lt_zero]
  exact inv_pos.2 (mul_pos hβ ha)

/-- For a positive `β₀ a₀` the denominator of the one-loop coupling is positive exactly above the
Landau log-scale. -/
theorem landauLogScale_lt_iff (h : 0 < β₀ * a₀) :
    landauLogScale β₀ a₀ < t ↔ 0 < 1 + β₀ * a₀ * t := by
  have key : β₀ * a₀ * landauLogScale β₀ a₀ = -1 := by
    linarith [one_add_mul_landauLogScale_eq_zero h.ne']
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

/-- The one-loop coupling with the reference value eliminated in favour of the Landau log-scale:
`a(t) = 1 / (β₀ (t - t_Λ))`. -/
theorem oneLoopCoupling_eq_inv (hβ : β₀ ≠ 0) (ha : a₀ ≠ 0) (t : ℝ) :
    oneLoopCoupling β₀ a₀ t = (β₀ * (t - landauLogScale β₀ a₀))⁻¹ := by
  have key : β₀ * (t + (β₀ * a₀)⁻¹) = (1 + β₀ * a₀ * t) / a₀ := by
    field_simp
    ring
  rw [oneLoopCoupling_def, landauLogScale_def, sub_neg_eq_add, key, inv_div]

/-! ### The renormalisation-group equation -/

/-- `IsOneLoopRGSolution β₀ s f` says that `f` solves the one-loop renormalisation-group equation
`da/dt = -β₀ a²` at every point of `s`, where `t = log (Q² / μ₀²)`. On an open connected `s`, a
solution that is nonzero at one point of `s` is a one-loop coupling of `oneLoopCoupling`, by
`isOneLoopRGSolution_oneLoopCoupling_Ioi` and `IsOneLoopRGSolution.eqOn_oneLoopCoupling`. -/
def IsOneLoopRGSolution (β₀ : ℝ) (s : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ t ∈ s, HasDerivAt f (-β₀ * f t ^ 2) t

/-- Being a solution of the one-loop renormalisation-group equation on `s` is having the
equation's derivative at every point of `s`; this is the introduction and elimination rule for
`IsOneLoopRGSolution`. -/
theorem isOneLoopRGSolution_iff :
    IsOneLoopRGSolution β₀ s f ↔ ∀ t ∈ s, HasDerivAt f (-β₀ * f t ^ 2) t :=
  Iff.rfl

/-- A solution of the one-loop renormalisation-group equation has the equation's derivative at
each point of its domain. -/
theorem IsOneLoopRGSolution.hasDerivAt (hf : IsOneLoopRGSolution β₀ s f) (ht : t ∈ s) :
    HasDerivAt f (-β₀ * f t ^ 2) t :=
  hf t ht

/-- A solution of the one-loop renormalisation-group equation on a set is a solution on every
subset of it. -/
theorem IsOneLoopRGSolution.mono {s' : Set ℝ} (hf : IsOneLoopRGSolution β₀ s f) (hsub : s' ⊆ s) :
    IsOneLoopRGSolution β₀ s' f :=
  fun _ ht => hf.hasDerivAt (hsub ht)

/-- **The one-loop renormalisation-group equation.** Away from its Landau log-scale, the one-loop
coupling satisfies `da/dt = -β₀ a²`. -/
theorem hasDerivAt_oneLoopCoupling (β₀ a₀ : ℝ) (h : 1 + β₀ * a₀ * t ≠ 0) :
    HasDerivAt (oneLoopCoupling β₀ a₀) (-β₀ * oneLoopCoupling β₀ a₀ t ^ 2) t := by
  have hd : HasDerivAt (fun x : ℝ => 1 + β₀ * a₀ * x) (β₀ * a₀) t := by
    simpa using ((hasDerivAt_id t).const_mul (β₀ * a₀)).const_add 1
  refine ((hasDerivAt_const t a₀).div hd h).congr_deriv ?_
  rw [oneLoopCoupling_def]
  field_simp
  ring

/-- The one-loop coupling solves the one-loop renormalisation-group equation off its Landau
log-scale. -/
theorem isOneLoopRGSolution_oneLoopCoupling (β₀ a₀ : ℝ) :
    IsOneLoopRGSolution β₀ {t | 1 + β₀ * a₀ * t ≠ 0} (oneLoopCoupling β₀ a₀) :=
  fun _ ht => hasDerivAt_oneLoopCoupling β₀ a₀ ht

/-- The one-loop coupling solves the one-loop renormalisation-group equation on the whole half
line above its Landau log-scale, which for a positive `β₀ a₀` is its maximal domain. -/
theorem isOneLoopRGSolution_oneLoopCoupling_Ioi (h : 0 < β₀ * a₀) :
    IsOneLoopRGSolution β₀ (Ioi (landauLogScale β₀ a₀)) (oneLoopCoupling β₀ a₀) :=
  (isOneLoopRGSolution_oneLoopCoupling β₀ a₀).mono fun _ ht =>
    ((landauLogScale_lt_iff h).1 ht).ne'

/-- A solution of the one-loop renormalisation-group equation on an open connected set that is
nonzero somewhere on the set is nonzero everywhere on it: a coupling obeying the one-loop equation
cannot reach zero at a finite scale. -/
theorem IsOneLoopRGSolution.ne_zero {t₀ : ℝ} (hf : IsOneLoopRGSolution β₀ s f) (hs : IsOpen s)
    (hs' : IsPreconnected s) (ht₀ : t₀ ∈ s) (h₀ : f t₀ ≠ 0) :
    ∀ t ∈ s, f t ≠ 0 := by
  intro t₁ ht₁ hzero
  -- Work on a compact interval `[a, b] ⊆ s` whose interior contains `t₀` and `t₁`: it exists
  -- because `s` is open, so it contains a ball around each of the two points, and connected, so
  -- it contains the interval between the outer endpoints of those balls.
  obtain ⟨a, b, hsub, ht₀', ht₁'⟩ : ∃ a b : ℝ, Icc a b ⊆ s ∧ t₀ ∈ Ioo a b ∧ t₁ ∈ Ioo a b := by
    obtain ⟨ε₀, hε₀, hball₀⟩ := Metric.isOpen_iff.1 hs t₀ ht₀
    obtain ⟨ε₁, hε₁, hball₁⟩ := Metric.isOpen_iff.1 hs t₁ ht₁
    have hpm : ∀ {x ε : ℝ}, 0 < ε → Metric.ball x ε ⊆ s → x - ε / 2 ∈ s ∧ x + ε / 2 ∈ s := by
      intro x ε hε hball
      refine ⟨hball ?_, hball ?_⟩ <;> rw [Real.ball_eq_Ioo] <;> constructor <;> linarith
    obtain ⟨hl₀, hr₀⟩ := hpm hε₀ hball₀
    obtain ⟨hl₁, hr₁⟩ := hpm hε₁ hball₁
    have hmin : min (t₀ - ε₀ / 2) (t₁ - ε₁ / 2) ∈ s := by
      rcases le_total (t₀ - ε₀ / 2) (t₁ - ε₁ / 2) with h | h
      · rwa [min_eq_left h]
      · rwa [min_eq_right h]
    have hmax : max (t₀ + ε₀ / 2) (t₁ + ε₁ / 2) ∈ s := by
      rcases le_total (t₀ + ε₀ / 2) (t₁ + ε₁ / 2) with h | h
      · rwa [max_eq_right h]
      · rwa [max_eq_left h]
    refine ⟨_, _, hs'.ordConnected.out hmin hmax, ⟨?_, ?_⟩, ?_, ?_⟩
    · exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
    · exact lt_of_lt_of_le (by linarith : t₀ < t₀ + ε₀ / 2) (le_max_left _ _)
    · exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
    · exact lt_of_lt_of_le (by linarith : t₁ < t₁ + ε₁ / 2) (le_max_right _ _)
  have hcont : ContinuousOn f (Icc a b) := fun x hx =>
    (hf.hasDerivAt (hsub hx)).continuousAt.continuousWithinAt
  -- `f` is bounded on `[a, b]`, and on a bounded set `x ↦ -β₀ x²` is Lipschitz by the mean value
  -- theorem, so Mathlib's uniqueness for Lipschitz right-hand sides applies with the zero
  -- solution.
  obtain ⟨R, hR⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  have hR0 : 0 ≤ R := le_trans (norm_nonneg _) (hR t₀ (Ioo_subset_Icc_self ht₀'))
  have hmem : ∀ x ∈ Icc a b, f x ∈ Icc (-R) R := fun x hx =>
    mem_Icc.2 (abs_le.1 (by simpa only [Real.norm_eq_abs] using hR x hx))
  have hderiv : ∀ x : ℝ, HasDerivAt (fun y : ℝ => -β₀ * y ^ 2) (-(2 * β₀ * x)) x := fun x =>
    ((hasDerivAt_pow 2 x).const_mul (-β₀)).congr_deriv (by push_cast; ring)
  have hlip : LipschitzOnWith (Real.toNNReal (2 * |β₀| * R)) (fun x : ℝ => -β₀ * x ^ 2)
      (Icc (-R) R) := by
    refine (convex_Icc (-R) R).lipschitzOnWith_of_nnnorm_deriv_le
      (fun x _ => (hderiv x).differentiableAt) fun x hx => ?_
    have hx' : |x| ≤ R := abs_le.2 ⟨hx.1, hx.2⟩
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ (mul_nonneg (by positivity) hR0),
      (hderiv x).deriv]
    calc ‖-(2 * β₀ * x)‖ = 2 * |β₀| * |x| := by
          rw [Real.norm_eq_abs, abs_neg, abs_mul, abs_mul, abs_two]
      _ ≤ 2 * |β₀| * R := by gcongr
  have heq := ODE_solution_unique_of_mem_Icc (v := fun _ x => -β₀ * x ^ 2)
    (s := fun _ => Icc (-R) R) (f := f) (g := fun _ => 0) (fun _ _ => hlip) ht₁' hcont
    (fun x hx => hf.hasDerivAt (hsub (Ioo_subset_Icc_self hx)))
    (fun x hx => hmem x (Ioo_subset_Icc_self hx)) continuousOn_const
    (fun x _ => by simpa using hasDerivAt_const x (0 : ℝ))
    (fun _ _ => mem_Icc.2 ⟨by linarith, hR0⟩) (by simpa using hzero)
  exact h₀ (heq (Ioo_subset_Icc_self ht₀'))

/-- The reciprocal of a solution of the one-loop renormalisation-group equation on an open
connected set is affine in the evolution variable with slope `β₀`. This is the separation of
variables behind `IsOneLoopRGSolution.eqOn_oneLoopCoupling`. -/
theorem IsOneLoopRGSolution.inv_eqOn {t₀ : ℝ} (hf : IsOneLoopRGSolution β₀ s f) (hs : IsOpen s)
    (hs' : IsPreconnected s) (ht₀ : t₀ ∈ s) (h₀ : f t₀ ≠ 0) :
    EqOn (fun t => (f t)⁻¹) (fun t => (f t₀)⁻¹ + β₀ * (t - t₀)) s := by
  have hne := hf.ne_zero hs hs' ht₀ h₀
  have hinv : ∀ t ∈ s, HasDerivAt (fun x => (f x)⁻¹) β₀ t := by
    intro t ht
    have hfne := hne t ht
    exact ((hf.hasDerivAt ht).inv hfne).congr_deriv (by field_simp)
  have haff : ∀ x : ℝ, HasDerivAt (fun y => (f t₀)⁻¹ + β₀ * (y - t₀)) β₀ x := fun x => by
    simpa using (((hasDerivAt_id x).sub_const t₀).const_mul β₀).const_add ((f t₀)⁻¹)
  exact hs.eqOn_of_deriv_eq hs'
    (fun x hx => (hinv x hx).differentiableAt.differentiableWithinAt)
    (fun x _ => (haff x).differentiableAt.differentiableWithinAt)
    (fun x hx => ((hinv x hx).deriv).trans ((haff x).deriv).symm) ht₀ (by simp)

/-- **Uniqueness of the one-loop running coupling.** A solution of `da/dt = -β₀ a²` on an open
connected set that is nonzero at a point `t₀` of the set agrees on that set with the one-loop
coupling whose reference value is its own value at `t₀`. Together with
`isOneLoopRGSolution_oneLoopCoupling_Ioi` this determines the one-loop coupling completely. -/
theorem IsOneLoopRGSolution.eqOn_oneLoopCoupling {t₀ : ℝ} (hf : IsOneLoopRGSolution β₀ s f)
    (hs : IsOpen s) (hs' : IsPreconnected s) (ht₀ : t₀ ∈ s) (h₀ : f t₀ ≠ 0) :
    EqOn f (fun t => oneLoopCoupling β₀ (f t₀) (t - t₀)) s := by
  intro t ht
  have h : (f t)⁻¹ = (f t₀)⁻¹ + β₀ * (t - t₀) := hf.inv_eqOn hs hs' ht₀ h₀ ht
  have hkey : (f t₀)⁻¹ + β₀ * (t - t₀) = (1 + β₀ * f t₀ * (t - t₀)) / f t₀ := by
    field_simp
  rw [hkey] at h
  have key : f t = oneLoopCoupling β₀ (f t₀) (t - t₀) := by
    rw [oneLoopCoupling_def, ← inv_inv (f t), h, inv_div]
  exact key

/-- **The one-loop solution does not extend past its Landau log-scale.** A solution of
`da/dt = -β₀ a²` on an open connected set, nonzero at a point `t₀` of the set, does not have the
Landau log-scale of its value at `t₀` in that set: a solution's domain stops short of its own
Landau log-scale, so the divergence of `tendsto_oneLoopCoupling_nhdsGT_landauLogScale` cannot be
removed by continuing the solution differently. -/
theorem IsOneLoopRGSolution.add_landauLogScale_notMem {t₀ : ℝ} (hf : IsOneLoopRGSolution β₀ s f)
    (hs : IsOpen s) (hs' : IsPreconnected s) (hβ : β₀ ≠ 0) (ht₀ : t₀ ∈ s) (h₀ : f t₀ ≠ 0) :
    t₀ + landauLogScale β₀ (f t₀) ∉ s := by
  intro hmem
  have hne := hf.ne_zero hs hs' ht₀ h₀ _ hmem
  have h : (f (t₀ + landauLogScale β₀ (f t₀)))⁻¹
      = (f t₀)⁻¹ + β₀ * (t₀ + landauLogScale β₀ (f t₀) - t₀) :=
    hf.inv_eqOn hs hs' ht₀ h₀ hmem
  have hzero : 1 + β₀ * f t₀ * landauLogScale β₀ (f t₀) = 0 :=
    one_add_mul_landauLogScale_eq_zero (mul_ne_zero hβ h₀)
  refine hne (inv_eq_zero.1 ?_)
  rw [h]
  field_simp
  linear_combination hzero

/-! ### Asymptotic freedom -/

/-- Above its Landau log-scale, a one-loop coupling with `β₀ > 0` and positive reference value is
positive. -/
theorem oneLoopCoupling_pos (hβ : 0 < β₀) (ha : 0 < a₀) (ht : landauLogScale β₀ a₀ < t) :
    0 < oneLoopCoupling β₀ a₀ t := by
  rw [oneLoopCoupling_def]
  exact div_pos ha ((landauLogScale_lt_iff (mul_pos hβ ha)).1 ht)

/-- **The one-loop coupling decreases with the scale.** For `β₀ > 0` and a positive reference
value, the coupling is strictly decreasing in `t = log (Q² / μ₀²)` above its Landau log-scale. -/
theorem strictAntiOn_oneLoopCoupling (hβ : 0 < β₀) (ha : 0 < a₀) :
    StrictAntiOn (oneLoopCoupling β₀ a₀) (Ioi (landauLogScale β₀ a₀)) := by
  intro x hx y _ hxy
  have hβa := mul_pos hβ ha
  rw [oneLoopCoupling_def, oneLoopCoupling_def]
  refine div_lt_div_of_pos_left ha ((landauLogScale_lt_iff hβa).1 hx) ?_
  have := mul_lt_mul_of_pos_left hxy hβa
  linarith

/-- **Asymptotic freedom at one loop.** For `β₀ > 0` and a positive reference value, the one-loop
coupling tends to zero as the scale grows. -/
theorem tendsto_oneLoopCoupling_atTop_zero (hβ : 0 < β₀) (ha : 0 < a₀) :
    Tendsto (oneLoopCoupling β₀ a₀) atTop (𝓝 0) := by
  have h : Tendsto (fun x : ℝ => 1 + β₀ * a₀ * x) atTop atTop :=
    tendsto_atTop_add_const_left _ 1 (tendsto_id.const_mul_atTop (mul_pos hβ ha))
  exact Tendsto.congr (fun x => (oneLoopCoupling_def β₀ a₀ x).symm) (h.const_div_atTop a₀)

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
  rw [oneLoopCoupling_sub_inv hβ.ne' ht.ne' hD.ne']
  simp only [Real.norm_eq_abs, abs_neg, abs_of_nonneg (inv_nonneg.2 (mul_pos hβt hD).le),
    abs_of_nonneg (inv_nonneg.2 (sq_nonneg t)), ← mul_inv]
  exact (inv_le_inv₀ (mul_pos hβt hD) hpos).2 (by nlinarith)

/-- **The Landau pole of the one-loop coupling.** For `β₀ > 0` and a positive reference value the
one-loop coupling diverges as the Landau log-scale is approached from above. -/
theorem tendsto_oneLoopCoupling_nhdsGT_landauLogScale (hβ : 0 < β₀) (ha : 0 < a₀) :
    Tendsto (oneLoopCoupling β₀ a₀) (𝓝[>] landauLogScale β₀ a₀) atTop := by
  have hmap : Tendsto (fun x => β₀ * (x - landauLogScale β₀ a₀))
      (𝓝[>] landauLogScale β₀ a₀) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have hc : Continuous fun x : ℝ => β₀ * (x - landauLogScale β₀ a₀) :=
        continuous_const.mul (continuous_id.sub continuous_const)
      simpa using (hc.tendsto (landauLogScale β₀ a₀)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact mul_pos hβ (sub_pos.2 hx)
  exact Tendsto.congr (fun x => (oneLoopCoupling_eq_inv hβ.ne' ha.ne' x).symm)
    (tendsto_inv_nhdsGT_zero.comp hmap)

/-! ### Changing the reference scale -/

/-- **Changing the reference scale.** Re-referencing the one-loop coupling at `t = u`, with the
value it takes there, gives the same function of the evolution variable. -/
theorem oneLoopCoupling_oneLoopCoupling_sub (h : 1 + β₀ * a₀ * u ≠ 0) :
    oneLoopCoupling β₀ (oneLoopCoupling β₀ a₀ u) (t - u) = oneLoopCoupling β₀ a₀ t := by
  have key : (1 : ℝ) + β₀ * oneLoopCoupling β₀ a₀ u * (t - u)
      = (1 + β₀ * a₀ * t) / (1 + β₀ * a₀ * u) := by
    rw [oneLoopCoupling_def]
    field_simp
    ring
  rw [oneLoopCoupling_def, key, oneLoopCoupling_def β₀ a₀ u, oneLoopCoupling_def β₀ a₀ t]
  rcases eq_or_ne (1 + β₀ * a₀ * t) 0 with ht | ht
  · simp [ht]
  · rw [div_div_div_cancel_right₀ h]

/-- **The Landau log-scale does not depend on the reference scale.** Re-referencing the one-loop
coupling at `t = u` shifts its Landau log-scale by exactly `u`, so the value of the evolution
variable at which the coupling diverges is the same in both parametrisations. -/
theorem add_landauLogScale_oneLoopCoupling (hβ : β₀ ≠ 0) (ha : a₀ ≠ 0) (u : ℝ) :
    u + landauLogScale β₀ (oneLoopCoupling β₀ a₀ u) = landauLogScale β₀ a₀ := by
  have key : (β₀ * oneLoopCoupling β₀ a₀ u)⁻¹ = (1 + β₀ * a₀ * u) / (β₀ * a₀) := by
    rw [oneLoopCoupling_def, mul_div_assoc', inv_div]
  rw [landauLogScale_def, landauLogScale_def, key]
  field_simp
  ring

/-! ### The scale form -/

/-- The Landau scale `Λ² = μ₀² exp (t_Λ)` of the one-loop coupling with reference value `a₀` at
the reference scale `μ₀²`: the scale at which the one-loop coupling diverges. -/
def landauScaleSq (β₀ a₀ μ₀sq : ℝ) : ℝ := μ₀sq * Real.exp (landauLogScale β₀ a₀)

theorem landauScaleSq_def (β₀ a₀ μ₀sq : ℝ) :
    landauScaleSq β₀ a₀ μ₀sq = μ₀sq * Real.exp (landauLogScale β₀ a₀) :=
  (rfl)

/-- The Landau scale of a positive reference scale is positive. -/
theorem landauScaleSq_pos (β₀ a₀ : ℝ) (hμ : 0 < μ₀sq) : 0 < landauScaleSq β₀ a₀ μ₀sq := by
  rw [landauScaleSq_def]
  positivity

/-- **The Landau scale is the Landau log-scale.** In the evolution variable of the reference scale
`μ₀²`, the scale `Λ²` sits at `landauLogScale β₀ a₀`. -/
theorem log_landauScaleSq_div (β₀ a₀ : ℝ) (hμ : 0 < μ₀sq) :
    Real.log (landauScaleSq β₀ a₀ μ₀sq / μ₀sq) = landauLogScale β₀ a₀ := by
  rw [landauScaleSq_def, mul_comm, mul_div_assoc, div_self hμ.ne', mul_one, Real.log_exp]

/-- **The one-loop coupling in terms of its Landau scale.** Eliminating the reference value in
favour of `Λ²` turns the solution into `a(Q²) = 1 / (β₀ log (Q² / Λ²))`. -/
theorem oneLoopCoupling_log_eq_inv (hβ : β₀ ≠ 0) (ha : a₀ ≠ 0) (hμ : 0 < μ₀sq) (hQ : 0 < Q2) :
    oneLoopCoupling β₀ a₀ (Real.log (Q2 / μ₀sq))
      = (β₀ * Real.log (Q2 / landauScaleSq β₀ a₀ μ₀sq))⁻¹ := by
  have hΛ : 0 < landauScaleSq β₀ a₀ μ₀sq := landauScaleSq_pos β₀ a₀ hμ
  have hlog : Real.log (Q2 / landauScaleSq β₀ a₀ μ₀sq)
      = Real.log (Q2 / μ₀sq) - landauLogScale β₀ a₀ := by
    rw [← log_landauScaleSq_div β₀ a₀ hμ, Real.log_div hQ.ne' hΛ.ne',
      Real.log_div hQ.ne' hμ.ne', Real.log_div hΛ.ne' hμ.ne']
    ring
  rw [oneLoopCoupling_eq_inv hβ ha, hlog]

/-- **The Landau scale does not depend on the reference scale.** Re-referencing the one-loop
coupling at the scale `μ₁²`, with the value it takes there, leaves `Λ²` unchanged. -/
theorem landauScaleSq_oneLoopCoupling (hβ : β₀ ≠ 0) (ha : a₀ ≠ 0) (hμ₀ : 0 < μ₀sq)
    (hμ₁ : 0 < μ₁sq) :
    landauScaleSq β₀ (oneLoopCoupling β₀ a₀ (Real.log (μ₁sq / μ₀sq))) μ₁sq
      = landauScaleSq β₀ a₀ μ₀sq := by
  have hshift := add_landauLogScale_oneLoopCoupling hβ ha (Real.log (μ₁sq / μ₀sq))
  have hL : landauLogScale β₀ (oneLoopCoupling β₀ a₀ (Real.log (μ₁sq / μ₀sq)))
      = landauLogScale β₀ a₀ - Real.log (μ₁sq / μ₀sq) := by linarith
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
      (Ioi (landauLogScale (beta0 (suNColorFactors nC nF)) a₀)) :=
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
