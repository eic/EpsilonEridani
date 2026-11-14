/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.ODE.Basic
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
that it is a solution (`hasDerivAt_oneLoopCoupling`), that on an open connected set every
solution is the one of these referenced at any point of the set
(`IsOneLoopRGSolution.eqOn_oneLoopCoupling`), and the three qualitative facts the truncation is
used for: the coupling decreases with the scale and tends to zero
(`strictAntiOn_oneLoopCoupling`, `tendsto_oneLoopCoupling_atTop_zero`) at the rate
`a(t) = 1/(β₀ t) + O(t⁻²)` (`isBigO_oneLoopCoupling_sub_inv`), and it blows up at the finite value
`landauLogScale β₀ a₀ = -(β₀ a₀)⁻¹` of the evolution variable
(`tendsto_oneLoopCoupling_nhdsGT_landauLogScale`). No nonzero solution has its own Landau
log-scale in its domain, so this solution does not continue through it
(`IsOneLoopRGSolution.add_landauLogScale_notMem`,
`IsOneLoopRGSolution.subset_Ioi_add_landauLogScale`). The last is a property of the truncation,
not of QCD.

`landauLogScale` is the `Λ` parameter of the one-loop coupling, expressed in the evolution
variable: it is a derived quantity, not an independent one. Re-referencing the coupling at
`t = u` shifts it by `-u`, so that it names the same point of the scale axis
(`add_landauLogScale_oneLoopCoupling`), and the scale `Λ² = μ₀² exp (landauLogScale β₀ a₀)` itself
does not depend on which scale is taken as the reference (`landauScaleSq_oneLoopCoupling`).
Eliminating `a₀` in favour of it turns the solution into the familiar
`a(Q²) = 1 / (β₀ log (Q² / Λ²))` (`oneLoopCoupling_log_eq_inv`).

The coupling here is `a₄` as a function of the evolution variable `t`, not `α_s` as a function of
`Q²`; it is a different object from `EpsilonEridani.QFT.QCD.oneLoopAlphaS`, which is a regularised
proxy, total in `Q²` and `Λ²` by construction and therefore not a solution of the equation above.
For the same reason `oneLoopCoupling β₀ a₀` is not an `Evolution.RunningCoupling`, although both
are functions `ℝ → ℝ`: that type is `α_s` as a function of `Q²`, so `oneLoopCoupling β₀ a₀` must
not be supplied to `dglapRhsLogScale` or `IsDGLAPLogScaleEquation`.

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

/-- The reciprocal of the one-loop coupling is affine in the evolution variable with slope `β₀`.
At the Landau log-scale both sides are `0`. -/
theorem inv_oneLoopCoupling (β₀ : ℝ) (ha : a₀ ≠ 0) (t : ℝ) :
    (oneLoopCoupling β₀ a₀ t)⁻¹ = a₀⁻¹ + β₀ * t := by
  rw [oneLoopCoupling_def, inv_div]
  field_simp

/-- The Landau log-scale of the one-loop coupling: for `β₀ a₀ ≠ 0`, the value `-(β₀ a₀)⁻¹` of
the evolution variable at which the denominator of `oneLoopCoupling β₀ a₀` vanishes
(`one_add_mul_eq_zero_iff_eq_landauLogScale`); for `β₀ a₀ = 0` the denominator never vanishes and
the value `0` is junk. This is the `Λ` parameter of the one-loop coupling in the evolution
variable, as a quantity derived from the reference value `a₀` rather than an independent
parameter; see `landauScaleSq` for the scale itself. -/
def landauLogScale (β₀ a₀ : ℝ) : ℝ := -(β₀ * a₀)⁻¹

theorem landauLogScale_def (β₀ a₀ : ℝ) : landauLogScale β₀ a₀ = -(β₀ * a₀)⁻¹ :=
  (rfl)

/-- The denominator of the one-loop coupling vanishes at the Landau log-scale. -/
@[simp]
theorem one_add_mul_landauLogScale_eq_zero (h : β₀ * a₀ ≠ 0) :
    1 + β₀ * a₀ * landauLogScale β₀ a₀ = 0 := by
  rw [landauLogScale_def, mul_neg, mul_inv_cancel₀ h]
  norm_num

/-- For `β₀ a₀ ≠ 0` the denominator of the one-loop coupling vanishes exactly at the Landau
log-scale. -/
theorem one_add_mul_eq_zero_iff_eq_landauLogScale (h : β₀ * a₀ ≠ 0) :
    1 + β₀ * a₀ * t = 0 ↔ t = landauLogScale β₀ a₀ := by
  refine ⟨fun ht => mul_left_cancel₀ h ?_, fun ht => ht ▸ one_add_mul_landauLogScale_eq_zero h⟩
  rw [landauLogScale_def, mul_neg, mul_inv_cancel₀ h]
  linarith

/-- For a positive `β₀ a₀` the Landau log-scale is negative: the one-loop coupling diverges at a
finite scale *below* the reference scale. -/
theorem landauLogScale_neg (h : 0 < β₀ * a₀) : landauLogScale β₀ a₀ < 0 := by
  rw [landauLogScale_def, neg_lt_zero]
  exact inv_pos.2 h

/-- For a positive `β₀ a₀` the denominator of the one-loop coupling is positive exactly above the
Landau log-scale. -/
theorem landauLogScale_lt_iff (h : 0 < β₀ * a₀) :
    landauLogScale β₀ a₀ < t ↔ 0 < 1 + β₀ * a₀ * t := by
  have key : β₀ * a₀ * landauLogScale β₀ a₀ = -1 := by
    linarith [one_add_mul_landauLogScale_eq_zero h.ne']
  constructor <;> intro ht <;> nlinarith

/-- The one-loop coupling with the reference value eliminated in favour of the Landau log-scale:
`a(t) = 1 / (β₀ (t - t_Λ))`. -/
theorem oneLoopCoupling_eq_inv (hβ : β₀ ≠ 0) (ha : a₀ ≠ 0) (t : ℝ) :
    oneLoopCoupling β₀ a₀ t = (β₀ * (t - landauLogScale β₀ a₀))⁻¹ := by
  rw [← inv_inv (oneLoopCoupling β₀ a₀ t), inv_oneLoopCoupling β₀ ha, landauLogScale_def,
    sub_neg_eq_add, mul_add, mul_inv, mul_inv_cancel_left₀ hβ, add_comm]

/-! ### The renormalisation-group equation -/

/-- `IsOneLoopRGSolution β₀ s f` says that `f` solves the one-loop renormalisation-group equation
`da/dt = -β₀ a²` on `s`, where `t = log (Q² / μ₀²)`: it is an integral curve on `s` of the
autonomous vector field `a ↦ -β₀ a²` (`isOneLoopRGSolution_iff`), so Mathlib's
`IsIntegralCurveOn` API applies to it. On an open connected `s`, every solution is a one-loop
coupling of `oneLoopCoupling`, by `isOneLoopRGSolution_oneLoopCoupling_Ioi` and
`IsOneLoopRGSolution.eqOn_oneLoopCoupling`. -/
def IsOneLoopRGSolution (β₀ : ℝ) (s : Set ℝ) (f : ℝ → ℝ) : Prop :=
  IsIntegralCurveOn f (fun _ a => -β₀ * a ^ 2) s

theorem isOneLoopRGSolution_iff :
    IsOneLoopRGSolution β₀ s f ↔ IsIntegralCurveOn f (fun _ a => -β₀ * a ^ 2) s :=
  Iff.rfl

/-- The zero function solves the one-loop renormalisation-group equation; by
`IsOneLoopRGSolution.ne_zero` it is the only solution on an open connected set that vanishes
somewhere on the set. -/
theorem isOneLoopRGSolution_zero (β₀ : ℝ) (s : Set ℝ) : IsOneLoopRGSolution β₀ s fun _ => 0 :=
  isOneLoopRGSolution_iff.2 fun t _ => by simpa using hasDerivWithinAt_const t s (0 : ℝ)

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
  isOneLoopRGSolution_iff.2 fun _ ht => (hasDerivAt_oneLoopCoupling β₀ a₀ ht).hasDerivWithinAt

/-- The one-loop coupling solves the one-loop renormalisation-group equation on the whole half
line above its Landau log-scale, which for `β₀, a₀ > 0` is its maximal domain by
`IsOneLoopRGSolution.subset_Ioi_add_landauLogScale`. -/
theorem isOneLoopRGSolution_oneLoopCoupling_Ioi (h : 0 < β₀ * a₀) :
    IsOneLoopRGSolution β₀ (Ioi (landauLogScale β₀ a₀)) (oneLoopCoupling β₀ a₀) :=
  isOneLoopRGSolution_iff.2 <|
    (isOneLoopRGSolution_iff.1 (isOneLoopRGSolution_oneLoopCoupling β₀ a₀)).mono fun _ ht =>
      ((landauLogScale_lt_iff h).1 ht).ne'

/-- An open connected subset of `ℝ` containing two points contains a compact interval whose
interior contains both. -/
theorem exists_Icc_subset_of_isOpen_isPreconnected {x y : ℝ} (hs : IsOpen s)
    (hs' : IsPreconnected s) (hx : x ∈ s) (hy : y ∈ s) :
    ∃ a b : ℝ, Icc a b ⊆ s ∧ x ∈ Ioo a b ∧ y ∈ Ioo a b := by
  obtain ⟨a₁, b₁, -, hn₁, hsub₁⟩ := exists_Icc_mem_subset_of_mem_nhds (hs.mem_nhds hx)
  obtain ⟨a₂, b₂, -, hn₂, hsub₂⟩ := exists_Icc_mem_subset_of_mem_nhds (hs.mem_nhds hy)
  rw [← mem_interior_iff_mem_nhds, interior_Icc] at hn₁ hn₂
  have hmin : min a₁ a₂ ∈ s := by
    rcases min_choice a₁ a₂ with h | h <;> rw [h]
    exacts [hsub₁ (left_mem_Icc.2 (hn₁.1.trans hn₁.2).le),
      hsub₂ (left_mem_Icc.2 (hn₂.1.trans hn₂.2).le)]
  have hmax : max b₁ b₂ ∈ s := by
    rcases max_choice b₁ b₂ with h | h <;> rw [h]
    exacts [hsub₁ (right_mem_Icc.2 (hn₁.1.trans hn₁.2).le),
      hsub₂ (right_mem_Icc.2 (hn₂.1.trans hn₂.2).le)]
  exact ⟨_, _, hs'.ordConnected.out hmin hmax,
    ⟨(min_le_left _ _).trans_lt hn₁.1, hn₁.2.trans_le (le_max_left _ _)⟩,
    ⟨(min_le_right _ _).trans_lt hn₂.1, hn₂.2.trans_le (le_max_right _ _)⟩⟩

/-- On the closed ball `[-R, R]` the map `x ↦ c x²` is Lipschitz with constant `2 |c| R`; for
`c = -β₀` it is the right-hand side of the one-loop renormalisation-group equation. -/
theorem lipschitzOnWith_mul_sq {c R : ℝ} (hR : 0 ≤ R) :
    LipschitzOnWith (Real.toNNReal (2 * |c| * R)) (fun x : ℝ => c * x ^ 2) (Icc (-R) R) := by
  have hderiv : ∀ x : ℝ, HasDerivAt (fun y : ℝ => c * y ^ 2) (2 * c * x) x := fun x =>
    ((hasDerivAt_pow 2 x).const_mul c).congr_deriv (by push_cast; ring)
  refine (convex_Icc (-R) R).lipschitzOnWith_of_nnnorm_deriv_le
    (fun x _ => (hderiv x).differentiableAt) fun x hx => ?_
  have hx' : |x| ≤ R := abs_le.2 ⟨hx.1, hx.2⟩
  rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ (mul_nonneg (by positivity) hR),
    (hderiv x).deriv]
  calc ‖2 * c * x‖ = 2 * |c| * |x| := by
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_two]
    _ ≤ 2 * |c| * R := by gcongr

/-- A solution of the one-loop renormalisation-group equation on an open connected set that is
nonzero somewhere on the set is nonzero everywhere on it: a coupling obeying the one-loop equation
cannot reach zero at a finite scale. The other case is `isOneLoopRGSolution_zero`. -/
theorem IsOneLoopRGSolution.ne_zero {t₀ : ℝ} (hf : IsOneLoopRGSolution β₀ s f) (hs : IsOpen s)
    (hs' : IsPreconnected s) (ht₀ : t₀ ∈ s) (h₀ : f t₀ ≠ 0) :
    ∀ t ∈ s, f t ≠ 0 := by
  intro t₁ ht₁ hzero
  have hd : ∀ {x}, x ∈ s → HasDerivAt f (-β₀ * f x ^ 2) x := fun hx =>
    (isOneLoopRGSolution_iff.1 hf _ hx).hasDerivAt (hs.mem_nhds hx)
  -- Work on a compact interval `[a, b] ⊆ s` whose interior contains `t₀` and `t₁`.
  obtain ⟨a, b, hsub, ht₀', ht₁'⟩ := exists_Icc_subset_of_isOpen_isPreconnected hs hs' ht₀ ht₁
  have hcont : ContinuousOn f (Icc a b) := fun x hx =>
    (hd (hsub hx)).continuousAt.continuousWithinAt
  -- `f` is bounded on `[a, b]`, and on a bounded set `x ↦ -β₀ x²` is Lipschitz, so Mathlib's
  -- uniqueness for Lipschitz right-hand sides applies with the zero solution.
  obtain ⟨R, hR⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  have hR0 : 0 ≤ R := le_trans (norm_nonneg _) (hR t₀ (Ioo_subset_Icc_self ht₀'))
  have hmem : ∀ x ∈ Icc a b, f x ∈ Icc (-R) R := fun x hx =>
    mem_Icc.2 (abs_le.1 (by simpa only [Real.norm_eq_abs] using hR x hx))
  have heq := ODE_solution_unique_of_mem_Icc (v := fun _ x => -β₀ * x ^ 2)
    (s := fun _ => Icc (-R) R) (f := f) (g := fun _ => 0)
    (fun _ _ => lipschitzOnWith_mul_sq hR0) ht₁' hcont
    (fun x hx => hd (hsub (Ioo_subset_Icc_self hx)))
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
    exact (((isOneLoopRGSolution_iff.1 hf t ht).hasDerivAt (hs.mem_nhds ht)).inv hfne).congr_deriv
      (by field_simp)
  have haff : ∀ x : ℝ, HasDerivAt (fun y => (f t₀)⁻¹ + β₀ * (y - t₀)) β₀ x := fun x => by
    simpa using (((hasDerivAt_id x).sub_const t₀).const_mul β₀).const_add ((f t₀)⁻¹)
  exact hs.eqOn_of_deriv_eq hs'
    (fun x hx => (hinv x hx).differentiableAt.differentiableWithinAt)
    (fun x _ => (haff x).differentiableAt.differentiableWithinAt)
    (fun x hx => ((hinv x hx).deriv).trans ((haff x).deriv).symm) ht₀ (by simp)

/-- **Uniqueness of the one-loop running coupling.** A solution of `da/dt = -β₀ a²` on an open
connected set agrees on that set with the one-loop coupling whose reference value is its own value
at any point `t₀` of the set. Together with `isOneLoopRGSolution_oneLoopCoupling_Ioi` this
determines the one-loop coupling completely. -/
theorem IsOneLoopRGSolution.eqOn_oneLoopCoupling {t₀ : ℝ} (hf : IsOneLoopRGSolution β₀ s f)
    (hs : IsOpen s) (hs' : IsPreconnected s) (ht₀ : t₀ ∈ s) :
    EqOn f (fun t => oneLoopCoupling β₀ (f t₀) (t - t₀)) s := by
  intro t ht
  rcases eq_or_ne (f t₀) 0 with h₀ | h₀
  · simp only [h₀, oneLoopCoupling_def, zero_div]
    by_contra h
    exact hf.ne_zero hs hs' ht h t₀ ht₀ h₀
  · exact inv_injective ((hf.inv_eqOn hs hs' ht₀ h₀ ht).trans (inv_oneLoopCoupling β₀ h₀ _).symm)

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

/-- **The one-loop solution does not extend below its Landau log-scale.** For `β₀ > 0`, a solution
of `da/dt = -β₀ a²` on an open connected set, positive at a point `t₀` of the set, lives strictly
above the Landau log-scale of its value at `t₀`. -/
theorem IsOneLoopRGSolution.subset_Ioi_add_landauLogScale {t₀ : ℝ}
    (hf : IsOneLoopRGSolution β₀ s f) (hs : IsOpen s) (hs' : IsPreconnected s) (hβ : 0 < β₀)
    (ht₀ : t₀ ∈ s) (h₀ : 0 < f t₀) :
    s ⊆ Ioi (t₀ + landauLogScale β₀ (f t₀)) := by
  intro x hx
  by_contra hle
  have hlt : t₀ + landauLogScale β₀ (f t₀) < t₀ := by
    linarith [landauLogScale_neg (mul_pos hβ h₀)]
  exact hf.add_landauLogScale_notMem hs hs' hβ.ne' ht₀ h₀.ne'
    (hs'.ordConnected.out hx ht₀ ⟨not_lt.1 hle, hlt.le⟩)

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

/-- **Asymptotic freedom at one loop.** For a positive `β₀ a₀`, the one-loop coupling tends to
zero as the scale grows. -/
theorem tendsto_oneLoopCoupling_atTop_zero (h : 0 < β₀ * a₀) :
    Tendsto (oneLoopCoupling β₀ a₀) atTop (𝓝 0) := by
  have h : Tendsto (fun x : ℝ => 1 + β₀ * a₀ * x) atTop atTop :=
    tendsto_atTop_add_const_left _ 1 (tendsto_id.const_mul_atTop h)
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
@[simp]
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

/-- **Re-referencing shifts the Landau log-scale.** Re-referencing the one-loop coupling at
`t = u` shifts its Landau log-scale by `-u`, so `u + t_Λ(a(u))` and `t_Λ(a₀)` are the same point
of the scale axis: the coupling diverges at the same scale in both parametrisations. -/
@[simp]
theorem add_landauLogScale_oneLoopCoupling (hβ : β₀ ≠ 0) (ha : a₀ ≠ 0) (u : ℝ) :
    u + landauLogScale β₀ (oneLoopCoupling β₀ a₀ u) = landauLogScale β₀ a₀ := by
  rw [landauLogScale_def, landauLogScale_def, mul_inv, inv_oneLoopCoupling β₀ ha, mul_add,
    inv_mul_cancel_left₀ hβ, mul_inv]
  ring

/-! ### The scale form -/

/-- The Landau scale `Λ² = μ₀² exp (t_Λ)` of the one-loop coupling with reference value `a₀` at
the reference scale `μ₀²`: for `β₀, a₀ > 0`, the scale at which the one-loop coupling diverges
(`tendsto_oneLoopCoupling_nhdsGT_landauLogScale`). For `β₀ a₀ = 0` the coupling does not diverge
and the value `μ₀²` is junk. -/
def landauScaleSq (β₀ a₀ μ₀sq : ℝ) : ℝ := μ₀sq * Real.exp (landauLogScale β₀ a₀)

theorem landauScaleSq_def (β₀ a₀ μ₀sq : ℝ) :
    landauScaleSq β₀ a₀ μ₀sq = μ₀sq * Real.exp (landauLogScale β₀ a₀) :=
  (rfl)

/-- The Landau scale of a positive reference scale is positive. -/
theorem landauScaleSq_pos (β₀ a₀ : ℝ) (hμ : 0 < μ₀sq) : 0 < landauScaleSq β₀ a₀ μ₀sq := by
  rw [landauScaleSq_def]
  positivity

/-- **The Landau scale sits at the Landau log-scale.** In the evolution variable of the reference
scale `μ₀²`, the scale `Λ²` sits at `landauLogScale β₀ a₀`. -/
@[simp]
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
@[simp]
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
  tendsto_oneLoopCoupling_atTop_zero (mul_pos (isAsymptoticallyFree_suNColorFactors nC nF h) ha)

end QCD

end Evolution
end Factorization
end QFT
end EpsilonEridani
