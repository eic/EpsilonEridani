/-
Copyright (c) 2026 The EpsilonEridani contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The EpsilonEridani contributors
-/
module

public import EpsilonEridani.Mathematics.LinearAlgebra.Complex.SkewAdjoint
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Physlib.Particles.FlavorPhysics.CKMMatrix.Basic
public import TauCeti.Analysis.Matrix.UnitaryGroup.Torus

/-!
# The physical parameters of the quark mixing matrix

With `n` generations the charged current couples the up-type quarks to the down-type quarks
through a unitary mixing matrix `V ∈ U(n)`. Redefining the phases of the quark fields,
`uᵢ ↦ e^{iαᵢ} uᵢ` and `dⱼ ↦ e^{-iβⱼ} dⱼ`, leaves the rest of the Lagrangian unchanged and is
compensated by the *rephasing*

`V ↦ diag(e^{iα}) V diag(e^{iβ})`,

the convention of Physlib's `PhaseShiftRelation`. Matrices related by a rephasing describe the
same physics, so the physical parameters of `V` are the directions in `U(n)` transverse to its
rephasing orbit.

This module counts them at the level of tangent spaces. The tangent space of `U(n)` at `V` is
identified with the Lie algebra `𝔲(n)` of skew-Hermitian matrices by left translation,
`X ↦ V⁻¹ X`, and the infinitesimal rephasing at `V` becomes the real-linear map

`rephasingGenerator V (α, β) = I (V† diag(α) V + diag(β))`

from `ℝⁿ × ℝⁿ` to `𝔲(n)`: `V` times it is the derivative at `t = 0` of the rephasing curve with
phases `tα`, `tβ` (`hasDerivAt_rephasing_apply`). A pair `(α, β)` lies in its kernel exactly when
`αᵢ + βⱼ = 0` at every nonzero entry `Vᵢⱼ` (`rephasingGenerator_eq_zero_iff`). The overall phase
`(1, -1)` always lies in the kernel; when no entry of `V` vanishes the kernel is its line, so the
rephasings span a subspace of dimension `2n - 1` and the quotient of `𝔲(n)` by it, the space of
physical directions at `V`, has dimension `n² - (2n - 1) = (n - 1)²`. For every `V` this is a
lower bound. For three generations it is the familiar count of four physical parameters, three
mixing angles and one phase.

## Main results

* `mul_rephasingGenerator_apply`: `(V · rephasingGenerator V (α, β))ᵢⱼ = I (αᵢ + βⱼ) Vᵢⱼ`.
* `hasDerivAt_rephasing_apply`: `V · rephasingGenerator V (α, β)` is the velocity at `t = 0` of
  the rephasing curve `t ↦ diag(e^{itα}) V diag(e^{itβ})`.
* `rephasingGenerator_eq_zero_iff`: the kernel consists of the `(α, β)` with `αᵢ + βⱼ = 0`
  whenever `Vᵢⱼ ≠ 0`.
* `ker_rephasingGenerator`: if no entry of `V` vanishes, the kernel is the line of the overall
  phase `(1, -1)`.
* `finrank_range_rephasingGenerator`: if no entry vanishes, the rephasings span `2n - 1`
  dimensions.
* `finrank_quotient_range_rephasingGenerator`: if no entry vanishes, the physical directions at
  `V` form a real vector space of dimension `(n - 1)²`;
  `sq_card_sub_one_le_finrank_quotient_range_rephasingGenerator` is the lower bound for every `V`.
* `finrank_quotient_range_rephasingGenerator_eq_four`: for a three-generation mixing matrix with
  no vanishing entry there are four physical directions.

## References

* N. Cabibbo, *Unitary Symmetry and Leptonic Decays*, Phys. Rev. Lett. 10 (1963) 531.
* M. Kobayashi and T. Maskawa, *CP-Violation in the Renormalizable Theory of Weak Interaction*,
  Prog. Theor. Phys. 49 (1973) 652.
* Particle Data Group, *The CKM quark-mixing matrix*, §12.1.
-/

public section

noncomputable section

namespace EpsilonEridani
namespace QFT
namespace Scattering
namespace DIS
namespace PVES
namespace Electroweak

open _root_.Matrix Complex Module

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The infinitesimal rephasing of a mixing matrix `V ∈ U(n)`, left-translated to the Lie algebra
`𝔲(n)` of skew-Hermitian matrices: the phases `(α, β)` of the up-type and down-type quarks go to
`I (V† diag(α) V + diag(β))`. Multiplied on the left by `V` it is the velocity of the rephasing
curve `t ↦ diag(e^{itα}) V diag(e^{itβ})` (`hasDerivAt_rephasing_apply`). -/
def rephasingGenerator (V : unitaryGroup ι ℂ) :
    (ι → ℝ) × (ι → ℝ) →ₗ[ℝ] skewAdjoint (_root_.Matrix ι ι ℂ) where
  toFun p := ⟨I • (star (V : _root_.Matrix ι ι ℂ) * diagonal (fun k => (p.1 k : ℂ)) * V +
      diagonal (fun k => (p.2 k : ℂ))), by
    have hD (d : ι → ℝ) : IsSelfAdjoint (diagonal fun k => (d k : ℂ)) :=
      _root_.Matrix.isHermitian_diagonal_of_self_adjoint _ (funext fun k => conj_ofReal (d k))
    exact I_smul_mem_skewAdjoint_iff_isSelfAdjoint.2 (((hD p.1).conjugate' _).add (hD p.2))⟩
  map_add' p q := by
    ext1
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, ofReal_add, ← diagonal_add, mul_add,
      add_mul, AddMemClass.mk_add_mk, smul_add]
    abel
  map_smul' c p := by
    ext1
    have h (d : ι → ℝ) : (fun k => ((c • d) k : ℂ)) = c • fun k => (d k : ℂ) :=
      funext fun k => by simp
    simp only [Prod.smul_fst, Prod.smul_snd, h, diagonal_smul, RingHom.id_apply,
      skewAdjoint.val_smul, _root_.Matrix.mul_smul, _root_.Matrix.smul_mul, ← smul_add,
      smul_comm I c]

/-- The infinitesimal rephasing `(α, β)` at `V` is the skew-Hermitian matrix
`I (V† diag(α) V + diag(β))`. -/
theorem coe_rephasingGenerator_apply (V : unitaryGroup ι ℂ) (p : (ι → ℝ) × (ι → ℝ)) :
    (rephasingGenerator V p : _root_.Matrix ι ι ℂ) =
      I • (star (V : _root_.Matrix ι ι ℂ) * diagonal (fun k => (p.1 k : ℂ)) * V +
        diagonal (fun k => (p.2 k : ℂ))) :=
  (rfl)

/-- Translated back to `V`, the infinitesimal rephasing is `I (diag(α) V + V diag(β))`. -/
theorem mul_rephasingGenerator (V : unitaryGroup ι ℂ) (p : (ι → ℝ) × (ι → ℝ)) :
    (V : _root_.Matrix ι ι ℂ) * rephasingGenerator V p =
      I • (diagonal (fun k => (p.1 k : ℂ)) * V + V * diagonal (fun k => (p.2 k : ℂ))) := by
  rw [coe_rephasingGenerator_apply, mul_smul_comm, mul_add, ← mul_assoc, ← mul_assoc,
    mem_unitaryGroup_iff.mp V.2, one_mul]

/-- Entrywise, the infinitesimal rephasing translated back to `V` multiplies `Vᵢⱼ` by
`I (αᵢ + βⱼ)`. -/
@[simp]
theorem mul_rephasingGenerator_apply (V : unitaryGroup ι ℂ) (p : (ι → ℝ) × (ι → ℝ)) (i j : ι) :
    ((V : _root_.Matrix ι ι ℂ) * rephasingGenerator V p) i j =
      I * ((p.1 i : ℂ) + p.2 j) * (V : _root_.Matrix ι ι ℂ) i j := by
  rw [mul_rephasingGenerator, _root_.Matrix.smul_apply, _root_.Matrix.add_apply, diagonal_mul,
    mul_diagonal, smul_eq_mul]
  ring

/-- `V · rephasingGenerator V (α, β)` is the velocity at `t = 0` of the rephasing curve
`t ↦ diag(e^{itα}) V diag(e^{itβ})`, read entrywise. This identifies `rephasingGenerator V` with
the derivative of the rephasing action at `V`, left-translated to the Lie algebra. -/
theorem hasDerivAt_rephasing_apply (V : unitaryGroup ι ℂ) (α β : ι → ℝ) (i j : ι) :
    HasDerivAt (fun t : ℝ => ((TauCeti.unitaryTorusHom ι (fun k => Circle.exp (t * α k)) * V *
        TauCeti.unitaryTorusHom ι (fun k => Circle.exp (t * β k)) : unitaryGroup ι ℂ) :
          _root_.Matrix ι ι ℂ) i j)
      (((V : _root_.Matrix ι ι ℂ) * rephasingGenerator V (α, β)) i j) 0 := by
  have hc : HasDerivAt (fun z : ℂ => (V : _root_.Matrix ι ι ℂ) i j * cexp (z * ((α i + β j) * I)))
      ((V : _root_.Matrix ι ι ℂ) i j * (cexp (((0 : ℝ) : ℂ) * ((α i + β j) * I)) *
        ((α i + β j) * I))) ((0 : ℝ) : ℂ) :=
    (((hasDerivAt_id _).mul_const _).cexp.congr_deriv (by simp)).const_mul _
  convert hc.comp_ofReal using 1
  · funext t
    simp only [Submonoid.coe_mul, TauCeti.coe_unitaryTorusHom, Circle.coe_exp, diagonal_mul,
      mul_diagonal, ofReal_mul]
    rw [mul_comm (cexp _), mul_assoc, ← Complex.exp_add]
    ring_nf
  · simp only [mul_rephasingGenerator_apply, ofReal_zero, zero_mul, Complex.exp_zero, one_mul]
    ring

/-- A rephasing `(α, β)` is infinitesimally trivial at `V` exactly when `αᵢ + βⱼ = 0` at every
nonzero entry `Vᵢⱼ`. -/
theorem rephasingGenerator_eq_zero_iff (V : unitaryGroup ι ℂ) (p : (ι → ℝ) × (ι → ℝ)) :
    rephasingGenerator V p = 0 ↔ ∀ i j, (V : _root_.Matrix ι ι ℂ) i j ≠ 0 → p.1 i + p.2 j = 0 := by
  have key : rephasingGenerator V p = 0 ↔
      (V : _root_.Matrix ι ι ℂ) * rephasingGenerator V p = 0 := by
    refine ⟨fun h => by simp [h], fun h => Subtype.ext ?_⟩
    simpa [← mul_assoc, mem_unitaryGroup_iff'.mp V.2] using
      congrArg (star (V : _root_.Matrix ι ι ℂ) * ·) h
  rw [key, ← _root_.Matrix.ext_iff]
  simp only [mul_rephasingGenerator_apply, _root_.Matrix.zero_apply, mul_eq_zero, I_ne_zero,
    false_or]
  refine forall₂_congr fun i j => ?_
  rw [← ofReal_add, ofReal_eq_zero, or_iff_not_imp_right]

/-- The overall phase `(1, -1)`, a common rephasing of every quark, never changes `V`. -/
@[simp]
theorem rephasingGenerator_one_neg_one (V : unitaryGroup ι ℂ) :
    rephasingGenerator V (1, -1) = 0 :=
  (rephasingGenerator_eq_zero_iff V _).2 fun _ _ _ => by simp

/-- If no entry of `V` vanishes, the only infinitesimally trivial rephasings are the multiples of
the overall phase `(1, -1)`. -/
theorem ker_rephasingGenerator {V : unitaryGroup ι ℂ}
    (hV : ∀ i j, (V : _root_.Matrix ι ι ℂ) i j ≠ 0) :
    LinearMap.ker (rephasingGenerator V) = ℝ ∙ ((1 : ι → ℝ), (-1 : ι → ℝ)) := by
  ext p
  rw [LinearMap.mem_ker, rephasingGenerator_eq_zero_iff, Submodule.mem_span_singleton]
  refine ⟨fun h => ?_, ?_⟩
  · rcases isEmpty_or_nonempty ι with hι | ⟨⟨i₀⟩⟩
    · exact ⟨0, Subsingleton.elim _ _⟩
    · refine ⟨p.1 i₀, Prod.ext (funext fun i => ?_) (funext fun j => ?_)⟩
      · have h₁ := h i i₀ (hV i i₀)
        have h₂ := h i₀ i₀ (hV i₀ i₀)
        simp only [Prod.smul_fst, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
        linarith
      · have h₁ := h i₀ j (hV i₀ j)
        simp only [Prod.smul_snd, Pi.smul_apply, Pi.neg_apply, Pi.one_apply, smul_eq_mul,
          mul_neg, mul_one]
        linarith
  · rintro ⟨c, rfl⟩ i j -
    simp

omit [Fintype ι] [DecidableEq ι] in
/-- The overall phase `(1, -1)` is a nonzero rephasing as soon as there is a generation. -/
private theorem one_neg_one_ne_zero [Nonempty ι] : ((1 : ι → ℝ), (-1 : ι → ℝ)) ≠ 0 := by
  inhabit ι
  intro h
  simpa using congr_fun (congrArg Prod.fst h) default

/-- For every `V`, the infinitesimally trivial rephasings contain at least the line of the
overall phase. -/
theorem one_le_finrank_ker_rephasingGenerator [Nonempty ι] (V : unitaryGroup ι ℂ) :
    1 ≤ finrank ℝ (LinearMap.ker (rephasingGenerator V)) := by
  rw [← finrank_span_singleton (K := ℝ) (one_neg_one_ne_zero (ι := ι))]
  exact Submodule.finrank_mono
    ((Submodule.span_singleton_le_iff_mem _ _).2 (rephasingGenerator_one_neg_one V))

/-- If no entry of `V` vanishes, the infinitesimally trivial rephasings form a line. -/
theorem finrank_ker_rephasingGenerator [Nonempty ι] {V : unitaryGroup ι ℂ}
    (hV : ∀ i j, (V : _root_.Matrix ι ι ℂ) i j ≠ 0) :
    finrank ℝ (LinearMap.ker (rephasingGenerator V)) = 1 := by
  rw [ker_rephasingGenerator hV, finrank_span_singleton one_neg_one_ne_zero]

/-- The rank of the infinitesimal rephasing map and the dimension of its kernel add up to the
`2n` quark phases. -/
theorem finrank_range_add_finrank_ker_rephasingGenerator (V : unitaryGroup ι ℂ) :
    finrank ℝ (LinearMap.range (rephasingGenerator V)) +
      finrank ℝ (LinearMap.ker (rephasingGenerator V)) = 2 * Fintype.card ι := by
  rw [LinearMap.finrank_range_add_finrank_ker, Module.finrank_prod,
    Module.finrank_fintype_fun_eq_card, two_mul]

/-- If no entry of `V` vanishes, the infinitesimal rephasings at `V` span `2n - 1` dimensions:
the `2n` quark phases less the overall phase. -/
theorem finrank_range_rephasingGenerator {V : unitaryGroup ι ℂ}
    (hV : ∀ i j, (V : _root_.Matrix ι ι ℂ) i j ≠ 0) :
    finrank ℝ (LinearMap.range (rephasingGenerator V)) = 2 * Fintype.card ι - 1 := by
  have h := finrank_range_add_finrank_ker_rephasingGenerator V
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp_all
  · rw [finrank_ker_rephasingGenerator hV] at h
    omega

/-- The physical directions at `V`, the quotient of `𝔲(n)` by the infinitesimal rephasings, and
the infinitesimal rephasings together fill the `n²` dimensions of `𝔲(n)`. -/
theorem finrank_quotient_range_rephasingGenerator_add (V : unitaryGroup ι ℂ) :
    finrank ℝ (skewAdjoint (_root_.Matrix ι ι ℂ) ⧸ LinearMap.range (rephasingGenerator V)) +
      finrank ℝ (LinearMap.range (rephasingGenerator V)) = Fintype.card ι ^ 2 := by
  rw [Submodule.finrank_quotient_add_finrank, _root_.Matrix.finrank_real_skewAdjoint]

/-- For every mixing matrix `V`, there are at least `(n - 1)²` physical directions at `V`: the
quotient of the Lie algebra `𝔲(n)` by the infinitesimal rephasings has dimension at least
`(n - 1)²`. -/
theorem sq_card_sub_one_le_finrank_quotient_range_rephasingGenerator (V : unitaryGroup ι ℂ) :
    (Fintype.card ι - 1) ^ 2 ≤
      finrank ℝ (skewAdjoint (_root_.Matrix ι ι ℂ) ⧸ LinearMap.range (rephasingGenerator V)) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp
  have h₁ := finrank_quotient_range_rephasingGenerator_add V
  have h₂ := finrank_range_add_finrank_ker_rephasingGenerator V
  have h₃ := one_le_finrank_ker_rephasingGenerator V
  obtain ⟨m, hm⟩ : ∃ m, Fintype.card ι = m + 1 :=
    ⟨_, (Nat.succ_pred_eq_of_pos Fintype.card_pos).symm⟩
  rw [hm] at h₁ h₂ ⊢
  simp only [add_tsub_cancel_right]
  nlinarith

/-- If no entry of the mixing matrix `V` vanishes, the physical directions at `V`, the quotient of
the Lie algebra `𝔲(n)` by the infinitesimal rephasings, form a real vector space of dimension
`n² - (2n - 1) = (n - 1)²`. -/
theorem finrank_quotient_range_rephasingGenerator {V : unitaryGroup ι ℂ}
    (hV : ∀ i j, (V : _root_.Matrix ι ι ℂ) i j ≠ 0) :
    finrank ℝ (skewAdjoint (_root_.Matrix ι ι ℂ) ⧸ LinearMap.range (rephasingGenerator V)) =
      (Fintype.card ι - 1) ^ 2 := by
  have h₁ := finrank_quotient_range_rephasingGenerator_add V
  rw [finrank_range_rephasingGenerator hV] at h₁
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp_all
  obtain ⟨m, hm⟩ : ∃ m, Fintype.card ι = m + 1 :=
    ⟨_, (Nat.succ_pred_eq_of_pos Fintype.card_pos).symm⟩
  rw [hm, show 2 * (m + 1) - 1 = 2 * m + 1 by omega] at h₁
  rw [hm, add_tsub_cancel_right]
  nlinarith

/-- A three-generation quark mixing matrix with no vanishing entry has four physical directions:
the quotient of `𝔲(3)` by the infinitesimal rephasings has dimension four, the count of three
mixing angles and one phase. -/
theorem finrank_quotient_range_rephasingGenerator_eq_four {V : CKMMatrix}
    (hV : ∀ i j, V.1 i j ≠ 0) :
    finrank ℝ (skewAdjoint (_root_.Matrix (Fin 3) (Fin 3) ℂ) ⧸
      LinearMap.range (rephasingGenerator V)) = 4 := by
  rw [finrank_quotient_range_rephasingGenerator hV, Fintype.card_fin]
  norm_num

end Electroweak
end PVES
end DIS
end Scattering
end QFT
end EpsilonEridani

