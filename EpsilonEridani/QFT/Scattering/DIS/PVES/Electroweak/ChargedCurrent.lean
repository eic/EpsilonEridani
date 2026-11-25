/-
Copyright (c) 2026 The EpsilonEridani contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The EpsilonEridani contributors
-/
module

public import EpsilonEridani.Relativity.CliffordAlgebraExtensions
public import TauCeti.Analysis.Matrix.UnitaryGroup.Torus

/-!
# The charged weak current and its rephasing invariance

The `W` boson couples the up-type quarks `u_i` to the down-type quarks `d_j` through the charged
weak current. In the conventions of the Particle Data Group the charged-current interaction is

`L_CC = -(g / √2) (W⁺_μ J^μ + W⁻_μ J^μ†)`, with `J^μ = Σᵢⱼ ū_i γ^μ P_L V_ij d_j`,

where `P_L = (1 - γ⁵) / 2` is the left chiral projector and `V` is the quark mixing matrix. This
file defines the current `J^μ` (`chargedCurrent`) for spinors in the Dirac representation of
`spaceTime.γ`, with up- and down-type flavours indexed by arbitrary finite types, so that `V` may be
rectangular. The spinors are `c`-numbers, as in a tree-level amplitude `ū(p') γ^μ P_L u(p)`.

The current is the instance `Γ = γ^μ P_L` of the flavour-summed bilinear `Σᵢⱼ ū_i Γ V_ij d_j`
(`flavorBilinear`). Its behaviour under rephasing and Hermitian conjugation does not depend on
the vertex `Γ`, and is proved for `flavorBilinear`.

## Main definitions

* `flavorBilinear V u d Γ`: the flavour-summed Dirac bilinear `Σᵢⱼ ū_i Γ V_ij d_j`.
* `chargedCurrent V u d μ`: the charged weak current `J^μ = Σᵢⱼ ū_i γ^μ P_L V_ij d_j`.

## Main results

* Rephasing. Multiplying the quark spinors by scalars changes the flavour-summed bilinear exactly as
  multiplying `V` by diagonal matrices on both sides does (`flavorBilinear_smul_smul`,
  `chargedCurrent_smul_smul`). So a rephasing of the quark spinors combined with the compensating
  change `V ↦ diag(a) V diag(b)⁻¹` of the mixing matrix leaves it invariant
  (`flavorBilinear_rephase`, `chargedCurrent_rephase`). For a unitary `V` the compensating matrix
  is the action of TauCeti's diagonal torus `TauCeti.unitaryTorusHom` on `U(n)`, so it is again
  unitary
  (`flavorBilinear_unitaryTorusHom_mul_mul_inv`, `chargedCurrent_unitaryTorusHom_mul_mul_inv`).
* Chirality. Only left-handed components contribute: projecting the up- or down-type spinors onto
  their left-handed parts leaves the current unchanged (`chargedCurrent_leftChiralProjector_up`,
  `chargedCurrent_leftChiralProjector_down`), and right-handed spinors give zero
  (`chargedCurrent_rightChiralProjector_up_eq_zero`,
  `chargedCurrent_rightChiralProjector_down_eq_zero`).
* Hermitian conjugation. The complex conjugate of the flavour-summed bilinear exchanges the spinors,
  replaces `V` by `Vᴴ` and `Γ` by its Dirac adjoint (`star_flavorBilinear`). So the complex
  conjugate of the current, to which the `W⁻` couples, is the current of the down-type into the
  up-type spinors with mixing matrix `Vᴴ` (`star_chargedCurrent`), because the vertex `γ^μ P_L` is
  its own Dirac adjoint (`spaceTime.diracAdjoint_γ_mul_leftChiralProjector`).

## References

* Particle Data Group, *The CKM quark-mixing matrix* and *Electroweak model and constraints on new
  physics*, §10.1.
* N. Cabibbo, *Unitary symmetry and leptonic decays*, Phys. Rev. Lett. 10 (1963) 531.
* M. Kobayashi and T. Maskawa, *CP-violation in the renormalizable theory of weak interaction*,
  Prog. Theor. Phys. 49 (1973) 652.
-/

public section

namespace EpsilonEridani.QFT.Scattering.DIS.PVES.Electroweak

open Matrix spaceTime

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-! ### Flavour-summed Dirac bilinears -/

/-- The flavour-summed Dirac bilinear `Σᵢⱼ ū_i Γ V_ij d_j` of up-type spinors `u`, down-type
spinors `d`, a mixing matrix `V` and a vertex `Γ`, in the Dirac representation. -/
noncomputable def flavorBilinear (V : Matrix ι κ ℂ) (u : ι → Fin 4 → ℂ) (d : κ → Fin 4 → ℂ)
    (Γ : Matrix (Fin 4) (Fin 4) ℂ) : ℂ :=
  ∑ i, ∑ j, V i j * diracBilinear (u i) Γ (d j)

/-- Unfolding lemma for `flavorBilinear`. -/
lemma flavorBilinear_def (V : Matrix ι κ ℂ) (u : ι → Fin 4 → ℂ) (d : κ → Fin 4 → ℂ)
    (Γ : Matrix (Fin 4) (Fin 4) ℂ) :
    flavorBilinear V u d Γ = ∑ i, ∑ j, V i j * diracBilinear (u i) Γ (d j) := (rfl)

/-- The flavor-summed bilinear is additive in the vertex. -/
@[simp]
lemma flavorBilinear_add (V : Matrix ι κ ℂ) (u : ι → Fin 4 → ℂ) (d : κ → Fin 4 → ℂ)
    (Γ Γ' : Matrix (Fin 4) (Fin 4) ℂ) :
    flavorBilinear V u d (Γ + Γ') = flavorBilinear V u d Γ + flavorBilinear V u d Γ' := by
  simp only [flavorBilinear_def, diracBilinear_add, mul_add, Finset.sum_add_distrib]

/-- The flavor-summed bilinear is linear in the vertex. -/
@[simp]
lemma flavorBilinear_smul (V : Matrix ι κ ℂ) (u : ι → Fin 4 → ℂ) (d : κ → Fin 4 → ℂ)
    (c : ℂ) (Γ : Matrix (Fin 4) (Fin 4) ℂ) :
    flavorBilinear V u d (c • Γ) = c * flavorBilinear V u d Γ := by
  simp only [flavorBilinear_def, diracBilinear_smul, Finset.mul_sum, mul_left_comm]

/-- The flavor-summed bilinear with the zero vertex vanishes. -/
@[simp]
lemma flavorBilinear_zero (V : Matrix ι κ ℂ) (u : ι → Fin 4 → ℂ) (d : κ → Fin 4 → ℂ) :
    flavorBilinear V u d 0 = 0 := by
  simp only [flavorBilinear_def, diracBilinear_zero, mul_zero, Finset.sum_const_zero]

/-- A matrix acting on the down-type spinors moves into the vertex:
`Σᵢⱼ ū_i Γ V_ij (M d_j) = Σᵢⱼ ū_i (Γ M) V_ij d_j`. -/
@[simp]
lemma flavorBilinear_mulVec_right (V : Matrix ι κ ℂ) (u : ι → Fin 4 → ℂ) (d : κ → Fin 4 → ℂ)
    (Γ M : Matrix (Fin 4) (Fin 4) ℂ) :
    flavorBilinear V u (fun j => M *ᵥ d j) Γ = flavorBilinear V u d (Γ * M) := by
  simp only [flavorBilinear_def, diracBilinear_mulVec_right]

/-- A matrix acting on the up-type spinors moves into the vertex through its Dirac adjoint:
`Σᵢⱼ \overline{M u_i} Γ V_ij d_j = Σᵢⱼ ū_i (\bar{M} Γ) V_ij d_j`. -/
@[simp]
lemma flavorBilinear_mulVec_left (V : Matrix ι κ ℂ) (u : ι → Fin 4 → ℂ) (d : κ → Fin 4 → ℂ)
    (Γ M : Matrix (Fin 4) (Fin 4) ℂ) :
    flavorBilinear V (fun i => M *ᵥ u i) d Γ = flavorBilinear V u d (diracAdjoint M * Γ) := by
  simp only [flavorBilinear_def, diracBilinear_mulVec_left]

/-- Rescaling the spinors, `u_i ↦ a_i u_i` and `d_j ↦ b_j d_j`, changes the flavour-summed
bilinear as the change `V ↦ diag(a*) V diag(b)` of the mixing matrix does. -/
theorem flavorBilinear_smul_smul [DecidableEq ι] [DecidableEq κ] (V : Matrix ι κ ℂ)
    (a : ι → ℂ) (b : κ → ℂ) (u : ι → Fin 4 → ℂ) (d : κ → Fin 4 → ℂ) (Γ : Matrix (Fin 4) (Fin 4) ℂ) :
    flavorBilinear V (fun i => a i • u i) (fun j => b j • d j) Γ =
      flavorBilinear (diagonal (star a) * V * diagonal b) u d Γ := by
  simp only [flavorBilinear_def, diracBilinear_smul_left, diracBilinear_smul_right, mul_diagonal,
    diagonal_mul, Pi.star_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- Rephasing invariance of the flavour-summed bilinear: rephasing the spinors,
`u_i ↦ a_i u_i` and `d_j ↦ b_j d_j` with `|a_i| = |b_j| = 1`, together with the compensating change
`V ↦ diag(a) V diag(b)⁻¹` of the mixing matrix leaves it unchanged. -/
theorem flavorBilinear_rephase [DecidableEq ι] [DecidableEq κ] (V : Matrix ι κ ℂ)
    (a : ι → Circle) (b : κ → Circle) (u : ι → Fin 4 → ℂ) (d : κ → Fin 4 → ℂ)
    (Γ : Matrix (Fin 4) (Fin 4) ℂ) :
    flavorBilinear (diagonal (fun i => (a i : ℂ)) * V * diagonal (fun j => ((b j)⁻¹ : ℂ)))
        (fun i => (a i : ℂ) • u i) (fun j => (b j : ℂ) • d j) Γ =
      flavorBilinear V u d Γ := by
  have hstar (z : Circle) : star (z : ℂ) * z = 1 :=
    Unitary.mem_iff_star_mul_self.mp z.coe_mem_unitary
  have hinv (z : Circle) : (z : ℂ)⁻¹ * z = 1 := inv_mul_cancel₀ (Circle.coe_ne_zero z)
  have ha : diagonal (star fun i => (a i : ℂ)) * diagonal (fun i => (a i : ℂ)) = 1 := by
    simp only [diagonal_mul_diagonal, Pi.star_apply, hstar, diagonal_one]
  have hb : diagonal (fun j => ((b j)⁻¹ : ℂ)) * diagonal (fun j => (b j : ℂ)) = 1 := by
    simp only [diagonal_mul_diagonal, hinv, diagonal_one]
  rw [flavorBilinear_smul_smul]
  simp only [← Matrix.mul_assoc, ha, Matrix.one_mul]
  rw [Matrix.mul_assoc, hb, Matrix.mul_one]

/-- Rephasing invariance for a unitary mixing matrix: the compensating change of `V` is the action
`V ↦ t_a V t_b⁻¹` of the diagonal torus of `U(n)`, so the rephased mixing matrix is again
unitary. -/
theorem flavorBilinear_unitaryTorusHom_mul_mul_inv [DecidableEq ι] (V : unitaryGroup ι ℂ)
    (a b : ι → Circle) (u : ι → Fin 4 → ℂ) (d : ι → Fin 4 → ℂ) (Γ : Matrix (Fin 4) (Fin 4) ℂ) :
    flavorBilinear (TauCeti.unitaryTorusHom ι a * V * (TauCeti.unitaryTorusHom ι b)⁻¹ :
        unitaryGroup ι ℂ) (fun i => (a i : ℂ) • u i) (fun j => (b j : ℂ) • d j) Γ =
      flavorBilinear V u d Γ := by
  have hV : ((TauCeti.unitaryTorusHom ι a * V * (TauCeti.unitaryTorusHom ι b)⁻¹ :
      unitaryGroup ι ℂ) : Matrix ι ι ℂ) =
        diagonal (fun i => (a i : ℂ)) * V * diagonal (fun j => ((b j : ℂ))⁻¹) := by
    simp only [← map_inv, Submonoid.coe_mul, TauCeti.coe_unitaryTorusHom, Pi.inv_apply,
      Circle.coe_inv]
  rw [hV, flavorBilinear_rephase]

/-- The complex conjugate of the flavour-summed bilinear exchanges the spinors and replaces the
mixing matrix by `Vᴴ` and the vertex by its Dirac adjoint:
`(Σᵢⱼ ū_i Γ V_ij d_j)* = Σᵢⱼ \bar{d}_j \bar{Γ} V*_ij u_i`. -/
@[simp]
theorem star_flavorBilinear (V : Matrix ι κ ℂ) (u : ι → Fin 4 → ℂ) (d : κ → Fin 4 → ℂ)
    (Γ : Matrix (Fin 4) (Fin 4) ℂ) :
    star (flavorBilinear V u d Γ) = flavorBilinear Vᴴ d u (diracAdjoint Γ) := by
  simp only [flavorBilinear_def, star_sum, star_mul', star_diracBilinear, conjTranspose_apply]
  rw [Finset.sum_comm]

/-! ### The charged current -/

/-- The charged weak current `J^μ = Σᵢⱼ ū_i γ^μ P_L V_ij d_j` of up-type spinors `u`, down-type
spinors `d` and a mixing matrix `V`, in the Dirac representation: the flavour-summed bilinear with
the `V - A` vertex `γ^μ P_L`. The `W⁺` boson couples to it through
`L_CC = -(g / √2) W⁺_μ J^μ + h.c.`. -/
noncomputable def chargedCurrent (V : Matrix ι κ ℂ) (u : ι → Fin 4 → ℂ) (d : κ → Fin 4 → ℂ)
    (μ : Fin 4) : ℂ :=
  flavorBilinear V u d (γ μ * leftChiralProjector)

/-- Unfolding lemma for `chargedCurrent`. -/
lemma chargedCurrent_def (V : Matrix ι κ ℂ) (u : ι → Fin 4 → ℂ) (d : κ → Fin 4 → ℂ)
    (μ : Fin 4) :
    chargedCurrent V u d μ = flavorBilinear V u d (γ μ * leftChiralProjector) := (rfl)

/-! ### Rephasing -/

/-- Rescaling the quark spinors, `u_i ↦ a_i u_i` and `d_j ↦ b_j d_j`, changes the charged current
as the change `V ↦ diag(a*) V diag(b)` of the mixing matrix does. -/
theorem chargedCurrent_smul_smul [DecidableEq ι] [DecidableEq κ] (V : Matrix ι κ ℂ)
    (a : ι → ℂ) (b : κ → ℂ) (u : ι → Fin 4 → ℂ) (d : κ → Fin 4 → ℂ) (μ : Fin 4) :
    chargedCurrent V (fun i => a i • u i) (fun j => b j • d j) μ =
      chargedCurrent (diagonal (star a) * V * diagonal b) u d μ := by
  rw [chargedCurrent_def, chargedCurrent_def, flavorBilinear_smul_smul]

/-- Rephasing invariance of the charged current: rephasing the quark spinors,
`u_i ↦ a_i u_i` and `d_j ↦ b_j d_j` with `|a_i| = |b_j| = 1`, together with the compensating change
`V ↦ diag(a) V diag(b)⁻¹` of the mixing matrix leaves the current unchanged. -/
theorem chargedCurrent_rephase [DecidableEq ι] [DecidableEq κ] (V : Matrix ι κ ℂ) (a : ι → Circle)
    (b : κ → Circle) (u : ι → Fin 4 → ℂ) (d : κ → Fin 4 → ℂ) (μ : Fin 4) :
    chargedCurrent (diagonal (fun i => (a i : ℂ)) * V * diagonal (fun j => ((b j)⁻¹ : ℂ)))
        (fun i => (a i : ℂ) • u i) (fun j => (b j : ℂ) • d j) μ =
      chargedCurrent V u d μ := by
  rw [chargedCurrent_def, chargedCurrent_def, flavorBilinear_rephase]

/-- Rephasing invariance for a unitary mixing matrix: the compensating change of `V` is the action
`V ↦ t_a V t_b⁻¹` of the diagonal torus of `U(n)`, so the rephased mixing matrix is again
unitary. -/
theorem chargedCurrent_unitaryTorusHom_mul_mul_inv [DecidableEq ι] (V : unitaryGroup ι ℂ)
    (a b : ι → Circle) (u : ι → Fin 4 → ℂ) (d : ι → Fin 4 → ℂ) (μ : Fin 4) :
    chargedCurrent (TauCeti.unitaryTorusHom ι a * V * (TauCeti.unitaryTorusHom ι b)⁻¹ :
        unitaryGroup ι ℂ) (fun i => (a i : ℂ) • u i) (fun j => (b j : ℂ) • d j) μ =
      chargedCurrent V u d μ := by
  rw [chargedCurrent_def, chargedCurrent_def, flavorBilinear_unitaryTorusHom_mul_mul_inv]

/-! ### Chirality -/

/-- Only the left-handed parts of the down-type spinors enter the charged current. -/
@[simp]
theorem chargedCurrent_leftChiralProjector_down (V : Matrix ι κ ℂ) (u : ι → Fin 4 → ℂ)
    (d : κ → Fin 4 → ℂ) (μ : Fin 4) :
    chargedCurrent V u (fun j => leftChiralProjector *ᵥ d j) μ = chargedCurrent V u d μ := by
  rw [chargedCurrent_def, chargedCurrent_def, flavorBilinear_mulVec_right, mul_assoc,
    leftChiralProjector_mul_self]

/-- Right-handed down-type spinors do not enter the charged current. -/
@[simp]
theorem chargedCurrent_rightChiralProjector_down_eq_zero (V : Matrix ι κ ℂ) (u : ι → Fin 4 → ℂ)
    (d : κ → Fin 4 → ℂ) (μ : Fin 4) :
    chargedCurrent V u (fun j => rightChiralProjector *ᵥ d j) μ = 0 := by
  rw [chargedCurrent_def, flavorBilinear_mulVec_right, mul_assoc,
    leftChiralProjector_mul_rightChiralProjector, mul_zero, flavorBilinear_zero]

/-- Only the left-handed parts of the up-type spinors enter the charged current. -/
@[simp]
theorem chargedCurrent_leftChiralProjector_up (V : Matrix ι κ ℂ) (u : ι → Fin 4 → ℂ)
    (d : κ → Fin 4 → ℂ) (μ : Fin 4) :
    chargedCurrent V (fun i => leftChiralProjector *ᵥ u i) d μ = chargedCurrent V u d μ := by
  rw [chargedCurrent_def, chargedCurrent_def, flavorBilinear_mulVec_left,
    diracAdjoint_leftChiralProjector, γ_mul_leftChiralProjector, ← mul_assoc,
    rightChiralProjector_mul_self]

/-- Right-handed up-type spinors do not enter the charged current. -/
@[simp]
theorem chargedCurrent_rightChiralProjector_up_eq_zero (V : Matrix ι κ ℂ) (u : ι → Fin 4 → ℂ)
    (d : κ → Fin 4 → ℂ) (μ : Fin 4) :
    chargedCurrent V (fun i => rightChiralProjector *ᵥ u i) d μ = 0 := by
  rw [chargedCurrent_def, flavorBilinear_mulVec_left, diracAdjoint_rightChiralProjector,
    γ_mul_leftChiralProjector, ← mul_assoc, leftChiralProjector_mul_rightChiralProjector,
    zero_mul, flavorBilinear_zero]

/-! ### Hermitian conjugation -/

/-- The Hermitian conjugate of the charged current, to which the `W⁻` boson couples, is the
charged current of the down-type into the up-type spinors with mixing matrix `Vᴴ`:
`(J^μ)* = Σᵢⱼ \bar{d}_j γ^μ P_L V*_ij u_i`. -/
@[simp]
theorem star_chargedCurrent (V : Matrix ι κ ℂ) (u : ι → Fin 4 → ℂ) (d : κ → Fin 4 → ℂ)
    (μ : Fin 4) :
    star (chargedCurrent V u d μ) = chargedCurrent Vᴴ d u μ := by
  rw [chargedCurrent_def, chargedCurrent_def, star_flavorBilinear,
    diracAdjoint_γ_mul_leftChiralProjector]

end EpsilonEridani.QFT.Scattering.DIS.PVES.Electroweak
