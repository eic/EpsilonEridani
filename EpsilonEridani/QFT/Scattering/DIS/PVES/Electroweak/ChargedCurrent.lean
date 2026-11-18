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

## Main definitions

* `chargedCurrent V u d μ`: the charged weak current `J^μ = Σᵢⱼ ū_i γ^μ P_L V_ij d_j`.

## Main results

* Rephasing. Multiplying the quark spinors by scalars changes the current exactly as multiplying
  `V` by diagonal matrices on both sides does (`chargedCurrent_smul`). So a rephasing of the quark
  spinors combined with the compensating change `V ↦ diag(a) V diag(b)⁻¹` of the mixing matrix
  leaves the current invariant (`chargedCurrent_rephase`). For a unitary `V` the compensating
  matrix is the action of TauCeti's diagonal torus `TauCeti.unitaryTorusHom` on `U(n)`, so it is
  again unitary (`chargedCurrent_unitaryTorusHom_mul_mul_inv`).
* Chirality. Only left-handed components contribute: projecting the up- or down-type spinors onto
  their left-handed parts leaves the current unchanged (`chargedCurrent_leftChiralProjector_up`,
  `chargedCurrent_leftChiralProjector_down`), and right-handed spinors give zero
  (`chargedCurrent_rightChiralProjector_up`, `chargedCurrent_rightChiralProjector_down`).
* Hermitian conjugation. The complex conjugate of the current, to which the `W⁻` couples, is the
  current of the down-type into the up-type spinors with mixing matrix `Vᴴ`
  (`star_chargedCurrent`), because the vertex `γ^μ P_L` is its own Dirac adjoint
  (`spaceTime.diracAdjoint_γ_mul_leftChiralProjector`).

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

/-- The charged weak current `J^μ = Σᵢⱼ ū_i γ^μ P_L V_ij d_j` of up-type spinors `u`, down-type
spinors `d` and a mixing matrix `V`, in the Dirac representation. The `W⁺` boson couples to it
through `L_CC = -(g / √2) W⁺_μ J^μ + h.c.`. -/
noncomputable def chargedCurrent (V : Matrix ι κ ℂ) (u : ι → Fin 4 → ℂ) (d : κ → Fin 4 → ℂ)
    (μ : Fin 4) : ℂ :=
  ∑ i, ∑ j, V i j * diracBilinear (u i) (γ μ * leftChiralProjector) (d j)

/-- Unfolding lemma for `chargedCurrent`. -/
lemma chargedCurrent_def (V : Matrix ι κ ℂ) (u : ι → Fin 4 → ℂ) (d : κ → Fin 4 → ℂ)
    (μ : Fin 4) :
    chargedCurrent V u d μ =
      ∑ i, ∑ j, V i j * diracBilinear (u i) (γ μ * leftChiralProjector) (d j) := (rfl)

/-! ### Rephasing -/

/-- Rescaling the quark spinors, `u_i ↦ a_i u_i` and `d_j ↦ b_j d_j`, changes the charged current
as the change `V ↦ diag(a*) V diag(b)` of the mixing matrix does. -/
theorem chargedCurrent_smul [DecidableEq ι] [DecidableEq κ] (V : Matrix ι κ ℂ) (a : ι → ℂ)
    (b : κ → ℂ) (u : ι → Fin 4 → ℂ) (d : κ → Fin 4 → ℂ) (μ : Fin 4) :
    chargedCurrent V (fun i => a i • u i) (fun j => b j • d j) μ =
      chargedCurrent (diagonal (star a) * V * diagonal b) u d μ := by
  simp only [chargedCurrent_def, diracBilinear_smul_left, diracBilinear_smul_right, mul_diagonal,
    diagonal_mul, Pi.star_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- Rephasing invariance of the charged current: rephasing the quark spinors,
`u_i ↦ a_i u_i` and `d_j ↦ b_j d_j` with `|a_i| = |b_j| = 1`, together with the compensating change
`V ↦ diag(a) V diag(b)⁻¹` of the mixing matrix leaves the current unchanged. -/
theorem chargedCurrent_rephase [DecidableEq ι] [DecidableEq κ] (V : Matrix ι κ ℂ) (a : ι → Circle)
    (b : κ → Circle) (u : ι → Fin 4 → ℂ) (d : κ → Fin 4 → ℂ) (μ : Fin 4) :
    chargedCurrent (diagonal (fun i => (a i : ℂ)) * V * diagonal (fun j => ((b j)⁻¹ : ℂ)))
        (fun i => (a i : ℂ) • u i) (fun j => (b j : ℂ) • d j) μ =
      chargedCurrent V u d μ := by
  rw [chargedCurrent_smul]
  congr 1
  ext i j
  have ha : star (a i : ℂ) * a i = 1 := by
    rw [Complex.star_def, ← Circle.coe_inv_eq_conj, ← Circle.coe_mul, inv_mul_cancel,
      Circle.coe_one]
  simp only [mul_diagonal, diagonal_mul, Pi.star_apply]
  calc star (a i : ℂ) * (a i * V i j * (b j : ℂ)⁻¹) * b j
      = (star (a i : ℂ) * a i) * V i j * ((b j : ℂ)⁻¹ * b j) := by ring
    _ = V i j := by rw [ha, inv_mul_cancel₀ (Circle.coe_ne_zero _), one_mul, mul_one]

/-- Rephasing invariance for a unitary mixing matrix: the compensating change of `V` is the action
`V ↦ t_a V t_b⁻¹` of the diagonal torus of `U(n)`, so the rephased mixing matrix is again
unitary. -/
theorem chargedCurrent_unitaryTorusHom_mul_mul_inv [DecidableEq ι] (V : unitaryGroup ι ℂ)
    (a b : ι → Circle) (u : ι → Fin 4 → ℂ) (d : ι → Fin 4 → ℂ) (μ : Fin 4) :
    chargedCurrent (TauCeti.unitaryTorusHom ι a * V * (TauCeti.unitaryTorusHom ι b)⁻¹ :
        unitaryGroup ι ℂ) (fun i => (a i : ℂ) • u i) (fun j => (b j : ℂ) • d j) μ =
      chargedCurrent V u d μ := by
  have hV : ((TauCeti.unitaryTorusHom ι a * V * (TauCeti.unitaryTorusHom ι b)⁻¹ :
      unitaryGroup ι ℂ) : Matrix ι ι ℂ) =
        diagonal (fun i => (a i : ℂ)) * V * diagonal (fun j => ((b j : ℂ))⁻¹) := by
    simp [← map_inv, Circle.coe_inv]
  rw [hV, chargedCurrent_rephase]

/-! ### Chirality -/

/-- Only the left-handed parts of the down-type spinors enter the charged current. -/
@[simp]
theorem chargedCurrent_leftChiralProjector_down (V : Matrix ι κ ℂ) (u : ι → Fin 4 → ℂ)
    (d : κ → Fin 4 → ℂ) (μ : Fin 4) :
    chargedCurrent V u (fun j => leftChiralProjector *ᵥ d j) μ = chargedCurrent V u d μ := by
  simp only [chargedCurrent_def, diracBilinear_mulVec_right, mul_assoc,
    leftChiralProjector_mul_self]

/-- Right-handed down-type spinors do not enter the charged current. -/
@[simp]
theorem chargedCurrent_rightChiralProjector_down (V : Matrix ι κ ℂ) (u : ι → Fin 4 → ℂ)
    (d : κ → Fin 4 → ℂ) (μ : Fin 4) :
    chargedCurrent V u (fun j => rightChiralProjector *ᵥ d j) μ = 0 := by
  simp only [chargedCurrent_def, diracBilinear_mulVec_right, mul_assoc,
    leftChiralProjector_mul_rightChiralProjector, mul_zero]
  simp [diracBilinear_def]

/-- Only the left-handed parts of the up-type spinors enter the charged current. -/
@[simp]
theorem chargedCurrent_leftChiralProjector_up (V : Matrix ι κ ℂ) (u : ι → Fin 4 → ℂ)
    (d : κ → Fin 4 → ℂ) (μ : Fin 4) :
    chargedCurrent V (fun i => leftChiralProjector *ᵥ u i) d μ = chargedCurrent V u d μ := by
  simp only [chargedCurrent_def, diracBilinear_mulVec_left, diracAdjoint_leftChiralProjector,
    ← mul_assoc, ← γ_mul_leftChiralProjector]
  simp only [mul_assoc, leftChiralProjector_mul_self]

/-- Right-handed up-type spinors do not enter the charged current. -/
@[simp]
theorem chargedCurrent_rightChiralProjector_up (V : Matrix ι κ ℂ) (u : ι → Fin 4 → ℂ)
    (d : κ → Fin 4 → ℂ) (μ : Fin 4) :
    chargedCurrent V (fun i => rightChiralProjector *ᵥ u i) d μ = 0 := by
  simp only [chargedCurrent_def, diracBilinear_mulVec_left, diracAdjoint_rightChiralProjector,
    ← mul_assoc, ← γ_mul_rightChiralProjector]
  simp only [mul_assoc, rightChiralProjector_mul_leftChiralProjector, mul_zero]
  simp [diracBilinear_def]

/-! ### Hermitian conjugation -/

/-- The Hermitian conjugate of the charged current, to which the `W⁻` boson couples, is the
charged current of the down-type into the up-type spinors with mixing matrix `Vᴴ`:
`(J^μ)* = Σᵢⱼ \bar{d}_j γ^μ P_L V*_ij u_i`. -/
theorem star_chargedCurrent (V : Matrix ι κ ℂ) (u : ι → Fin 4 → ℂ) (d : κ → Fin 4 → ℂ)
    (μ : Fin 4) :
    star (chargedCurrent V u d μ) = chargedCurrent Vᴴ d u μ := by
  simp only [chargedCurrent_def, star_sum, star_mul', star_diracBilinear,
    diracAdjoint_γ_mul_leftChiralProjector, conjTranspose_apply]
  rw [Finset.sum_comm]

end EpsilonEridani.QFT.Scattering.DIS.PVES.Electroweak
