/-
Copyright (c) 2026 The EpsilonEridani contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The EpsilonEridani contributors
-/
module

public import PhyslibAlpha.QuantumMechanics.AngularMomentum.Addition

/-!
# Components of the coupled angular momentum

The coupled angular momentum `PhyslibAlpha.Sl2.AngularMomentumRepresentation.tensor ρ₁ ρ₂` on
`V ⊗ W` has Cartesian components `J₁ ⊗ 1 + 1 ⊗ J₂`, the diagonal action
`PhyslibAlpha.Sl2.diagEnd` of the two factors. Upstream states this for the ladder operators
(`tensor_Jp`, `tensor_Jm`); this module states it for the Cartesian components, so that results
about `diagEnd`, such as its commutation with an operator on `V ⊗ W`, apply to the total angular
momentum without unfolding `tensor`.

## Main results

* `PhyslibAlpha.Sl2.AngularMomentumRepresentation.tensor_Jx`, `tensor_Jy`, `tensor_Jz`:
  `(tensor ρ₁ ρ₂).Jx = diagEnd ρ₁.Jx ρ₂.Jx`, and likewise for `Jy` and `Jz`.
-/

@[expose] public section

namespace PhyslibAlpha.Sl2.AngularMomentumRepresentation

variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- The `x`-component of the coupled angular momentum is `ρ₁.Jx ⊗ 1 + 1 ⊗ ρ₂.Jx`. -/
@[simp]
theorem tensor_Jx (ρ₁ : AngularMomentumRepresentation V) (ρ₂ : AngularMomentumRepresentation W) :
    (tensor ρ₁ ρ₂).Jx = diagEnd ρ₁.Jx ρ₂.Jx :=
  (rfl)

/-- The `y`-component of the coupled angular momentum is `ρ₁.Jy ⊗ 1 + 1 ⊗ ρ₂.Jy`. -/
@[simp]
theorem tensor_Jy (ρ₁ : AngularMomentumRepresentation V) (ρ₂ : AngularMomentumRepresentation W) :
    (tensor ρ₁ ρ₂).Jy = diagEnd ρ₁.Jy ρ₂.Jy :=
  (rfl)

/-- The `z`-component of the coupled angular momentum is `ρ₁.Jz ⊗ 1 + 1 ⊗ ρ₂.Jz`. -/
@[simp]
theorem tensor_Jz (ρ₁ : AngularMomentumRepresentation V) (ρ₂ : AngularMomentumRepresentation W) :
    (tensor ρ₁ ρ₂).Jz = diagEnd ρ₁.Jz ρ₂.Jz :=
  (rfl)

end PhyslibAlpha.Sl2.AngularMomentumRepresentation
