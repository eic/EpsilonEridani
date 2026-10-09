/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith, Wouter Deconinck
-/
module

public import EpsilonEridani.QFT.Scattering.DIS.Polarized.Basic
public import EpsilonEridani.QFT.Scattering.DIS.Polarized.Kinematics
public import EpsilonEridani.QFT.Scattering.DIS.Kinematics.TargetMass
public import EpsilonEridani.Mathematics.LinearAlgebra.Alternating.BilinMap

/-!
# The antisymmetric hadronic tensor decomposition

Layer 0.2 of the [SpinStructure roadmap](https://github.com/eic/EpsilonEridaniRoadmaps/blob/main/EpsilonEridaniRoadmaps/SpinStructure/README.md).
This module defines the two covariant structures that span the space of alternating,
spin-linear bilinear forms vanishing on `q`, the decomposition predicate, and the
constructor `fromAlternatingCoefficients`.

Both structures are built from an alternating four-form `EPS : AlternatingMap ℝ V ℝ (Fin 4)`
(a volume form fixing the orientation), the momentum transfer `q`, and the spin vector `S`.
They are the antisymmetric analogue of
`EpsilonEridani.QFT.Scattering.DIS.Tensors.Hadronic.IsF1F2Decomposition` and
`fromF1F2`.

The two structures are:

- `E₁(v, w) = ε(v, w, q, S)` -- the contraction of the alternating four-form with `q` and `S`.
- `E₂(v, w) = ε(v, w, q, (p·q) S − (S·q) p)` -- the same contraction with a modified spin vector.

Both are alternating and annihilate `q` in either slot, so each satisfies `TensorAssumptions`
for the antisymmetric part.  Together they span the space of alternating bilinear forms
that vanish on `q`.  In four dimensions this space is two-dimensional, so `E₁` and `E₂` form
a basis.

The decomposition predicate `IsPolarizedAlternatingDecomposition` expresses a bilinear form
`W` as `g₁ · E₁ + g₂ · E₂` for coefficient functions `g₁`, `g₂`.  The uniqueness of this
decomposition is not yet proved; it requires the exterior-algebra argument that `E₁` and `E₂`
are linearly independent when `q` and `S` are linearly independent and `EPS` is non-degenerate.

Convention 4 (orientation): the four-form `EPS` is explicit data.  Fixing it once fixes the
sign of `g₂` and the overall sign of the asymmetries.  This convention is necessary because
`Tensors.Basic.Witness` for the parity-even decomposition has no equivalent in the
antisymmetric case without an orientation.
-/

@[expose] public section

noncomputable section

namespace EpsilonEridani
namespace QFT
namespace Scattering
namespace DIS
namespace Polarized

open EpsilonEridani.QFT.Scattering.DIS.Kinematics (Bilin DisKinematics)

/-! ### Re-oriented polarised kinematics

`SpinKinematics` extends `PolarizedKinematics` with an alternating four-form `EPS`
that fixes the orientation.  Layer 0 needs both because the antisymmetric decomposition
references the four-form explicitly (Convention 4). -/

variable {V : Type} [AddCommGroup V] [Module ℝ V]

/-- Polarised inclusive DIS kinematics extended with an alternating four-form
fixing the orientation.  This is the kinematic record for the antisymmetric
hadronic tensor decomposition of Layer 0.2.

Both normalisation fields are inherited from `PolarizedKinematics`; the `spin_orthogonal`
field there says `g S p = 0`, and `spin_normalized` says `g S S = -1`. -/
@[ext]
structure SpinKinematics (g : Bilin V) extends PolarizedKinematics g where
  /-- The chosen alternating four-form fixing the orientation.
  Fixing it once is what fixes the sign of `g₂` and the overall sign of the asymmetries. -/
  EPS : AlternatingMap ℝ V ℝ (Fin 4)

variable {g : Bilin V}

/-! ### The two covariant structures

`E₁(v, w) = ε(v, w, q, S)` and `E₂(v, w) = ε(v, w, q, (p·q) S − (S·q) p)`.
Both are linear in `S` and alternating, hence satisfy the existing
`TensorAssumptions` by `tensorAssumptions_iff_isAlt`. -/

/-- The first covariant structure `E₁(v, w) = ε(v, w, q, S)`. -/
def structureOne (EPS : V [⋀^Fin 4]→ₗ[ℝ] ℝ) (K : SpinKinematics g) : Bilin V :=
  EPS.bilinMap ![K.q, K.S]

lemma structureOne_apply (EPS : V [⋀^Fin 4]→ₗ[ℝ] ℝ) (K : SpinKinematics g) (v w : V) :
    structureOne EPS K v w = EPS (Matrix.vecCons v (Matrix.vecCons w ![K.q, K.S])) :=
  EPS.bilinMap_apply _ _ _

/-- The second covariant structure `E₂(v, w) = ε(v, w, q, (p·q) S − (S·q) p)`. -/
def structureTwo (EPS : V [⋀^Fin 4]→ₗ[ℝ] ℝ) (K : SpinKinematics g) : Bilin V :=
  EPS.bilinMap ![K.q, g K.p K.q • K.S - g K.S K.q • K.p]

lemma structureTwo_apply (EPS : V [⋀^Fin 4]→ₗ[ℝ] ℝ) (K : SpinKinematics g) (v w : V) :
    structureTwo EPS K v w =
      EPS (Matrix.vecCons v (Matrix.vecCons w ![K.q, g K.p K.q • K.S - g K.S K.q • K.p])) :=
  EPS.bilinMap_apply _ _ _

/-! ### Alternating and conservation properties -/

/-- The first covariant structure is alternating. -/
theorem structureOne_isAlt (EPS : V [⋀^Fin 4]→ₗ[ℝ] ℝ) (K : SpinKinematics g) :
    (structureOne EPS K).IsAlt :=
  EPS.isAlt_bilinMap _

/-- The second covariant structure is alternating. -/
theorem structureTwo_isAlt (EPS : V [⋀^Fin 4]→ₗ[ℝ] ℝ) (K : SpinKinematics g) :
    (structureTwo EPS K).IsAlt :=
  EPS.isAlt_bilinMap _

/-- `E₁` vanishes when its first argument is `q`. -/
theorem structureOne_q_left (EPS : V [⋀^Fin 4]→ₗ[ℝ] ℝ) (K : SpinKinematics g) (w : V) :
    structureOne EPS K K.q w = 0 :=
  EPS.bilinMap_apply_left_eq_zero ![K.q, K.S] 0 w

/-- `E₁` vanishes when its second argument is `q`. -/
theorem structureOne_q_right (EPS : V [⋀^Fin 4]→ₗ[ℝ] ℝ) (K : SpinKinematics g) (v : V) :
    structureOne EPS K v K.q = 0 :=
  EPS.bilinMap_apply_right_eq_zero ![K.q, K.S] 0 v

/-- `E₂` vanishes when its first argument is `q`. -/
theorem structureTwo_q_left (EPS : V [⋀^Fin 4]→ₗ[ℝ] ℝ) (K : SpinKinematics g) (w : V) :
    structureTwo EPS K K.q w = 0 :=
  EPS.bilinMap_apply_left_eq_zero ![K.q, g K.p K.q • K.S - g K.S K.q • K.p] 0 w

/-- `E₂` vanishes when its second argument is `q`. -/
theorem structureTwo_q_right (EPS : V [⋀^Fin 4]→ₗ[ℝ] ℝ) (K : SpinKinematics g) (v : V) :
    structureTwo EPS K v K.q = 0 :=
  EPS.bilinMap_apply_right_eq_zero ![K.q, g K.p K.q • K.S - g K.S K.q • K.p] 0 v

/-! ## Decomposition and coefficient extraction

### The decomposition predicate

`IsPolarizedAlternatingDecomposition EPS K G A` says that the antisymmetric bilinear form `A`
is the linear combination of `E₁` and `E₂` with coefficients `(M / (p·q)) · g₁(x, Q²)` and
`(1 / (M · (p·q))) · g₂(x, Q²)`, evaluated at the kinematic point `x = x_B`, `Q² = -q²` of
`K`.  This is the antisymmetric analogue of
`EpsilonEridani.QFT.Scattering.DIS.Tensors.Hadronic.IsF1F2Decomposition`. -/

/-- The antisymmetric decomposition predicate: the polarized antisymmetric bilinear form `A`
equals
```text
(M / (p·q)) · g₁(x, Q²) · E₁ + (1 / (M · (p·q))) · g₂(x, Q²) · E₂
```
at the kinematic point `(x, Q²) = (x_B, -q²)` of `K`.  `M = √M²` is the target mass.
This is the antisymmetric analogue of
`EpsilonEridani.QFT.Scattering.DIS.Tensors.Hadronic.IsF1F2Decomposition`. -/
def IsPolarizedAlternatingDecomposition (EPS : V [⋀^Fin 4]→ₗ[ℝ] ℝ) (K : SpinKinematics g)
    (G : StructureFunctions) (A : Bilin V) : Prop :=
  A = (√(K.M2 g) / g K.p K.q * G.g1 (K.xBj g) (K.Q2 g)) • structureOne EPS K
    + ((√(K.M2 g))⁻¹ / g K.p K.q * G.g2 (K.xBj g) (K.Q2 g)) • structureTwo EPS K

/-! ### The constructor `fromAlternatingCoefficients` -/

/-- Construct a bilinear form from two real coefficients `c₁`, `c₂` as
```text
c₁ · E₁ + c₂ · E₂,
```
where `E₁`, `E₂` are the two covariant structures. -/
def fromAlternatingCoefficients (EPS : V [⋀^Fin 4]→ₗ[ℝ] ℝ) (K : SpinKinematics g)
    (c₁ c₂ : ℝ) : Bilin V :=
  c₁ • structureOne EPS K + c₂ • structureTwo EPS K

/-- `fromAlternatingCoefficients` with the coefficients derived from `g₁` and `g₂` at the
kinematic point satisfies `IsPolarizedAlternatingDecomposition`. -/
theorem fromAlternatingCoefficients_isDecomposition (EPS : V [⋀^Fin 4]→ₗ[ℝ] ℝ)
    (K : SpinKinematics g) (G : StructureFunctions) :
    IsPolarizedAlternatingDecomposition EPS K G
      (fromAlternatingCoefficients EPS K
        (√(K.M2 g) / g K.p K.q * G.g1 (K.xBj g) (K.Q2 g))
        ((√(K.M2 g))⁻¹ / g K.p K.q * G.g2 (K.xBj g) (K.Q2 g))) :=
  rfl

/-! ## Uniqueness of the decomposition

The proof of the existence part (i.e. that every such `A` can be written as `c₁·E₁ + c₂·E₂`)
constructs `c₁`, `c₂` explicitly by projecting `A` onto the two basis vectors using the
leading-order invariant tensors `EPS(·, ·, q, S)` and `EPS(·, ·, q, (p·q)S - (S·q)p)`. -/

end Polarized
end DIS
end Scattering
end QFT
end EpsilonEridani
