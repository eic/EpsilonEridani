/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.AffineSpace.Midpoint

/-!
# Dipole coordinates in the transverse plane

A colour dipole is a quark at transverse position `x` and an antiquark at transverse position
`y`, both points of `EuclideanSpace ℝ (Fin 2)`. The endpoints are the data: the dipole amplitude
`N Y x y` of the colour-dipole picture is a function of both of them, and not of their difference
alone, because its dependence on the position of the dipole in the target (the impact parameter)
is what makes the unitarity bound local in the transverse plane and what diffractive cross
sections integrate over.

The two derived coordinates used throughout the small-`x` literature are

* the dipole size `r = x - y` (`Dipole.size`), the transverse vector from the antiquark to the
  quark (also called the dipole vector; the amplitude is written `N(r, b)` in these
  coordinates), whose norm `|r|` is the distance between the endpoints, and
* the impact parameter `b = (x + y) / 2` (`Dipole.impactParameter`), the midpoint of the
  endpoints.

This file records a dipole by its endpoints, defines the two derived coordinates, and proves that
passing from endpoints to `(r, b)` is a linear isomorphism, with inverse
`(r, b) ↦ (b + r / 2, b - r / 2)`. A dipole has zero size exactly when its two endpoints
coincide; such a dipole sits on the diagonal at its impact parameter.

## Main definitions

* `SmallX.Dipole`: a quark-antiquark pair of transverse positions, with the ℝ-vector-space
  structure of pairs of points.
* `SmallX.Dipole.size`, `SmallX.Dipole.impactParameter`: the dipole vector and the impact
  parameter.
* `SmallX.Dipole.ofSizeImpactParameter`: the dipole with prescribed size and impact parameter.
* `SmallX.Dipole.equivProd`: a dipole as the pair `(x, y)` of its endpoints, along which the
  vector-space structure is transported.
* `SmallX.Dipole.sizeImpactParameterEquiv`: the linear isomorphism `d ↦ (r, b)`.

## Main results

* `SmallX.Dipole.ext_iff_size_impactParameter`: a dipole is determined by its size and impact
  parameter.
* `SmallX.Dipole.size_eq_zero_iff`: a dipole has zero size exactly when its endpoints coincide,
  equivalently (`size_eq_zero_iff_quark_eq_impactParameter`,
  `size_eq_zero_iff_antiquark_eq_impactParameter`) when either endpoint sits at the impact
  parameter.
* `SmallX.Dipole.norm_size`: the norm of the dipole vector is the distance between the endpoints.

## References

* N. N. Nikolaev and B. G. Zakharov, *Colour transparency and scaling properties of nuclear
  shadowing in deep inelastic scattering*, Z. Phys. **C49** (1991) 607.
* A. H. Mueller, *Soft gluons in the infinite-momentum wave function and the BFKL pomeron*,
  Nucl. Phys. **B415** (1994) 373.
* Y. V. Kovchegov and E. Levin, *Quantum Chromodynamics at High Energy*, Cambridge University
  Press (2012), chapters 3-4.
-/

public section

noncomputable section

namespace EpsilonEridani
namespace QFT
namespace SmallX

/-- A colour dipole: a quark and an antiquark at two points of the transverse plane. The
endpoints are the data; the dipole vector and the impact parameter are derived from them. -/
@[ext]
structure Dipole where
  /-- The transverse position `x` of the quark. -/
  quark : EuclideanSpace ℝ (Fin 2)
  /-- The transverse position `y` of the antiquark. -/
  antiquark : EuclideanSpace ℝ (Fin 2)

namespace Dipole

/-! ### The vector-space structure of pairs of endpoints -/

/-- A dipole as the pair `(x, y)` of its quark and antiquark positions. The vector-space structure
of `Dipole` is the one of `EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)`, transported along
this equivalence. -/
def equivProd : Dipole ≃ EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) where
  toFun d := (d.quark, d.antiquark)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : AddCommGroup Dipole := equivProd.addCommGroup

instance : Module ℝ Dipole := equivProd.addEquiv.module ℝ

@[simp] lemma equivProd_apply (d : Dipole) : equivProd d = (d.quark, d.antiquark) := (rfl)

@[simp] lemma equivProd_symm_apply (p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) :
    equivProd.symm p = ⟨p.1, p.2⟩ :=
  (rfl)

/-! The transported operations act on a dipole as `equivProd.symm (op (equivProd d))`
(`Equiv.addCommGroup`, `AddEquiv.module`), and the operations of the product act componentwise,
so each endpoint equation below holds by construction, definitionally. -/

@[simp] lemma quark_zero : (0 : Dipole).quark = 0 := (rfl)

@[simp] lemma antiquark_zero : (0 : Dipole).antiquark = 0 := (rfl)

@[simp] lemma quark_add (d d' : Dipole) : (d + d').quark = d.quark + d'.quark := (rfl)

@[simp] lemma antiquark_add (d d' : Dipole) :
    (d + d').antiquark = d.antiquark + d'.antiquark := (rfl)

@[simp] lemma quark_neg (d : Dipole) : (-d).quark = -d.quark := (rfl)

@[simp] lemma antiquark_neg (d : Dipole) : (-d).antiquark = -d.antiquark := (rfl)

@[simp] lemma quark_sub (d d' : Dipole) : (d - d').quark = d.quark - d'.quark := (rfl)

@[simp] lemma antiquark_sub (d d' : Dipole) :
    (d - d').antiquark = d.antiquark - d'.antiquark := (rfl)

@[simp] lemma quark_smul (c : ℝ) (d : Dipole) : (c • d).quark = c • d.quark := (rfl)

@[simp] lemma antiquark_smul (c : ℝ) (d : Dipole) : (c • d).antiquark = c • d.antiquark := (rfl)

/-! ### Size and impact parameter -/

/-- The dipole size `r = x - y`, the transverse vector from the antiquark to the quark (also
called the dipole vector). Its norm is the distance between the endpoints. -/
def size (d : Dipole) : EuclideanSpace ℝ (Fin 2) := d.quark - d.antiquark

/-- The impact parameter `b = (x + y) / 2`, the midpoint of the two endpoints. -/
def impactParameter (d : Dipole) : EuclideanSpace ℝ (Fin 2) := midpoint ℝ d.quark d.antiquark

lemma size_def (d : Dipole) : d.size = d.quark - d.antiquark := (rfl)

lemma impactParameter_def (d : Dipole) : d.impactParameter = midpoint ℝ d.quark d.antiquark :=
  (rfl)

lemma impactParameter_eq_smul_add (d : Dipole) :
    d.impactParameter = (2 : ℝ)⁻¹ • (d.quark + d.antiquark) := by
  rw [impactParameter_def, midpoint_eq_smul_add, invOf_eq_inv]

/-- The norm of the dipole vector is the distance between the quark and the antiquark. -/
lemma norm_size (d : Dipole) : ‖d.size‖ = dist d.quark d.antiquark := by
  rw [size_def, dist_eq_norm]

/-- A dipole has zero size exactly when its quark and antiquark sit at the same point. -/
@[simp] lemma size_eq_zero_iff {d : Dipole} : d.size = 0 ↔ d.quark = d.antiquark := by
  rw [size_def, sub_eq_zero]

/-- A dipole has zero size exactly when its quark sits at its impact parameter. -/
lemma size_eq_zero_iff_quark_eq_impactParameter {d : Dipole} :
    d.size = 0 ↔ d.quark = d.impactParameter := by
  rw [impactParameter_def, left_eq_midpoint_iff, size_eq_zero_iff]

/-- A dipole has zero size exactly when its antiquark sits at its impact parameter. -/
lemma size_eq_zero_iff_antiquark_eq_impactParameter {d : Dipole} :
    d.size = 0 ↔ d.antiquark = d.impactParameter := by
  rw [impactParameter_def, right_eq_midpoint_iff, size_eq_zero_iff]

@[simp] lemma size_zero : (0 : Dipole).size = 0 := by simp [size_def]

@[simp] lemma impactParameter_zero : (0 : Dipole).impactParameter = 0 := by
  simp [impactParameter_def]

@[simp] lemma size_add (d d' : Dipole) : (d + d').size = d.size + d'.size := by
  simp only [size_def, quark_add, antiquark_add]
  abel

@[simp] lemma impactParameter_add (d d' : Dipole) :
    (d + d').impactParameter = d.impactParameter + d'.impactParameter := by
  simpa only [impactParameter_def, quark_add, antiquark_add, vadd_eq_add] using
    (midpoint_vadd_midpoint (R := ℝ) d.quark d.antiquark d'.quark d'.antiquark).symm

@[simp] lemma size_neg (d : Dipole) : (-d).size = -d.size := by
  simp only [size_def, quark_neg, antiquark_neg]
  abel

@[simp] lemma impactParameter_neg (d : Dipole) : (-d).impactParameter = -d.impactParameter := by
  simp only [impactParameter_eq_smul_add, quark_neg, antiquark_neg]
  module

@[simp] lemma size_sub (d d' : Dipole) : (d - d').size = d.size - d'.size := by
  simp only [size_def, quark_sub, antiquark_sub]
  abel

@[simp] lemma impactParameter_sub (d d' : Dipole) :
    (d - d').impactParameter = d.impactParameter - d'.impactParameter := by
  simpa only [impactParameter_def, quark_sub, antiquark_sub, vsub_eq_sub] using
    (midpoint_vsub_midpoint (R := ℝ) d.quark d.antiquark d'.quark d'.antiquark).symm

@[simp] lemma size_smul (c : ℝ) (d : Dipole) : (c • d).size = c • d.size := by
  simp only [size_def, quark_smul, antiquark_smul, smul_sub]

@[simp] lemma impactParameter_smul (c : ℝ) (d : Dipole) :
    (c • d).impactParameter = c • d.impactParameter := by
  simp only [impactParameter_eq_smul_add, quark_smul, antiquark_smul]
  module

/-- The quark sits half the dipole vector beyond the impact parameter: `x = b + r / 2`. -/
@[simp] lemma impactParameter_add_smul_size (d : Dipole) :
    d.impactParameter + (2 : ℝ)⁻¹ • d.size = d.quark := by
  rw [impactParameter_def, size_def, ← invOf_eq_inv, ← left_sub_midpoint, add_sub_cancel]

/-- The antiquark sits half the dipole vector before the impact parameter: `y = b - r / 2`. -/
@[simp] lemma impactParameter_sub_smul_size (d : Dipole) :
    d.impactParameter - (2 : ℝ)⁻¹ • d.size = d.antiquark := by
  rw [impactParameter_def, size_def, ← invOf_eq_inv, ← midpoint_sub_right, sub_sub_cancel]

/-! ### Reconstruction from size and impact parameter -/

/-- The dipole of dipole vector `r` and impact parameter `b`: its quark sits at `b + r / 2` and its
antiquark at `b - r / 2`. -/
def ofSizeImpactParameter (r b : EuclideanSpace ℝ (Fin 2)) : Dipole :=
  ⟨b + (2 : ℝ)⁻¹ • r, b - (2 : ℝ)⁻¹ • r⟩

@[simp] lemma quark_ofSizeImpactParameter (r b : EuclideanSpace ℝ (Fin 2)) :
    (ofSizeImpactParameter r b).quark = b + (2 : ℝ)⁻¹ • r :=
  (rfl)

@[simp] lemma antiquark_ofSizeImpactParameter (r b : EuclideanSpace ℝ (Fin 2)) :
    (ofSizeImpactParameter r b).antiquark = b - (2 : ℝ)⁻¹ • r :=
  (rfl)

@[simp] lemma size_ofSizeImpactParameter (r b : EuclideanSpace ℝ (Fin 2)) :
    (ofSizeImpactParameter r b).size = r := by
  rw [size_def, quark_ofSizeImpactParameter, antiquark_ofSizeImpactParameter]
  module

@[simp] lemma impactParameter_ofSizeImpactParameter (r b : EuclideanSpace ℝ (Fin 2)) :
    (ofSizeImpactParameter r b).impactParameter = b := by
  rw [impactParameter_def, quark_ofSizeImpactParameter, antiquark_ofSizeImpactParameter,
    midpoint_add_sub]

@[simp] lemma ofSizeImpactParameter_size_impactParameter (d : Dipole) :
    ofSizeImpactParameter d.size d.impactParameter = d := by
  ext1 <;> simp

/-- The diagonal dipole at `b` is the dipole of zero size at impact parameter `b`. -/
lemma ofSizeImpactParameter_zero_left (b : EuclideanSpace ℝ (Fin 2)) :
    ofSizeImpactParameter 0 b = ⟨b, b⟩ := by
  ext1 <;> simp

/-- The change of variables from the endpoints `(x, y)` of a dipole to its dipole vector and
impact parameter `(r, b) = (x - y, (x + y) / 2)` is a linear isomorphism, with inverse
`(r, b) ↦ (b + r / 2, b - r / 2)`. -/
def sizeImpactParameterEquiv :
    Dipole ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) where
  toFun d := (d.size, d.impactParameter)
  invFun p := ofSizeImpactParameter p.1 p.2
  map_add' d d' := by simp
  map_smul' c d := by simp
  left_inv := ofSizeImpactParameter_size_impactParameter
  right_inv p := by simp

@[simp] lemma sizeImpactParameterEquiv_apply (d : Dipole) :
    sizeImpactParameterEquiv d = (d.size, d.impactParameter) :=
  (rfl)

@[simp] lemma sizeImpactParameterEquiv_symm_apply
    (p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) :
    sizeImpactParameterEquiv.symm p = ofSizeImpactParameter p.1 p.2 :=
  (rfl)

/-- Two dipoles are equal exactly when they have the same dipole vector and the same impact
parameter. -/
lemma ext_iff_size_impactParameter {d d' : Dipole} :
    d = d' ↔ d.size = d'.size ∧ d.impactParameter = d'.impactParameter :=
  ⟨fun h => h ▸ ⟨rfl, rfl⟩, fun h => sizeImpactParameterEquiv.injective (Prod.ext h.1 h.2)⟩

end Dipole

end SmallX
end QFT
end EpsilonEridani
