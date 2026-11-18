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

* the dipole vector `r = x - y` (`Dipole.size`), whose norm is the dipole size `|r|`, and
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
* `SmallX.Dipole.endpointsEquiv`: a dipole as the pair `(x, y)` of its endpoints.
* `SmallX.Dipole.sizeImpactParameterEquiv`: the linear isomorphism `d ↦ (r, b)`.

## Main results

* `SmallX.Dipole.ext_iff_size_impactParameter`: a dipole is determined by its size and impact
  parameter.
* `SmallX.Dipole.size_eq_zero_iff`: a dipole has zero size exactly when its endpoints coincide.
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

instance : Zero Dipole := ⟨⟨0, 0⟩⟩

instance : Add Dipole := ⟨fun d d' => ⟨d.quark + d'.quark, d.antiquark + d'.antiquark⟩⟩

instance : Neg Dipole := ⟨fun d => ⟨-d.quark, -d.antiquark⟩⟩

instance : Sub Dipole := ⟨fun d d' => ⟨d.quark - d'.quark, d.antiquark - d'.antiquark⟩⟩

instance {S : Type*} [SMul S (EuclideanSpace ℝ (Fin 2))] : SMul S Dipole :=
  ⟨fun c d => ⟨c • d.quark, c • d.antiquark⟩⟩

@[simp] lemma zero_quark : (0 : Dipole).quark = 0 := (rfl)

@[simp] lemma zero_antiquark : (0 : Dipole).antiquark = 0 := (rfl)

@[simp] lemma add_quark (d d' : Dipole) : (d + d').quark = d.quark + d'.quark := (rfl)

@[simp] lemma add_antiquark (d d' : Dipole) :
    (d + d').antiquark = d.antiquark + d'.antiquark := (rfl)

@[simp] lemma neg_quark (d : Dipole) : (-d).quark = -d.quark := (rfl)

@[simp] lemma neg_antiquark (d : Dipole) : (-d).antiquark = -d.antiquark := (rfl)

@[simp] lemma sub_quark (d d' : Dipole) : (d - d').quark = d.quark - d'.quark := (rfl)

@[simp] lemma sub_antiquark (d d' : Dipole) :
    (d - d').antiquark = d.antiquark - d'.antiquark := (rfl)

@[simp] lemma smul_quark {S : Type*} [SMul S (EuclideanSpace ℝ (Fin 2))] (c : S) (d : Dipole) :
    (c • d).quark = c • d.quark := (rfl)

@[simp] lemma smul_antiquark {S : Type*} [SMul S (EuclideanSpace ℝ (Fin 2))] (c : S)
    (d : Dipole) : (c • d).antiquark = c • d.antiquark := (rfl)

instance : AddCommGroup Dipole :=
  Function.Injective.addCommGroup (fun d : Dipole => (d.quark, d.antiquark))
    (fun _ _ h => Dipole.ext_iff.2 (Prod.ext_iff.1 h)) rfl (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

instance : Module ℝ Dipole :=
  Function.Injective.module ℝ (AddMonoidHom.mk' (fun d : Dipole => (d.quark, d.antiquark))
    fun _ _ => rfl) (fun _ _ h => Dipole.ext_iff.2 (Prod.ext_iff.1 h)) fun _ _ => rfl

/-- A dipole is the pair `(x, y)` of its quark and antiquark positions. -/
def endpointsEquiv : Dipole ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) where
  toFun d := (d.quark, d.antiquark)
  invFun p := ⟨p.1, p.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] lemma endpointsEquiv_apply (d : Dipole) : endpointsEquiv d = (d.quark, d.antiquark) :=
  (rfl)

@[simp] lemma endpointsEquiv_symm_apply (p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) :
    endpointsEquiv.symm p = ⟨p.1, p.2⟩ :=
  (rfl)

/-! ### Size and impact parameter -/

/-- The dipole vector `r = x - y`, from the antiquark to the quark. Its norm is the dipole
size. -/
def size (d : Dipole) : EuclideanSpace ℝ (Fin 2) := d.quark - d.antiquark

/-- The impact parameter `b = (x + y) / 2`, the midpoint of the two endpoints. -/
def impactParameter (d : Dipole) : EuclideanSpace ℝ (Fin 2) := midpoint ℝ d.quark d.antiquark

lemma size_def (d : Dipole) : d.size = d.quark - d.antiquark := (rfl)

lemma impactParameter_def (d : Dipole) : d.impactParameter = midpoint ℝ d.quark d.antiquark :=
  (rfl)

lemma impactParameter_eq_smul_add (d : Dipole) :
    d.impactParameter = (2 : ℝ)⁻¹ • (d.quark + d.antiquark) := by
  rw [impactParameter_def, midpoint_eq_smul_add, invOf_eq_inv]

@[simp] lemma size_mk (x y : EuclideanSpace ℝ (Fin 2)) : (⟨x, y⟩ : Dipole).size = x - y := (rfl)

@[simp] lemma impactParameter_mk (x y : EuclideanSpace ℝ (Fin 2)) :
    (⟨x, y⟩ : Dipole).impactParameter = midpoint ℝ x y :=
  (rfl)

/-- The norm of the dipole vector is the distance between the quark and the antiquark. -/
lemma norm_size (d : Dipole) : ‖d.size‖ = dist d.quark d.antiquark := by
  rw [size_def, dist_eq_norm]

/-- A dipole has zero size exactly when its quark and antiquark sit at the same point. -/
lemma size_eq_zero_iff {d : Dipole} : d.size = 0 ↔ d.quark = d.antiquark := by
  rw [size_def, sub_eq_zero]

/-- A dipole of zero size sits at its impact parameter. -/
lemma quark_eq_impactParameter_of_size_eq_zero {d : Dipole} (h : d.size = 0) :
    d.quark = d.impactParameter := by
  rw [impactParameter_def, size_eq_zero_iff.1 h, midpoint_self]

@[simp] lemma size_zero : (0 : Dipole).size = 0 := sub_zero _

@[simp] lemma impactParameter_zero : (0 : Dipole).impactParameter = 0 := midpoint_self ℝ _

@[simp] lemma size_add (d d' : Dipole) : (d + d').size = d.size + d'.size := by
  simp only [size_def, add_quark, add_antiquark]
  abel

@[simp] lemma impactParameter_add (d d' : Dipole) :
    (d + d').impactParameter = d.impactParameter + d'.impactParameter := by
  simp only [impactParameter_eq_smul_add, add_quark, add_antiquark]
  module

@[simp] lemma size_neg (d : Dipole) : (-d).size = -d.size := by
  simp only [size_def, neg_quark, neg_antiquark]
  abel

@[simp] lemma impactParameter_neg (d : Dipole) : (-d).impactParameter = -d.impactParameter := by
  simp only [impactParameter_eq_smul_add, neg_quark, neg_antiquark]
  module

@[simp] lemma size_sub (d d' : Dipole) : (d - d').size = d.size - d'.size := by
  simp only [size_def, sub_quark, sub_antiquark]
  abel

@[simp] lemma impactParameter_sub (d d' : Dipole) :
    (d - d').impactParameter = d.impactParameter - d'.impactParameter := by
  simp only [impactParameter_eq_smul_add, sub_quark, sub_antiquark]
  module

@[simp] lemma size_smul (c : ℝ) (d : Dipole) : (c • d).size = c • d.size := by
  simp only [size_def, smul_quark, smul_antiquark, smul_sub]

@[simp] lemma impactParameter_smul (c : ℝ) (d : Dipole) :
    (c • d).impactParameter = c • d.impactParameter := by
  simp only [impactParameter_eq_smul_add, smul_quark, smul_antiquark]
  module

/-- The quark sits half the dipole vector beyond the impact parameter: `x = b + r / 2`. -/
lemma impactParameter_add_size (d : Dipole) :
    d.impactParameter + (2 : ℝ)⁻¹ • d.size = d.quark := by
  rw [impactParameter_eq_smul_add, size_def]
  module

/-- The antiquark sits half the dipole vector before the impact parameter: `y = b - r / 2`. -/
lemma impactParameter_sub_size (d : Dipole) :
    d.impactParameter - (2 : ℝ)⁻¹ • d.size = d.antiquark := by
  rw [impactParameter_eq_smul_add, size_def]
  module

/-! ### Reconstruction from size and impact parameter -/

/-- The dipole of dipole vector `r` and impact parameter `b`: its quark sits at `b + r / 2` and its
antiquark at `b - r / 2`. -/
def ofSizeImpactParameter (r b : EuclideanSpace ℝ (Fin 2)) : Dipole :=
  ⟨b + (2 : ℝ)⁻¹ • r, b - (2 : ℝ)⁻¹ • r⟩

@[simp] lemma ofSizeImpactParameter_quark (r b : EuclideanSpace ℝ (Fin 2)) :
    (ofSizeImpactParameter r b).quark = b + (2 : ℝ)⁻¹ • r :=
  (rfl)

@[simp] lemma ofSizeImpactParameter_antiquark (r b : EuclideanSpace ℝ (Fin 2)) :
    (ofSizeImpactParameter r b).antiquark = b - (2 : ℝ)⁻¹ • r :=
  (rfl)

@[simp] lemma size_ofSizeImpactParameter (r b : EuclideanSpace ℝ (Fin 2)) :
    (ofSizeImpactParameter r b).size = r := by
  rw [size_def, ofSizeImpactParameter_quark, ofSizeImpactParameter_antiquark]
  module

@[simp] lemma impactParameter_ofSizeImpactParameter (r b : EuclideanSpace ℝ (Fin 2)) :
    (ofSizeImpactParameter r b).impactParameter = b := by
  rw [impactParameter_def, ofSizeImpactParameter_quark, ofSizeImpactParameter_antiquark,
    midpoint_add_sub]

@[simp] lemma ofSizeImpactParameter_size_impactParameter (d : Dipole) :
    ofSizeImpactParameter d.size d.impactParameter = d := by
  ext1
  · exact impactParameter_add_size d
  · exact impactParameter_sub_size d

/-- The diagonal dipole at `b` is the dipole of zero size at impact parameter `b`. -/
lemma ofSizeImpactParameter_zero (b : EuclideanSpace ℝ (Fin 2)) :
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
    d = d' ↔ d.size = d'.size ∧ d.impactParameter = d'.impactParameter := by
  rw [← Prod.mk.injEq, ← sizeImpactParameterEquiv_apply, ← sizeImpactParameterEquiv_apply,
    sizeImpactParameterEquiv.injective.eq_iff]

end Dipole

end SmallX
end QFT
end EpsilonEridani
