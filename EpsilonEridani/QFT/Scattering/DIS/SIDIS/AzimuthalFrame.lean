/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.Mathematics.Geometry.Euclidean.Angle.Oriented.Basic
public import EpsilonEridani.Mathematics.InnerProductSpace.Orientation
public import EpsilonEridani.Relativity.Tensors.RealTensor.Vector.LightFront

/-!
# The azimuthal frame of semi-inclusive DIS and the Trento convention

In semi-inclusive deep-inelastic scattering `ℓ(l) + N(P, S) → ℓ(l') + h(P_h) + X` the angular
dependence of the cross section is carried by two azimuths about the virtual-photon direction: the
azimuth `φ_h` of the produced hadron and the azimuth `φ_S` of the target spin, both measured from
the lepton plane. They are defined in a frame in which the target and the virtual photon
`q = l - l'` move along the `z`-axis. This file works in the light-front components of
`EpsilonEridani.Relativity.Tensors.RealTensor.Vector.LightFront`, where the `z`-axis is the
longitudinal axis, so a frame of this kind is one in which `q` has no transverse part. Azimuths
are then oriented angles in the transverse plane `EuclideanSpace ℝ (Fin 2)`.

An `AzimuthalFrame` is the data such an angle needs beyond the photon axis: the reference
direction `leptonDir` in the transverse plane and an orientation of that plane. In a physical
frame `leptonDir` is the transverse part of the incoming lepton momentum, so the half-plane it
spans with the photon axis is the lepton plane. The azimuth of a four-vector `p` is the oriented
angle from `leptonDir` to `p_T`. Then `φ_h = F.azimuth P_h` and `φ_S = F.azimuth S`. They take
values in `Real.Angle`, so no branch cut is chosen.

The orientation is a genuine choice. The Trento convention (Bacchetta, D'Alesio, Diehl and
Miller) measures azimuths in a right-handed frame whose `z`-axis points along the virtual-photon
three-momentum `q` and whose `x`-axis points along the lepton's transverse momentum. In
coordinates

  `cos φ_h = (l_T · P_hT) / (|l_T| |P_hT|)`,  `sin φ_h = (q × l) · P_h / (|q| |l_T| |P_hT|)`.

Rotating counterclockwise about `+z` is the standard orientation of the transverse plane
(`EuclideanSpace.orientation`). So Trento's orientation is the standard one when the photon moves
along `+z` and the opposite one when it moves along `-z`. This is `trentoOrientation q`, and
`trento l q` is the Trento frame of the lepton momentum `l` and the photon momentum `q`. Its
azimuths satisfy the two formulas above (`cos_azimuth_trento`, `sin_azimuth_trento`).

Two properties make the pair `(φ_h, φ_S)` a usable set of variables. First, it is invariant
under boosts along the photon direction. Such a boost does not change transverse parts. It also
cannot reverse the direction of the spacelike photon momentum. So it maps the Trento frame of
`(l, q)` to the Trento frame of the boosted momenta, and it preserves every azimuth
(`azimuth_trento_boost`). The azimuthal analysis is therefore the same in the target rest frame
and in any collinear frame reached from it along the photon axis. Second, the opposite
orientation negates both azimuths (`azimuth_reverse`). So a cross section whose modulations are
`cos(m φ_h + n φ_S)` and `sin(m φ_h + n φ_S)` keeps its cosine amplitudes and flips the sign of
its sine amplitudes when it is written in the other convention (`sum_cos_add_sin_reverse`). The
Sivers modulation `sin(φ_h - φ_S)` and the Collins modulation `sin(φ_h + φ_S)` are of this kind.
This is the sign by which single-transverse-spin asymmetries quoted in the two conventions differ.

## Main definitions

* `EpsilonEridani.QFT.Scattering.DIS.SIDIS.AzimuthalFrame`: a reference direction and an
  orientation of the transverse plane.
* `AzimuthalFrame.azimuth F p`: the azimuth of the four-vector `p` about the photon axis.
* `AzimuthalFrame.reverse F`: the frame with the opposite orientation.
* `AzimuthalFrame.trentoOrientation q`: the orientation fixed by the Trento convention for a
  photon momentum `q` along the `z`-axis.
* `AzimuthalFrame.trento l q`: the Trento frame of the lepton momentum `l` and the photon
  momentum `q`.

## Main statements

* `AzimuthalFrame.cos_azimuth_trento`, `AzimuthalFrame.sin_azimuth_trento`: the Trento azimuths
  in coordinates.
* `AzimuthalFrame.azimuth_trento_lepton`: the lepton lies at azimuth zero.
* `AzimuthalFrame.trento_boost`, `AzimuthalFrame.azimuth_trento_boost`: the Trento frame and the
  azimuths it defines are invariant under boosts along the photon direction.
* `AzimuthalFrame.azimuth_reverse`: the opposite orientation negates every azimuth.
* `AzimuthalFrame.sin_azimuth_reverse`, `AzimuthalFrame.cos_azimuth_reverse`,
  `AzimuthalFrame.sum_cos_add_sin_reverse`: under the opposite orientation the sine modulations
  change sign and the cosine modulations do not.

## References

* A. Bacchetta, U. D'Alesio, M. Diehl and C. A. Miller, *Single-spin asymmetries: the Trento
  conventions*, Phys. Rev. D 70 (2004) 117504, arXiv:hep-ph/0410050.
* A. Bacchetta, M. Diehl, K. Goeke, A. Metz, P. J. Mulders and M. Schlegel, *Semi-inclusive deep
  inelastic scattering at small transverse momentum*, JHEP 02 (2007) 093, arXiv:hep-ph/0611265.
-/

public section

noncomputable section

namespace EpsilonEridani.QFT.Scattering.DIS.SIDIS

open scoped EuclideanSpace Lorentz.Vector
open Lorentz.Vector (transversePart)
open LorentzGroup (boost)

/-- The transverse plane. -/
local notation "E²" => EuclideanSpace ℝ (Fin 2)

/-- An azimuthal frame: the data that measure azimuths about the photon axis, which is the
`z`-axis of the light-front components. `leptonDir` is the reference direction in the transverse
plane. In a physical frame it is the transverse part of the incoming lepton momentum, so that
together with the photon axis it spans the lepton plane. `orientation` is the sense in which
azimuths increase. -/
@[ext]
structure AzimuthalFrame where
  /-- The reference direction in the transverse plane, from which azimuths are measured. -/
  leptonDir : E²
  /-- The orientation of the transverse plane. -/
  orientation : Orientation ℝ E² (Fin 2)

namespace AzimuthalFrame

/-! ### Azimuths -/

/-- The azimuth of a four-vector `p` about the photon axis: the oriented angle from the reference
direction of the frame to the transverse part of `p`. The hadron azimuth `φ_h` is the azimuth of
the hadron momentum and the spin azimuth `φ_S` that of the target spin vector. It is `0` when `p`
or the reference direction has no transverse part. -/
def azimuth (F : AzimuthalFrame) (p : Lorentz.Vector 3) : Real.Angle :=
  F.orientation.oangle F.leptonDir (transversePart p)

lemma azimuth_def (F : AzimuthalFrame) (p : Lorentz.Vector 3) :
    F.azimuth p = F.orientation.oangle F.leptonDir (transversePart p) := (rfl)

/-- A four-vector whose transverse part is the reference direction lies at azimuth zero. -/
lemma azimuth_eq_zero_of_transversePart_eq {F : AzimuthalFrame} {p : Lorentz.Vector 3}
    (hp : transversePart p = F.leptonDir) : F.azimuth p = 0 := by
  rw [azimuth_def, hp, Orientation.oangle_self]

/-- A boost along the photon axis does not change any azimuth. -/
@[simp]
lemma azimuth_boost (F : AzimuthalFrame) (β : ℝ) (hβ : |β| < 1) (p : Lorentz.Vector 3) :
    F.azimuth (boost (2 : Fin 3) β hβ • p) = F.azimuth p := by
  rw [azimuth_def, Lorentz.Vector.transversePart_boost_two, azimuth_def]

/-! ### Reversing the orientation -/

/-- The frame with the same reference direction and the opposite orientation. -/
def reverse (F : AzimuthalFrame) : AzimuthalFrame where
  leptonDir := F.leptonDir
  orientation := -F.orientation

@[simp]
lemma leptonDir_reverse (F : AzimuthalFrame) : F.reverse.leptonDir = F.leptonDir := (rfl)

@[simp]
lemma orientation_reverse (F : AzimuthalFrame) : F.reverse.orientation = -F.orientation := (rfl)

@[simp]
lemma reverse_reverse (F : AzimuthalFrame) : F.reverse.reverse = F := by
  ext1
  · simp
  · exact neg_neg F.orientation

/-- Reversing the orientation negates every azimuth. -/
@[simp]
lemma azimuth_reverse (F : AzimuthalFrame) (p : Lorentz.Vector 3) :
    F.reverse.azimuth p = -F.azimuth p := by
  rw [azimuth_def, azimuth_def, orientation_reverse, leptonDir_reverse,
    Orientation.oangle_neg_orientation_eq_neg]

/-- Under the opposite orientation every sine modulation `sin(m φ_h + n φ_S)` changes sign. -/
lemma sin_azimuth_reverse (F : AzimuthalFrame) (m n : ℤ) (Ph S : Lorentz.Vector 3) :
    Real.Angle.sin (m • F.reverse.azimuth Ph + n • F.reverse.azimuth S) =
      -Real.Angle.sin (m • F.azimuth Ph + n • F.azimuth S) := by
  rw [azimuth_reverse, azimuth_reverse, smul_neg, smul_neg, ← neg_add, Real.Angle.sin_neg]

/-- Under the opposite orientation every cosine modulation `cos(m φ_h + n φ_S)` is unchanged. -/
lemma cos_azimuth_reverse (F : AzimuthalFrame) (m n : ℤ) (Ph S : Lorentz.Vector 3) :
    Real.Angle.cos (m • F.reverse.azimuth Ph + n • F.reverse.azimuth S) =
      Real.Angle.cos (m • F.azimuth Ph + n • F.azimuth S) := by
  rw [azimuth_reverse, azimuth_reverse, smul_neg, smul_neg, ← neg_add, Real.Angle.cos_neg]

/-- The structure functions in the two orientations. A finite sum of modulations with cosine
amplitudes `A i` and sine amplitudes `B i` of the harmonics `m i φ_h + n i φ_S` is, written in the
azimuths of the reversed frame, the sum with the same cosine amplitudes and the sine amplitudes
`-B i`. -/
theorem sum_cos_add_sin_reverse (F : AzimuthalFrame) {ι : Type*} (s : Finset ι) (m n : ι → ℤ)
    (A B : ι → ℝ) (Ph S : Lorentz.Vector 3) :
    ∑ i ∈ s, (A i * Real.Angle.cos (m i • F.azimuth Ph + n i • F.azimuth S) +
        B i * Real.Angle.sin (m i • F.azimuth Ph + n i • F.azimuth S)) =
      ∑ i ∈ s, (A i * Real.Angle.cos (m i • F.reverse.azimuth Ph + n i • F.reverse.azimuth S) +
        -B i * Real.Angle.sin (m i • F.reverse.azimuth Ph + n i • F.reverse.azimuth S)) := by
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [cos_azimuth_reverse, sin_azimuth_reverse, neg_mul_neg]

/-! ### The Trento convention -/

/-- The orientation of the Trento convention for a photon momentum `q` along the `z`-axis:
azimuths increase counterclockwise about the photon three-momentum. This is the standard
orientation of the transverse plane when the photon moves along `+z`, and the opposite one
otherwise. -/
def trentoOrientation (q : Lorentz.Vector 3) : Orientation ℝ E² (Fin 2) :=
  if 0 < q (Sum.inr 2) then EuclideanSpace.orientation (Fin 2)
  else -EuclideanSpace.orientation (Fin 2)

lemma trentoOrientation_of_pos {q : Lorentz.Vector 3} (hq : 0 < q (Sum.inr 2)) :
    trentoOrientation q = EuclideanSpace.orientation (Fin 2) := by
  exact ite_eq_left_iff.2 fun h => absurd hq h

lemma trentoOrientation_of_nonpos {q : Lorentz.Vector 3} (hq : q (Sum.inr 2) ≤ 0) :
    trentoOrientation q = -EuclideanSpace.orientation (Fin 2) := by
  exact ite_eq_right_iff.2 fun h => absurd h hq.not_gt

/-- The Trento frame of the incoming lepton momentum `l` and the photon momentum `q`: azimuths
are measured from the transverse part of `l` in the Trento orientation. -/
def trento (l q : Lorentz.Vector 3) : AzimuthalFrame where
  leptonDir := transversePart l
  orientation := trentoOrientation q

@[simp]
lemma leptonDir_trento (l q : Lorentz.Vector 3) : (trento l q).leptonDir = transversePart l :=
  (rfl)

@[simp]
lemma orientation_trento (l q : Lorentz.Vector 3) :
    (trento l q).orientation = trentoOrientation q := (rfl)

/-- The incoming lepton lies at azimuth zero in its Trento frame. -/
@[simp]
lemma azimuth_trento_lepton (l q : Lorentz.Vector 3) : (trento l q).azimuth l = 0 :=
  azimuth_eq_zero_of_transversePart_eq (leptonDir_trento l q).symm

/-- In a frame where the photon has no transverse part, the scattered lepton `l' = l - q` defines
the same Trento frame as the incoming one: both span the lepton plane with the photon axis. -/
lemma trento_sub_photon (l : Lorentz.Vector 3) {q : Lorentz.Vector 3}
    (hq : transversePart q = 0) : trento (l - q) q = trento l q := by
  ext1 <;> simp [hq]

/-- The cosine of a Trento azimuth: `|l_T| |p_T| cos φ = l_T · p_T`. -/
theorem cos_azimuth_trento (l q p : Lorentz.Vector 3) :
    ‖transversePart l‖ * ‖transversePart p‖ * Real.Angle.cos ((trento l q).azimuth p) =
      l (Sum.inr 0) * p (Sum.inr 0) + l (Sum.inr 1) * p (Sum.inr 1) := by
  rw [azimuth_def, leptonDir_trento, ← Orientation.inner_eq_norm_mul_norm_mul_cos_oangle]
  simp [PiLp.inner_apply, Fin.sum_univ_two, mul_comm]

/-- The sine of a Trento azimuth, for a photon momentum `q` along the `z`-axis:
`|q| |l_T| |p_T| sin φ = (q × l) · p` for the spatial parts, whose right-hand side is
`q³ (l¹ p² - l² p¹)` when `q = q³ e_z`. -/
theorem sin_azimuth_trento (l q p : Lorentz.Vector 3) :
    |q (Sum.inr 2)| * (‖transversePart l‖ * ‖transversePart p‖ *
        Real.Angle.sin ((trento l q).azimuth p)) =
      q (Sum.inr 2) * (l (Sum.inr 0) * p (Sum.inr 1) - l (Sum.inr 1) * p (Sum.inr 0)) := by
  rw [azimuth_def, leptonDir_trento, orientation_trento,
    ← Orientation.areaForm_eq_norm_mul_norm_mul_sin_oangle]
  rcases le_or_gt (q (Sum.inr 2)) 0 with hle | hpos
  · rw [trentoOrientation_of_nonpos hle, Orientation.areaForm_neg_orientation, abs_of_nonpos hle]
    simp only [LinearMap.neg_apply, EuclideanSpace.areaForm_orientation_apply,
      Lorentz.Vector.transversePart_apply_zero, Lorentz.Vector.transversePart_apply_one]
    ring
  · rw [trentoOrientation_of_pos hpos, abs_of_pos hpos,
      EuclideanSpace.areaForm_orientation_apply, Lorentz.Vector.transversePart_apply_zero,
      Lorentz.Vector.transversePart_apply_one, Lorentz.Vector.transversePart_apply_zero,
      Lorentz.Vector.transversePart_apply_one]

/-! ### Invariance under boosts along the photon direction -/

/-- A boost along the photon direction maps the Trento frame of `(l, q)` to the Trento frame of
the boosted momenta, for a spacelike photon momentum `q` along the `z`-axis. -/
theorem trento_boost (l : Lorentz.Vector 3) {q : Lorentz.Vector 3} (hT : transversePart q = 0)
    (hq : ⟪q, q⟫ₘ < 0) (β : ℝ) (hβ : |β| < 1) :
    trento (boost (2 : Fin 3) β hβ • l) (boost (2 : Fin 3) β hβ • q) = trento l q := by
  ext1
  · simp
  · simp only [orientation_trento, trentoOrientation,
      Lorentz.Vector.boost_two_inr_two_pos_iff hT hq]

/-- The azimuths `φ_h` and `φ_S` are invariant under boosts along the photon direction: boosting
the lepton, the photon and the four-vector `p` together leaves the Trento azimuth of `p`
unchanged, for a spacelike photon momentum `q` along the `z`-axis. -/
theorem azimuth_trento_boost (l : Lorentz.Vector 3) {q : Lorentz.Vector 3}
    (hT : transversePart q = 0) (hq : ⟪q, q⟫ₘ < 0) (β : ℝ) (hβ : |β| < 1)
    (p : Lorentz.Vector 3) :
    (trento (boost (2 : Fin 3) β hβ • l) (boost (2 : Fin 3) β hβ • q)).azimuth
        (boost (2 : Fin 3) β hβ • p) = (trento l q).azimuth p := by
  rw [trento_boost l hT hq, azimuth_boost]

end AzimuthalFrame

end EpsilonEridani.QFT.Scattering.DIS.SIDIS
