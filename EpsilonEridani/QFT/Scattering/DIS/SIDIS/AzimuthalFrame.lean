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
spans with the photon axis is the lepton plane. The azimuth of a vector of the transverse plane is
the oriented angle from `leptonDir` to it, and the azimuth of a four-vector `p` is that of its
transverse part `p_T`. Then `φ_h = F.azimuth P_hT` and `φ_S = F.azimuth S_T`. They take values in
`Real.Angle`, so no branch cut is chosen.

The orientation is a genuine choice. The Trento convention (Bacchetta, D'Alesio, Diehl and
Miller) measures azimuths in a right-handed frame whose `z`-axis points along the virtual-photon
three-momentum `q` and whose `x`-axis points along the lepton's transverse momentum. In
coordinates

  `cos φ_h = (l_T · P_hT) / (|l_T| |P_hT|)`,  `sin φ_h = (q × l) · P_h / (|q| |l_T| |P_hT|)`.

Rotating counterclockwise about `+z` is the standard orientation of the transverse plane
(`EuclideanSpace.orientation`). So Trento's orientation is the standard one when the photon moves
along `+z` and the opposite one when it moves along `-z`. This is `trentoOrientation q`, and
`trento l q` is the Trento frame of the lepton momentum `l` and the photon momentum `q`. Its
azimuths satisfy the two formulas above (`norm_mul_norm_mul_cos_azimuth_of_leptonDir_eq`,
`abs_inr_two_mul_norm_mul_norm_mul_sin_azimuth_trento`).

Two properties make the pair `(φ_h, φ_S)` a usable set of variables. First, it is invariant
under boosts along the photon direction. Such a boost does not change transverse parts. It also
cannot reverse the direction of the spacelike photon momentum. So it maps the Trento frame of
`(l, q)` to the Trento frame of the boosted momenta, and it preserves every azimuth
(`azimuth_trento_boost_two`). The azimuthal analysis is therefore the same in the target rest frame
and in any collinear frame reached from it along the photon axis. Second, the opposite
orientation negates both azimuths (`azimuth_negOrientation`). So a cross section whose
modulations are `cos(m φ_h + n φ_S)` and `sin(m φ_h + n φ_S)` keeps its cosine amplitudes and
flips the sign of its sine amplitudes when it is written in the other convention
(`sum_cos_add_sin_negOrientation`). The Sivers modulation `sin(φ_h - φ_S)` and the Collins
modulation `sin(φ_h + φ_S)` are of this kind. This is the sign by which single-transverse-spin
asymmetries quoted in the two conventions differ.

## Main definitions

* `EpsilonEridani.QFT.Scattering.DIS.SIDIS.AzimuthalFrame`: a reference direction and an
  orientation of the transverse plane.
* `AzimuthalFrame.azimuth F v`: the azimuth of the vector `v` of the transverse plane about the
  photon axis.
* `AzimuthalFrame.negOrientation F`: the frame with the opposite orientation.
* `AzimuthalFrame.trentoOrientation q`: the orientation fixed by the Trento convention for a
  photon momentum `q` along the `z`-axis.
* `AzimuthalFrame.trento l q`: the Trento frame of the lepton momentum `l` and the photon
  momentum `q`.

## Main statements

* `AzimuthalFrame.inner_eq_norm_mul_norm_mul_cos_azimuth`,
  `AzimuthalFrame.areaForm_eq_norm_mul_norm_mul_sin_azimuth`: the cosine and the sine of an azimuth
  in any frame.
* `AzimuthalFrame.norm_mul_norm_mul_cos_azimuth_of_leptonDir_eq`,
  `AzimuthalFrame.abs_inr_two_mul_norm_mul_norm_mul_sin_azimuth_trento`: the azimuths measured
  from the lepton direction, and in particular the Trento azimuths, in coordinates.
* `AzimuthalFrame.azimuth_trento_self_eq_zero`: the lepton lies at azimuth zero.
* `AzimuthalFrame.trento_boost_two`, `AzimuthalFrame.azimuth_trento_boost_two`: the Trento frame
  and the azimuths it defines are invariant under boosts along the photon direction.
* `AzimuthalFrame.azimuth_negOrientation`: the opposite orientation negates every azimuth.
* `AzimuthalFrame.sin_zsmul_azimuth_add_zsmul_azimuth_negOrientation`,
  `AzimuthalFrame.cos_zsmul_azimuth_add_zsmul_azimuth_negOrientation`,
  `AzimuthalFrame.mul_cos_add_mul_sin_negOrientation`,
  `AzimuthalFrame.sum_cos_add_sin_negOrientation`: under the opposite orientation the sine
  modulations change sign and the cosine modulations do not.

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

/-- The azimuth of a vector `v` of the transverse plane: the oriented angle from the reference
direction of the frame to `v`. The azimuth of a four-vector `p` about the photon axis is that of
its transverse part, `F.azimuth (transversePart p)`. The hadron azimuth `φ_h` is the azimuth of the
transverse hadron momentum and the spin azimuth `φ_S` that of the transverse target spin; the
azimuth of a transverse momentum such as `Lorentz.Vector.relativeTransverse k P` is defined in the
same way. It is `0` when `v` or the reference direction is `0`. -/
def azimuth (F : AzimuthalFrame) (v : E²) : Real.Angle :=
  F.orientation.oangle F.leptonDir v

lemma azimuth_def (F : AzimuthalFrame) (v : E²) :
    F.azimuth v = F.orientation.oangle F.leptonDir v := (rfl)

/-- The reference direction lies at azimuth zero. -/
@[simp]
lemma azimuth_leptonDir (F : AzimuthalFrame) : F.azimuth F.leptonDir = 0 := by
  rw [azimuth_def, Orientation.oangle_self]

/-- The zero vector lies at azimuth zero. -/
@[simp]
lemma azimuth_zero (F : AzimuthalFrame) : F.azimuth 0 = 0 := by
  rw [azimuth_def, Orientation.oangle_zero_right]

/-- In a frame whose reference direction is zero every azimuth is zero. -/
@[simp]
lemma azimuth_eq_zero_of_leptonDir_eq_zero {F : AzimuthalFrame} (hF : F.leptonDir = 0) (v : E²) :
    F.azimuth v = 0 := by
  rw [azimuth_def, hF, Orientation.oangle_zero_left]

/-- The cosine of an azimuth: `l_T · v = |l_T| |v| cos φ`, where `l_T` is the reference
direction. It does not depend on the orientation of the frame. -/
theorem inner_eq_norm_mul_norm_mul_cos_azimuth (F : AzimuthalFrame) (v : E²) :
    inner ℝ F.leptonDir v = ‖F.leptonDir‖ * ‖v‖ * Real.Angle.cos (F.azimuth v) := by
  rw [azimuth_def, Orientation.inner_eq_norm_mul_norm_mul_cos_oangle]

/-- The sine of an azimuth: `ω(l_T, v) = |l_T| |v| sin φ`, where `l_T` is the reference direction
and `ω` the area form of the orientation of the frame. -/
theorem areaForm_eq_norm_mul_norm_mul_sin_azimuth (F : AzimuthalFrame) (v : E²) :
    F.orientation.areaForm F.leptonDir v = ‖F.leptonDir‖ * ‖v‖ * Real.Angle.sin (F.azimuth v) := by
  rw [azimuth_def, Orientation.areaForm_eq_norm_mul_norm_mul_sin_oangle]

/-- Rescaling a vector by a positive factor does not change its azimuth. -/
@[simp]
lemma azimuth_smul_of_pos (F : AzimuthalFrame) {c : ℝ} (hc : 0 < c) (v : E²) :
    F.azimuth (c • v) = F.azimuth v := by
  rw [azimuth_def, Orientation.oangle_smul_right_of_pos _ _ _ hc, azimuth_def]

/-- Negating a nonzero vector shifts its azimuth by `π`, in a frame with a nonzero reference
direction. -/
lemma azimuth_neg {F : AzimuthalFrame} (hF : F.leptonDir ≠ 0) {v : E²} (hv : v ≠ 0) :
    F.azimuth (-v) = F.azimuth v + (Real.pi : Real.Angle) := by
  rw [azimuth_def, Orientation.oangle_neg_right _ hF hv, azimuth_def]

/-! ### Reversing the orientation -/

/-- The frame with the same reference direction and the opposite orientation. -/
def negOrientation (F : AzimuthalFrame) : AzimuthalFrame where
  leptonDir := F.leptonDir
  orientation := -F.orientation

@[simp]
lemma leptonDir_negOrientation (F : AzimuthalFrame) :
    F.negOrientation.leptonDir = F.leptonDir := (rfl)

@[simp]
lemma orientation_negOrientation (F : AzimuthalFrame) :
    F.negOrientation.orientation = -F.orientation := (rfl)

@[simp]
lemma negOrientation_negOrientation (F : AzimuthalFrame) :
    F.negOrientation.negOrientation = F := by
  ext1
  · simp
  · exact neg_neg F.orientation

/-- Reversing the orientation negates every azimuth. -/
@[simp]
lemma azimuth_negOrientation (F : AzimuthalFrame) (v : E²) :
    F.negOrientation.azimuth v = -F.azimuth v := by
  rw [azimuth_def, azimuth_def, orientation_negOrientation, leptonDir_negOrientation,
    Orientation.oangle_neg_orientation_eq_neg]

/-- Under the opposite orientation every sine modulation `sin(m φ_h + n φ_S)` changes sign. -/
lemma sin_zsmul_azimuth_add_zsmul_azimuth_negOrientation (F : AzimuthalFrame) (m n : ℤ)
    (Ph S : E²) :
    Real.Angle.sin (m • F.negOrientation.azimuth Ph + n • F.negOrientation.azimuth S) =
      -Real.Angle.sin (m • F.azimuth Ph + n • F.azimuth S) := by
  rw [azimuth_negOrientation, azimuth_negOrientation, smul_neg, smul_neg, ← neg_add,
    Real.Angle.sin_neg]

/-- Under the opposite orientation every cosine modulation `cos(m φ_h + n φ_S)` is unchanged. -/
lemma cos_zsmul_azimuth_add_zsmul_azimuth_negOrientation (F : AzimuthalFrame) (m n : ℤ)
    (Ph S : E²) :
    Real.Angle.cos (m • F.negOrientation.azimuth Ph + n • F.negOrientation.azimuth S) =
      Real.Angle.cos (m • F.azimuth Ph + n • F.azimuth S) := by
  rw [azimuth_negOrientation, azimuth_negOrientation, smul_neg, smul_neg, ← neg_add,
    Real.Angle.cos_neg]

/-- A single modulation in the two orientations: cosine amplitude `A` and sine amplitude `B` of
the harmonic `m φ_h + n φ_S` become, in the azimuths of the oppositely oriented frame, the cosine
amplitude `A` and the sine amplitude `-B`. -/
lemma mul_cos_add_mul_sin_negOrientation (F : AzimuthalFrame) (m n : ℤ) (A B : ℝ) (Ph S : E²) :
    A * Real.Angle.cos (m • F.azimuth Ph + n • F.azimuth S) +
        B * Real.Angle.sin (m • F.azimuth Ph + n • F.azimuth S) =
      A * Real.Angle.cos (m • F.negOrientation.azimuth Ph + n • F.negOrientation.azimuth S) +
        -B * Real.Angle.sin (m • F.negOrientation.azimuth Ph + n • F.negOrientation.azimuth S) := by
  rw [cos_zsmul_azimuth_add_zsmul_azimuth_negOrientation,
    sin_zsmul_azimuth_add_zsmul_azimuth_negOrientation, neg_mul_neg]

/-- The structure functions in the two orientations. A finite sum of modulations with cosine
amplitudes `A i` and sine amplitudes `B i` of the harmonics `m i φ_h + n i φ_S` is, written in the
azimuths of the oppositely oriented frame, the sum with the same cosine amplitudes and the sine
amplitudes `-B i`. -/
theorem sum_cos_add_sin_negOrientation (F : AzimuthalFrame) {ι : Type*} (s : Finset ι)
    (m n : ι → ℤ) (A B : ι → ℝ) (Ph S : E²) :
    ∑ i ∈ s, (A i * Real.Angle.cos (m i • F.azimuth Ph + n i • F.azimuth S) +
        B i * Real.Angle.sin (m i • F.azimuth Ph + n i • F.azimuth S)) =
      ∑ i ∈ s, (A i * Real.Angle.cos
          (m i • F.negOrientation.azimuth Ph + n i • F.negOrientation.azimuth S) +
        -B i * Real.Angle.sin
          (m i • F.negOrientation.azimuth Ph + n i • F.negOrientation.azimuth S)) :=
  Finset.sum_congr rfl fun i _ => F.mul_cos_add_mul_sin_negOrientation (m i) (n i) (A i) (B i) Ph S

/-! ### The Trento convention -/

/-- The orientation of the Trento convention for a photon momentum `q` along the `z`-axis:
azimuths increase counterclockwise about the photon three-momentum. This is the standard
orientation of the transverse plane when the photon moves along `+z`, and the opposite one
otherwise. -/
def trentoOrientation (q : Lorentz.Vector 3) : Orientation ℝ E² (Fin 2) :=
  if 0 < q (Sum.inr 2) then EuclideanSpace.orientation (Fin 2)
  else -EuclideanSpace.orientation (Fin 2)

lemma trentoOrientation_of_inr_two_pos {q : Lorentz.Vector 3} (hq : 0 < q (Sum.inr 2)) :
    trentoOrientation q = EuclideanSpace.orientation (Fin 2) := by
  rw [trentoOrientation, ite_eq_left hq]

lemma trentoOrientation_of_inr_two_nonpos {q : Lorentz.Vector 3} (hq : q (Sum.inr 2) ≤ 0) :
    trentoOrientation q = -EuclideanSpace.orientation (Fin 2) := by
  rw [trentoOrientation, ite_eq_right hq.not_gt]

/-- Two photon momenta pointing the same way along the `z`-axis have the same Trento
orientation. -/
lemma trentoOrientation_congr {q q' : Lorentz.Vector 3}
    (h : 0 < q (Sum.inr 2) ↔ 0 < q' (Sum.inr 2)) : trentoOrientation q = trentoOrientation q' := by
  rcases le_or_gt (q (Sum.inr 2)) 0 with hle | hpos
  · rw [trentoOrientation_of_inr_two_nonpos hle,
      trentoOrientation_of_inr_two_nonpos (not_lt.1 (mt h.2 hle.not_gt))]
  · rw [trentoOrientation_of_inr_two_pos hpos, trentoOrientation_of_inr_two_pos (h.1 hpos)]

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
lemma azimuth_trento_self_eq_zero (l q : Lorentz.Vector 3) :
    (trento l q).azimuth (transversePart l) = 0 := by
  rw [← leptonDir_trento l q, azimuth_leptonDir]

/-- In a frame where the photon has no transverse part, the scattered lepton `l' = l - q` defines
the same Trento frame as the incoming one: both span the lepton plane with the photon axis. -/
lemma trento_sub_photon (l : Lorentz.Vector 3) {q : Lorentz.Vector 3}
    (hq : transversePart q = 0) : trento (l - q) q = trento l q := by
  ext1 <;> simp [hq]

/-- The cosine of an azimuth measured from the transverse part of a lepton momentum `l`, such as
a Trento azimuth (`leptonDir_trento`): `|l_T| |p_T| cos φ = l_T · p_T`. It does not depend on the
orientation of the frame. -/
theorem norm_mul_norm_mul_cos_azimuth_of_leptonDir_eq {F : AzimuthalFrame} {l : Lorentz.Vector 3}
    (hF : F.leptonDir = transversePart l) (p : Lorentz.Vector 3) :
    ‖transversePart l‖ * ‖transversePart p‖ * Real.Angle.cos (F.azimuth (transversePart p)) =
      l (Sum.inr 0) * p (Sum.inr 0) + l (Sum.inr 1) * p (Sum.inr 1) := by
  rw [← hF, ← inner_eq_norm_mul_norm_mul_cos_azimuth, hF]
  simp only [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, conj_trivial,
    Lorentz.Vector.transversePart_apply_zero, Lorentz.Vector.transversePart_apply_one]
  ring

/-- The sine of a Trento azimuth, for a photon momentum `q` along the `z`-axis:
`|q| |l_T| |p_T| sin φ = (q × l) · p` for the spatial parts, whose right-hand side is
`q³ (l¹ p² - l² p¹)` when `q = q³ e_z`. -/
theorem abs_inr_two_mul_norm_mul_norm_mul_sin_azimuth_trento (l q p : Lorentz.Vector 3) :
    |q (Sum.inr 2)| * (‖transversePart l‖ * ‖transversePart p‖ *
        Real.Angle.sin ((trento l q).azimuth (transversePart p))) =
      q (Sum.inr 2) * (l (Sum.inr 0) * p (Sum.inr 1) - l (Sum.inr 1) * p (Sum.inr 0)) := by
  rw [← leptonDir_trento l q, ← areaForm_eq_norm_mul_norm_mul_sin_azimuth, leptonDir_trento,
    orientation_trento]
  rcases le_or_gt (q (Sum.inr 2)) 0 with hle | hpos
  · rw [trentoOrientation_of_inr_two_nonpos hle, Orientation.areaForm_neg_orientation,
      abs_of_nonpos hle]
    simp only [LinearMap.neg_apply, EuclideanSpace.areaForm_orientation_apply,
      Lorentz.Vector.transversePart_apply_zero, Lorentz.Vector.transversePart_apply_one]
    ring
  · rw [trentoOrientation_of_inr_two_pos hpos, abs_of_pos hpos]
    simp only [EuclideanSpace.areaForm_orientation_apply,
      Lorentz.Vector.transversePart_apply_zero, Lorentz.Vector.transversePart_apply_one]

/-! ### Invariance under boosts along the photon direction -/

/-- A boost along the photon direction maps the Trento frame of `(l, q)` to the Trento frame of
the boosted momenta, for a photon momentum `q` whose longitudinal part is spacelike,
`q⁺ q⁻ < 0`. A spacelike `q` along the `z`-axis is of this kind
(`Lorentz.Vector.minkowskiProduct_self_eq_lightFront`). -/
theorem trento_boost_two (l : Lorentz.Vector 3) {q : Lorentz.Vector 3}
    (hq : Lorentz.Vector.plusComponent q * Lorentz.Vector.minusComponent q < 0) (β : ℝ)
    (hβ : |β| < 1) :
    trento (boost (2 : Fin 3) β hβ • l) (boost (2 : Fin 3) β hβ • q) = trento l q := by
  ext1
  · simp
  · exact trentoOrientation_congr (Lorentz.Vector.boost_two_inr_two_pos_iff hq β hβ)

/-- The azimuths `φ_h` and `φ_S` are invariant under boosts along the photon direction: boosting
the lepton, the photon and the four-vector `p` together leaves the Trento azimuth of `p`
unchanged, for a photon momentum `q` whose longitudinal part is spacelike, `q⁺ q⁻ < 0`. -/
theorem azimuth_trento_boost_two (l : Lorentz.Vector 3) {q : Lorentz.Vector 3}
    (hq : Lorentz.Vector.plusComponent q * Lorentz.Vector.minusComponent q < 0) (β : ℝ)
    (hβ : |β| < 1) (p : Lorentz.Vector 3) :
    (trento (boost (2 : Fin 3) β hβ • l) (boost (2 : Fin 3) β hβ • q)).azimuth
        (transversePart (boost (2 : Fin 3) β hβ • p)) =
      (trento l q).azimuth (transversePart p) := by
  rw [trento_boost_two l hq, Lorentz.Vector.transversePart_boost_two]

end AzimuthalFrame

end EpsilonEridani.QFT.Scattering.DIS.SIDIS
