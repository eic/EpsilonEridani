/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.QFT.Scattering.DIS.Tensors.Basic

/-!
# Reference frames: energy, spatial part and opening angle

Jet distances, hemisphere assignments and event shapes are not Lorentz invariant: each is defined
relative to a frame, and the frame is always an explicit argument. Over the abstract momentum space
`V` with bilinear form `g : Bilin V` used by `DisKinematics`, a frame is a vector `n` with
`g n n = 1` (unit-normalised timelike in the signature `(+,-,-,-)`), and

* the **energy** of `p` is `E(p) = g p n / √(g n n)`, a linear functional;
* the **spatial part** of `p` is `p_s = p - (g p n / g n n) • n`, the projection along `ℝ ∙ n` onto
  the `g`-orthogonal complement of `n`;
* the **spatial norm** of `p` is `|p_s| = √(-g p_s p_s)`, and the **cosine of the opening angle** of
  `a` and `b` is `cos θ_ab = -g a_s b_s / (|a_s| |b_s|)`.

For a symmetric `g` the spatial parts satisfy `g a_s b_s = g a b - E(a) E(b)`, which is the
mass-shell relation `E² = m² + |p_s|²` when `a = b`. Consequently a massless momentum (`g p p = 0`)
has `|p_s| = |E(p)|`, and for two massless momenta of positive energy

  `1 - cos θ_ab = g a b / (E(a) E(b))`,

the relation `2 a·b = 2 E_a E_b (1 - cos θ_ab)` on which the Durham and generalised-`k_T` distance
measures rest. A massive pseudojet, such as the `E`-scheme sum of two massless momenta, does not
satisfy it, which is why the massless hypotheses are stated.

## Main definitions

* `EpsilonEridani.QFT.Jets.Frame g`: a timelike reference vector for the bilinear form `g`.
* `Frame.energy`, `Frame.spatial`: the energy functional and the spatial projection of a frame.
* `Frame.spatialNorm`, `Frame.cosAngle`: the magnitude of the spatial part and the cosine of the
  opening angle between two momenta.

## Main statements

* `Frame.bilin_spatial_n`, `Frame.energy_spatial`: the spatial part is orthogonal to the frame
  vector and carries no energy.
* `Frame.ker_spatial`, `Frame.range_spatial`: the spatial projection has kernel `ℝ ∙ n` and range
  the momenta `p` with `g p n = 0`.
* `Frame.bilin_spatial_spatial`: `g a_s b_s = g a b - E(a) E(b)`.
* `Frame.spatialNorm_of_massless`: a massless momentum has `|p_s| = |E(p)|`.
* `Frame.one_sub_cosAngle_of_massless`: `1 - cos θ_ab = g a b / (E(a) E(b))` for massless `a`, `b`
  of positive energy.
* `Frame.Witness.cosAngle_restFrameWit`: in the rest frame of the `+--` Minkowski form, two
  back-to-back photons have `cos θ = -1`.

## References

* S. Catani, Yu. L. Dokshitzer, M. Olsson, G. Turnock and B. R. Webber, *New clustering algorithm
  for multijet cross sections in e⁺e⁻ annihilation*, Phys. Lett. B 269 (1991) 432.
-/

public section

noncomputable section

namespace EpsilonEridani
namespace QFT
namespace Jets

open EpsilonEridani.QFT.Scattering.DIS.Kinematics (Bilin)

variable {V : Type} [AddCommGroup V] [Module ℝ V]

/-- A frame for the bilinear form `g`: a reference vector `n` with `g n n = 1`
(unit-normalised timelike in the signature `(+,-,-,-)`). Energies, spatial
parts and angles are taken relative to it. -/
@[ext]
structure Frame (g : Bilin V) where
  /-- The unit-normalised timelike reference vector (the four-velocity of the observer). -/
  n : V
  /-- The reference vector is unit-normalised. -/
  norm : g n n = 1

namespace Frame

variable {g : Bilin V} (F : Frame g)

/-! ### The energy -/

/-- The energy of a momentum relative to the frame, `E(p) = g p n / √(g n n)`, as a linear
functional. -/
def energy : V →ₗ[ℝ] ℝ :=
  (Real.sqrt (g F.n F.n))⁻¹ • g.flip F.n

theorem energy_apply (p : V) : F.energy p = g p F.n / Real.sqrt (g F.n F.n) := by
  simp [energy, div_eq_inv_mul]

/-- The frame vector has energy `√(g n n)`; for a unit-normalised frame vector this is `1`. -/
@[simp]
theorem energy_n : F.energy F.n = Real.sqrt (g F.n F.n) := by
  rw [energy_apply, Real.div_sqrt]

theorem energy_n_pos : 0 < F.energy F.n := by
  rw [energy_n, F.norm]
  exact Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 1)

/-! ### The spatial part -/

/-- The spatial part of a momentum relative to the frame, `p - (g p n / g n n) • n`: the projection
along `ℝ ∙ n` onto the `g`-orthogonal complement of `n`. It is the endomorphism
`Module.preReflection n f` for the functional `f = g · n / g n n`, which satisfies `f n = 1`
(rather than the `f n = 2` of a reflection). -/
def spatial : V →ₗ[ℝ] V :=
  Module.preReflection F.n ((g F.n F.n)⁻¹ • g.flip F.n)

theorem spatial_apply (p : V) : F.spatial p = p - (g p F.n / g F.n F.n) • F.n := by
  simp [spatial, Module.preReflection_apply, div_eq_inv_mul]

/-- A momentum is the sum of its time part, along the frame vector, and its spatial part. -/
theorem energy_div_smul_add_spatial (p : V) :
    (F.energy p / Real.sqrt (g F.n F.n)) • F.n + F.spatial p = p := by
  have hnE : g F.n F.n = 1 := F.norm
  have hsqrt : Real.sqrt (g F.n F.n) = 1 := by rw [hnE]; exact Real.sqrt_one
  simp only [energy_apply, spatial_apply, hsqrt, hnE]
  field_simp
  ring

/-- The spatial part is `g`-orthogonal to the frame vector. -/
@[simp]
theorem bilin_spatial_n (p : V) : g (F.spatial p) F.n = 0 := by
  have hn : g F.n F.n = 1 := F.norm
  have hn0 : g F.n F.n ≠ 0 := by rw [hn]; norm_num
  simp [spatial_apply, hn0]

/-- The spatial part carries no energy. -/
@[simp]
theorem energy_spatial (p : V) : F.energy (F.spatial p) = 0 := by
  rw [energy_apply, bilin_spatial_n, zero_div]

@[simp]
theorem spatial_n : F.spatial F.n = 0 := by
  have hn : g F.n F.n = 1 := F.norm
  have h1 : g F.n F.n ≠ 0 := by rw [hn]; norm_num
  rw [spatial_apply, div_self h1, one_smul, sub_self]

theorem spatial_eq_self_iff {p : V} : F.spatial p = p ↔ g p F.n = 0 := by
  rw [spatial_apply, sub_eq_self, smul_eq_zero, div_eq_zero_iff]
  have hn : F.n ≠ 0 := by
    intro h
    have hn' : g F.n F.n = 1 := F.norm
    rw [h] at hn'
    simp at hn'
  have hN : g F.n F.n ≠ 0 := by
    have hn' : g F.n F.n = 1 := F.norm
    rw [hn']; norm_num
  simp [hN, hn]

/-- The spatial projection is idempotent. -/
@[simp]
theorem spatial_spatial (p : V) : F.spatial (F.spatial p) = F.spatial p :=
  F.spatial_eq_self_iff.mpr (F.bilin_spatial_n p)

/-- The momenta with vanishing spatial part are the multiples of the frame vector. -/
theorem ker_spatial : LinearMap.ker F.spatial = ℝ ∙ F.n := by
  ext p
  rw [LinearMap.mem_ker, Submodule.mem_span_singleton]
  constructor
  · intro hp
    refine ⟨F.energy p / Real.sqrt (g F.n F.n), ?_⟩
    simpa [hp] using F.energy_div_smul_add_spatial p
  · rintro ⟨c, rfl⟩
    rw [map_smul, spatial_n, smul_zero]

/-- The spatial parts are exactly the momenta `p` with `g p n = 0`, that is, the orthogonal
complement of `ℝ ∙ n` for `g.flip` in the sense of `LinearMap.BilinForm.orthogonal`. For a
symmetric form this is `g.orthogonal (ℝ ∙ n)`. -/
theorem range_spatial : LinearMap.range F.spatial = g.flip.orthogonal (ℝ ∙ F.n) := by
  ext p
  simp only [LinearMap.mem_range, LinearMap.BilinForm.mem_orthogonal_iff,
    Submodule.mem_span_singleton, forall_exists_index, forall_apply_eq_imp_iff,
    LinearMap.BilinForm.flip_apply, map_smul, smul_eq_mul, mul_eq_zero]
  constructor
  · rintro ⟨q, rfl⟩ c
    exact Or.inr (F.bilin_spatial_n q)
  · intro hp
    have hn : g F.n F.n = 1 := F.norm
    have hp' : g p F.n = 0 := by
      simpa [F.norm] using hp 1
    exact ⟨p, F.spatial_eq_self_iff.mpr hp'⟩

/-- The `g`-product of two spatial parts, `g a_s b_s = g a b - E(a) E(b)`. For `a = b` this is the
mass-shell relation `g p_s p_s = m² - E(p)²`. -/
theorem bilin_spatial_spatial (hg : g.IsSymm) (a b : V) :
    g (F.spatial a) (F.spatial b) = g a b - F.energy a * F.energy b := by
  have hone : g F.n F.n = 1 := F.norm
  simp only [spatial_apply, energy_apply, div_mul_div_comm, hone,
    map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hg.eq F.n b]
  field_simp
  ring

/-! ### The spatial norm and the opening angle -/

/-- The magnitude `|p_s| = √(-g p_s p_s)` of the spatial part of a momentum. -/
def spatialNorm (p : V) : ℝ :=
  Real.sqrt (-g (F.spatial p) (F.spatial p))

theorem spatialNorm_def (p : V) : F.spatialNorm p = Real.sqrt (-g (F.spatial p) (F.spatial p)) := by
  simp [spatialNorm]

theorem spatialNorm_nonneg (p : V) : 0 ≤ F.spatialNorm p :=
  Real.sqrt_nonneg _

@[simp]
theorem spatialNorm_smul (c : ℝ) (p : V) : F.spatialNorm (c • p) = |c| * F.spatialNorm p := by
  simp only [spatialNorm, map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [← mul_assoc, ← mul_neg, Real.sqrt_mul (mul_self_nonneg c), Real.sqrt_mul_self_eq_abs]

/-- A massless momentum has spatial norm equal to the absolute value of its energy. -/
theorem spatialNorm_of_massless (hg : g.IsSymm) {p : V} (hp : g p p = 0) :
    F.spatialNorm p = |F.energy p| := by
  simp [spatialNorm, F.bilin_spatial_spatial hg, hp, Real.sqrt_mul_self_eq_abs]

/-- The cosine of the opening angle between two momenta in the frame,
`cos θ_ab = -g a_s b_s / (|a_s| |b_s|)`. -/
def cosAngle (a b : V) : ℝ :=
  -g (F.spatial a) (F.spatial b) / (F.spatialNorm a * F.spatialNorm b)

theorem cosAngle_def (a b : V) :
    F.cosAngle a b = -g (F.spatial a) (F.spatial b) / (F.spatialNorm a * F.spatialNorm b) := by
  simp [cosAngle]

theorem cosAngle_comm (hg : g.IsSymm) (a b : V) : F.cosAngle a b = F.cosAngle b a := by
  rw [cosAngle, cosAngle, hg.eq, mul_comm]

/-- A momentum with nonvanishing spatial part makes angle zero with itself. -/
theorem cosAngle_self {p : V} (hp : F.spatialNorm p ≠ 0) : F.cosAngle p p = 1 := by
  have hpos : 0 < -g (F.spatial p) (F.spatial p) :=
    Real.sqrt_pos.mp ((F.spatialNorm_nonneg p).lt_of_ne' hp)
  rw [cosAngle, spatialNorm, Real.mul_self_sqrt hpos.le, div_self hpos.ne']

/-- Rescaling a momentum by a positive factor does not change its direction. -/
theorem cosAngle_smul_left {c : ℝ} (hc : 0 < c) (a b : V) :
    F.cosAngle (c • a) b = F.cosAngle a b := by
  simp only [cosAngle, spatialNorm_smul, abs_of_pos hc, map_smul, LinearMap.smul_apply,
    smul_eq_mul, mul_assoc, ← mul_neg, mul_div_mul_left _ _ hc.ne']

/-- Rescaling a momentum by a positive factor does not change its direction. -/
theorem cosAngle_smul_right {c : ℝ} (hc : 0 < c) (a b : V) :
    F.cosAngle a (c • b) = F.cosAngle a b := by
  simp only [cosAngle, spatialNorm_smul, abs_of_pos hc, map_smul, smul_eq_mul]
  rw [mul_left_comm, ← mul_neg, mul_div_mul_left _ _ hc.ne']

/-- For two massless momenta of positive energy, `1 - cos θ_ab = g a b / (E(a) E(b))`; that is,
`2 a·b = 2 E_a E_b (1 - cos θ_ab)`. -/
theorem one_sub_cosAngle_of_massless (hg : g.IsSymm) {a b : V} (ha : g a a = 0)
    (hb : g b b = 0) (hEa : 0 < F.energy a) (hEb : 0 < F.energy b) :
    1 - F.cosAngle a b = g a b / (F.energy a * F.energy b) := by
  simp only [cosAngle, F.spatialNorm_of_massless hg ha, F.spatialNorm_of_massless hg hb,
    abs_of_pos hEa, abs_of_pos hEb, F.bilin_spatial_spatial hg]
  field_simp
  ring

/-! ### A witness

The `+--` Minkowski form `gWit` on `ℝ × ℝ × ℝ`, already used as the DIS tensor witness, carries
the rest frame `n = (1, 0, 0)`. In it the energy of `p` is its time component, and two
back-to-back photons have opening angle `π`. -/

namespace Witness

open EpsilonEridani.QFT.Scattering.DIS.Tensors.Hadronic.Witness (gWit gWit_apply gWit_isSymm)

/-- The rest frame `n = (1, 0, 0)` of the Minkowski form `gWit`. -/
def restFrameWit : Frame gWit where
  n := (1, 0, 0)
  norm := by norm_num

/-- In the rest frame the energy of a momentum is its time component. -/
theorem energy_restFrameWit (p : ℝ × ℝ × ℝ) : restFrameWit.energy p = p.1 := by
  simp [energy_apply, restFrameWit]

/-- Two back-to-back photons, `(1, 1, 0)` and `(1, -1, 0)`, have `cos θ = -1` in the rest
frame. -/
theorem cosAngle_restFrameWit :
    restFrameWit.cosAngle ((1, 1, 0) : ℝ × ℝ × ℝ) (1, -1, 0) = -1 := by
  have h := restFrameWit.one_sub_cosAngle_of_massless gWit_isSymm
    (a := ((1, 1, 0) : ℝ × ℝ × ℝ)) (b := (1, -1, 0)) (by norm_num) (by norm_num)
    (by norm_num [energy_restFrameWit]) (by norm_num [energy_restFrameWit])
  rw [energy_restFrameWit, energy_restFrameWit] at h
  norm_num at h
  linarith

end Witness

end Frame

end Jets
end QFT
end EpsilonEridani
