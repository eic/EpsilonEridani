/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.QFT.Scattering.DIS.Kinematics.Basic

/-!
# Reference frames: energy, spatial part and opening angle

Jet distances, hemisphere assignments and event shapes are not Lorentz invariant: each is defined
relative to a frame, and the frame is always an explicit argument. Over the abstract momentum space
`V` with bilinear form `g : Bilin V` used by `DisKinematics`, a frame is a vector `n` with
`0 < g n n` (timelike in the signature `(+,-,-,-)`), and

* the **energy** of `p` is `E(p) = g p n / √(g n n)`, a linear functional;
* the **spatial part** of `p` is `p_s = p - (g p n / g n n) • n`, the projection
  `Bilin.projOrthogonal g n` along `ℝ ∙ n` onto the `g`-orthogonal complement of `n`;
* the **spatial norm** of `p` is `|p_s| = √(-g p_s p_s)`, and the **cosine of the opening angle** of
  `a` and `b` is `cos θ_ab = -g a_s b_s / (|a_s| |b_s|)`.

For a symmetric `g` the spatial parts satisfy `g a_s b_s = g a b - E(a) E(b)`, which is the
mass-shell relation `E² = m² + |p_s|²` when `a = b`. Consequently a massless momentum (`g p p = 0`)
has `|p_s| = |E(p)|`, and for two massless momenta of positive energy

  `1 - cos θ_ab = g a b / (E(a) E(b))`,

the relation `2 a·b = 2 E_a E_b (1 - cos θ_ab)` on which the Durham and generalised-`k_T` distance
measures rest. A massive pseudojet, such as the `E`-scheme sum of two massless momenta, does not
satisfy it, which is why the massless hypotheses are stated.

No signature hypothesis on `g` is imposed. The names "magnitude" and "opening angle" are justified
when `g` is negative definite on the `g`-orthogonal complement of `n`, as for a Minkowski form;
without that hypothesis `spatialNorm` and `cosAngle` are just the stated formulas.

## Main definitions

* `EpsilonEridani.QFT.Jets.Frame g`: a reference vector `n` with `0 < g n n` (timelike in the
  signature `(+,-,-,-)`) for the bilinear form `g`.
* `Frame.energy`, `Frame.spatial`: the energy functional and the spatial projection of a frame.
* `Frame.spatialNorm`, `Frame.cosAngle`: the magnitude of the spatial part and the cosine of the
  opening angle between two momenta.

## Main statements

* `Frame.spatial_orthogonal_n`, `Frame.energy_spatial`: the spatial part is orthogonal to the frame
  vector and carries no energy.
* `Frame.ker_spatial`, `Frame.range_spatial`: the spatial projection has kernel `ℝ ∙ n` and range
  the momenta `p` with `g p n = 0`.
* `Frame.spatial_pairing_spatial`: `g a_s b_s = g a b - E(a) E(b)`.
* `Frame.spatialNorm_eq_sqrt_energy_sq_sub`: `|p_s| = √(E(p)² - g p p)`, and
  `Frame.spatialNorm_eq_abs_energy_of_massless`: a massless momentum has `|p_s| = |E(p)|`.
* `Frame.one_sub_cosAngle_of_massless`: `1 - cos θ_ab = g a b / (E(a) E(b))` for massless `a`, `b`
  of positive energy.

A concrete frame, the rest frame of the `+--` Minkowski form, is in
`EpsilonEridani.QFT.Jets.Frame.Witness`.

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

/-- A frame for the bilinear form `g`: a reference vector `n` that is timelike, `0 < g n n`, in the
signature `(+,-,-,-)`. Energies, spatial parts and angles are taken relative to it. -/
@[ext]
structure Frame (g : Bilin V) where
  /-- The timelike reference vector (the four-velocity of the observer, up to normalisation). -/
  n : V
  /-- The reference vector is timelike. -/
  timelike : 0 < g n n

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
  rw [energy_n]
  exact Real.sqrt_pos.mpr F.timelike

/-- The frame vector is nonzero. -/
theorem n_ne_zero : F.n ≠ 0 :=
  LinearMap.BilinForm.ne_zero_of_not_isOrtho_self F.n F.timelike.ne'

/-! ### The spatial part -/

/-- The spatial part of a momentum relative to the frame, `p - (g p n / g n n) • n`: the projection
`Bilin.projOrthogonal g n` along `ℝ ∙ n` onto the `g`-orthogonal complement of `n`. -/
def spatial : V →ₗ[ℝ] V :=
  g.projOrthogonal F.n

theorem spatial_def : F.spatial = g.projOrthogonal F.n :=
  (rfl)

theorem spatial_apply (p : V) : F.spatial p = p - (g p F.n / g F.n F.n) • F.n :=
  g.projOrthogonal_apply F.n p

/-- A momentum is the sum of its time part, along the frame vector, and its spatial part. -/
theorem energy_div_smul_add_spatial (p : V) :
    (F.energy p / Real.sqrt (g F.n F.n)) • F.n + F.spatial p = p := by
  simp [energy_apply, spatial_apply, div_div, Real.mul_self_sqrt F.timelike.le]

/-- The spatial part is `g`-orthogonal to the frame vector. -/
@[simp]
theorem spatial_orthogonal_n (p : V) : g (F.spatial p) F.n = 0 :=
  g.projOrthogonal_orthogonal F.timelike.ne' p

/-- The spatial part carries no energy. -/
@[simp]
theorem energy_spatial (p : V) : F.energy (F.spatial p) = 0 := by
  rw [energy_apply, spatial_orthogonal_n, zero_div]

@[simp]
theorem spatial_n : F.spatial F.n = 0 :=
  g.projOrthogonal_apply_self F.timelike.ne'

theorem spatial_eq_self_iff {p : V} : F.spatial p = p ↔ g p F.n = 0 :=
  g.projOrthogonal_eq_self_iff F.timelike.ne'

/-- The spatial projection is idempotent. -/
@[simp]
theorem spatial_spatial (p : V) : F.spatial (F.spatial p) = F.spatial p :=
  g.projOrthogonal_projOrthogonal F.timelike.ne' p

/-- The momenta with vanishing spatial part are the multiples of the frame vector. -/
theorem ker_spatial : LinearMap.ker F.spatial = ℝ ∙ F.n :=
  g.ker_projOrthogonal F.timelike.ne'

/-- The spatial parts are exactly the momenta `p` with `g p n = 0`, that is, the orthogonal
complement of `ℝ ∙ n` for `g.flip` in the sense of `LinearMap.BilinForm.orthogonal`. For a
symmetric form this is `g.orthogonal (ℝ ∙ n)`. -/
theorem range_spatial : LinearMap.range F.spatial = g.flip.orthogonal (ℝ ∙ F.n) :=
  g.range_projOrthogonal F.timelike.ne'

/-- The `g`-product of two spatial parts, `g a_s b_s = g a b - E(a) E(b)`. For `a = b` this is the
mass-shell relation `g p_s p_s = m² - E(p)²`. -/
theorem spatial_pairing_spatial (hg : g.IsSymm) (a b : V) :
    g (F.spatial a) (F.spatial b) = g a b - F.energy a * F.energy b := by
  have hN : g F.n F.n ≠ 0 := F.timelike.ne'
  rw [spatial_apply, spatial_apply, Bilin.apply_sub_smul_pair, hg.eq F.n b, energy_apply,
    energy_apply, div_mul_div_comm _ (Real.sqrt _), Real.mul_self_sqrt F.timelike.le]
  field_simp
  ring

/-! ### The spatial norm and the opening angle -/

/-- The magnitude `|p_s| = √(-g p_s p_s)` of the spatial part of a momentum. -/
def spatialNorm (p : V) : ℝ :=
  Real.sqrt (-g (F.spatial p) (F.spatial p))

theorem spatialNorm_def (p : V) : F.spatialNorm p = Real.sqrt (-g (F.spatial p) (F.spatial p)) :=
  (rfl)

theorem spatialNorm_nonneg (p : V) : 0 ≤ F.spatialNorm p := by
  rw [spatialNorm_def]
  exact Real.sqrt_nonneg _

theorem spatialNorm_pos_iff (p : V) :
    0 < F.spatialNorm p ↔ 0 < -g (F.spatial p) (F.spatial p) := by
  rw [spatialNorm_def, Real.sqrt_pos]

@[simp]
theorem spatialNorm_smul (c : ℝ) (p : V) : F.spatialNorm (c • p) = |c| * F.spatialNorm p := by
  simp only [spatialNorm_def, map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [← mul_assoc, ← mul_neg, Real.sqrt_mul (mul_self_nonneg c), Real.sqrt_mul_self_eq_abs]

/-- The spatial norm in terms of the energy and the invariant mass, `|p_s| = √(E(p)² - g p p)`. -/
theorem spatialNorm_eq_sqrt_energy_sq_sub (hg : g.IsSymm) (p : V) :
    F.spatialNorm p = Real.sqrt (F.energy p ^ 2 - g p p) := by
  rw [spatialNorm_def, F.spatial_pairing_spatial hg]
  congr 1
  ring

/-- A massless momentum has spatial norm equal to the absolute value of its energy. -/
theorem spatialNorm_eq_abs_energy_of_massless (hg : g.IsSymm) {p : V} (hp : g p p = 0) :
    F.spatialNorm p = |F.energy p| := by
  rw [F.spatialNorm_eq_sqrt_energy_sq_sub hg, hp, sub_zero, Real.sqrt_sq_eq_abs]

/-- The cosine of the opening angle between two momenta in the frame,
`cos θ_ab = -g a_s b_s / (|a_s| |b_s|)`. -/
def cosAngle (a b : V) : ℝ :=
  -g (F.spatial a) (F.spatial b) / (F.spatialNorm a * F.spatialNorm b)

theorem cosAngle_def (a b : V) :
    F.cosAngle a b = -g (F.spatial a) (F.spatial b) / (F.spatialNorm a * F.spatialNorm b) :=
  (rfl)

theorem cosAngle_comm (hg : g.IsSymm) (a b : V) : F.cosAngle a b = F.cosAngle b a := by
  rw [cosAngle_def, cosAngle_def, hg.eq, mul_comm]

/-- A momentum of nonzero spatial norm makes angle zero with itself. -/
theorem cosAngle_self {p : V} (hp : F.spatialNorm p ≠ 0) : F.cosAngle p p = 1 := by
  have hpos : 0 < -g (F.spatial p) (F.spatial p) :=
    (F.spatialNorm_pos_iff p).mp ((F.spatialNorm_nonneg p).lt_of_ne' hp)
  rw [cosAngle_def, spatialNorm_def, Real.mul_self_sqrt hpos.le, div_self hpos.ne']

/-- Rescaling a momentum by a positive factor does not change its direction. -/
theorem cosAngle_smul_left_of_pos {c : ℝ} (hc : 0 < c) (a b : V) :
    F.cosAngle (c • a) b = F.cosAngle a b := by
  simp only [cosAngle_def, spatialNorm_smul, abs_of_pos hc, map_smul, LinearMap.smul_apply,
    smul_eq_mul, mul_assoc, ← mul_neg, mul_div_mul_left _ _ hc.ne']

/-- Rescaling a momentum by a positive factor does not change its direction. -/
theorem cosAngle_smul_right_of_pos {c : ℝ} (hc : 0 < c) (a b : V) :
    F.cosAngle a (c • b) = F.cosAngle a b := by
  simp only [cosAngle_def, spatialNorm_smul, abs_of_pos hc, map_smul, smul_eq_mul]
  rw [mul_left_comm, ← mul_neg, mul_div_mul_left _ _ hc.ne']

/-- For two massless momenta of positive energy, `1 - cos θ_ab = g a b / (E(a) E(b))`; that is,
`2 a·b = 2 E_a E_b (1 - cos θ_ab)`. -/
theorem one_sub_cosAngle_of_massless (hg : g.IsSymm) {a b : V} (ha : g a a = 0)
    (hb : g b b = 0) (hEa : 0 < F.energy a) (hEb : 0 < F.energy b) :
    1 - F.cosAngle a b = g a b / (F.energy a * F.energy b) := by
  simp only [cosAngle_def, F.spatialNorm_eq_abs_energy_of_massless hg ha,
    F.spatialNorm_eq_abs_energy_of_massless hg hb, abs_of_pos hEa, abs_of_pos hEb,
    F.spatial_pairing_spatial hg]
  field_simp
  ring

end Frame

end Jets
end QFT
end EpsilonEridani
