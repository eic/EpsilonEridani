/-
Copyright (c) 2026 The EpsilonEridani contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The EpsilonEridani contributors
-/
module

public import EpsilonEridani.Relativity.Tensors.RealTensor.Vector.MinkowskiProductExtensions
public import EpsilonEridani.Mathematics.MeasureTheory.Measure.CharacteristicFunction.BasicExtensions
public import EpsilonEridani.Mathematics.Probability.Distributions.Gaussian.MultivariateExtensions

/-!
# The coherence condition for an extended source

A source of finite size emits an equivalent photon coherently, from its whole charge at once, only
if the photon does not resolve the charge distribution. Write the normalised charge distribution
of the source in its rest frame as a probability measure `μ` on space, with root-mean-square radius
`R`, `R² = ∫ ‖r‖² dμ`. A photon that leaves the source with four-momentum transfer `q` probes
`μ` through its form factor `F(q) = ∫ exp (i ⟪r, q.spatialPart⟫) dμ`, Mathlib's characteristic
function `MeasureTheory.charFun μ` evaluated at the spatial momentum `q.spatialPart` of the photon
in that frame. The coherent emission amplitude is that of a point charge times `F(q)`, so the
coherent rate carries `‖F(q)‖²`.

This file bounds the form factor above and below the scale `Q² ~ 1 / R²` of the virtuality
`Q² = -⟪q, q⟫ₘ`: below it the departure of the form factor from the point-charge value is
controlled by `Q² R²`, and beyond it the squared form factor of a Gaussian source decays.
The bounds below the scale hold only in the rest frame of the source: they take the hypotheses
`p.spatialPart = 0`, `p.timeComponent = m` and `⟪p', p'⟫ₘ = m ^ 2` of
`Lorentz.Vector.norm_spatialPart_sub_sq_of_spatialPart_eq_zero_of_massShell`, which put the source
at rest with mass `m` and its recoil on the same mass shell.

* Below the scale the source is not resolved, for any charge distribution of finite radius:
  in the source rest frame the spatial momentum transfer is fixed by the virtuality,
  `‖q.spatialPart‖² = Q² (1 + Q² / (4 m²))`
  (`Lorentz.Vector.norm_spatialPart_sub_sq_of_spatialPart_eq_zero_of_massShell`),
  and `1 - ‖F(q)‖ ≤ ‖q.spatialPart‖² R² / 2` (`MeasureTheory.one_sub_norm_charFun_le`). Together
  they give `1 - ‖F(q)‖ ≤ Q² (1 + Q² / (4 m²)) R² / 2` (`one_sub_norm_charFun_spatialPart_sub_le`).
  So `‖F‖` stays close to one, the value for a point charge, while `Q² R²` is small against one and
  the recoil factor `1 + Q² / (4 m²)` stays bounded; under `Q² R² ≲ 1` the latter holds for a
  source with `m R ≳ 1`. For the isotropic Gaussian charge distribution of width `σ` in `d`
  dimensions, the exact form factor `ProbabilityTheory.norm_charFun_map_smul_stdGaussian` gives
  the bound sharper by the factor `d`, `1 - ‖F(q)‖ ≤ ‖q.spatialPart‖² σ² / 2`
  (`ProbabilityTheory.one_sub_norm_charFun_map_smul_stdGaussian_le`), that is
  `1 - ‖F(q)‖ ≤ Q² (1 + Q² / (4 m²)) σ² / 2`
  (`one_sub_norm_charFun_map_smul_stdGaussian_spatialPart_sub_le`), or in its mean square radius
  `R² = d σ²`, `1 - ‖F(q)‖ ≤ Q² (1 + Q² / (4 m²)) R² / (2 d)`
  (`one_sub_norm_charFun_map_smul_stdGaussian_spatialPart_sub_le_of_integral_norm_sq_eq`).
* Beyond the scale the coherent rate is suppressed by the square of the form factor. For the
  isotropic Gaussian charge distribution of width `σ` in `d` dimensions,
  `‖F(q)‖² ≤ exp (-σ² Q²)` (`norm_sq_charFun_map_smul_stdGaussian_spatialPart_le`); in its mean
  square radius `R² = d σ²` this is `‖F(q)‖² ≤ exp (-Q² R² / d)`
  (`norm_sq_charFun_map_smul_stdGaussian_spatialPart_le_of_integral_norm_sq_eq`), which is
  `exp (-Q² R² / 3)` in three dimensions.
  It is composed from the general squared form factor
  `ProbabilityTheory.norm_sq_charFun_map_smul_stdGaussian` of the dilated Gaussian, whose second
  moment `ProbabilityTheory.integral_norm_sq_map_smul_stdGaussian` gives `R² = d σ²`, and from
  `Q² ≤ ‖q.spatialPart‖²` (`Lorentz.Vector.neg_minkowskiProduct_self_le_norm_spatialPart_sq`).
  The inequality itself is a frame-agnostic bound, holding for the spatial part of `q` in every
  frame; it reads as the suppression factor of the coherent rate only when `q.spatialPart` is the
  momentum transfer in the rest frame of the source, in which `μ` is its charge distribution. Some
  shape assumption is needed here: the form factor of two point charges a distance `2 R` apart is
  `cos ⟪r₀, q.spatialPart⟫` and does not decay at all.

Within the coherence condition `Q² R² ≤ 1`, taken as a hypothesis on the photon variables, the
photon energy in the collider frame is bounded by the Lorentz factor over the radius, `k R < γ`,
as the `Kinematics.PhotonKinematics` lemma
`abs_energy_mul_lt_gamma_of_mem_photonRegion_of_virtuality_mul_sq_le_one` states, `|k R| < γ`.
That kinematic consequence needs no form factor and lives with the photon kinematics; there `R`
is any real number, so it applies to the root-mean-square radius `R² = ∫ ‖r‖² dμ` of the charge
measure `μ` of the opening paragraph as well as to the radius `s.radius` of a `ChargedSource`.

## References

* J. D. Jackson, *Classical Electrodynamics*, 3rd ed., Wiley (1999), section 15.4,
  *Weizsäcker–Williams method of virtual quanta*.
* G. Baur, K. Hencken, D. Trautmann, S. Sadovsky and Y. Kharlov, *Coherent γγ and γA interactions
  in very peripheral collisions at relativistic ion colliders*, Phys. Rep. **364** (2002) 359,
  section 2.
-/

public section

noncomputable section

namespace EpsilonEridani
namespace QFT
namespace Scattering
namespace Photoproduction

open MeasureTheory ProbabilityTheory
open scoped Lorentz.Vector

/-- **Below the coherence scale the source is not resolved.** Let a source of mass `m ≠ 0` sit at
rest with four-momentum `p` and recoil to `p'` on the same mass shell, emitting the photon
`q = p - p'` of virtuality `Q² = -⟪q, q⟫ₘ`. For any normalised charge distribution `μ` of finite
mean square radius `R² = ∫ ‖r‖² dμ`, the form factor at the photon momentum satisfies
`1 - ‖F(q)‖ ≤ Q² (1 + Q² / (4 m²)) R² / 2`. -/
theorem one_sub_norm_charFun_spatialPart_sub_le {d : ℕ} {μ : Measure (EuclideanSpace ℝ (Fin d))}
    [IsProbabilityMeasure μ] (hμ : Integrable (fun r ↦ ‖r‖ ^ 2) μ) {p p' : Lorentz.Vector d}
    {m : ℝ} (hm : m ≠ 0) (hp : p.spatialPart = 0) (hp0 : p.timeComponent = m)
    (hp' : ⟪p', p'⟫ₘ = m ^ 2) :
    1 - ‖charFun μ (p - p').spatialPart‖ ≤
      -⟪p - p', p - p'⟫ₘ * (1 + -⟪p - p', p - p'⟫ₘ / (4 * m ^ 2)) * (∫ r, ‖r‖ ^ 2 ∂μ) / 2 := by
  rw [← Lorentz.Vector.norm_spatialPart_sub_sq_of_spatialPart_eq_zero_of_massShell hm hp hp0 hp']
  exact one_sub_norm_charFun_le hμ _

/-- **Below the coherence scale the Gaussian source is not resolved.** For the isotropic Gaussian
charge distribution of width `σ` in `d` dimensions, of mean square radius `R² = d σ²`
(`ProbabilityTheory.integral_norm_sq_map_smul_stdGaussian`), a source of mass `m ≠ 0` at rest
emitting the photon `q = p - p'` of virtuality `Q² = -⟪q, q⟫ₘ` has form factor
`1 - ‖F(q)‖ ≤ Q² (1 + Q² / (4 m²)) σ² / 2`, that is `Q² (1 + Q² / (4 m²)) R² / (2 d)`
(`one_sub_norm_charFun_map_smul_stdGaussian_spatialPart_sub_le_of_integral_norm_sq_eq`): isotropy
improves the bound `one_sub_norm_charFun_spatialPart_sub_le` for a general charge distribution
by the factor `d`. -/
theorem one_sub_norm_charFun_map_smul_stdGaussian_spatialPart_sub_le {d : ℕ} (σ : ℝ)
    {p p' : Lorentz.Vector d} {m : ℝ} (hm : m ≠ 0) (hp : p.spatialPart = 0)
    (hp0 : p.timeComponent = m) (hp' : ⟪p', p'⟫ₘ = m ^ 2) :
    1 - ‖charFun ((stdGaussian (EuclideanSpace ℝ (Fin d))).map (σ • ·)) (p - p').spatialPart‖ ≤
      -⟪p - p', p - p'⟫ₘ * (1 + -⟪p - p', p - p'⟫ₘ / (4 * m ^ 2)) * σ ^ 2 / 2 := by
  rw [← Lorentz.Vector.norm_spatialPart_sub_sq_of_spatialPart_eq_zero_of_massShell
    hm hp hp0 hp', mul_comm _ (σ ^ 2)]
  exact one_sub_norm_charFun_map_smul_stdGaussian_le σ _

/-- **Below the coherence scale the Gaussian source is not resolved**, in its mean square radius.
For the isotropic Gaussian charge distribution `ν` of width `σ` in `d` dimensions with mean square
radius `R² = ∫ ‖r‖² dν`, a source of mass `m ≠ 0` at rest emitting the photon `q = p - p'` of
virtuality `Q² = -⟪q, q⟫ₘ` has form factor `1 - ‖F(q)‖ ≤ Q² (1 + Q² / (4 m²)) R² / (2 d)`; this is
`one_sub_norm_charFun_map_smul_stdGaussian_spatialPart_sub_le` through `R² = d σ²`
(`ProbabilityTheory.integral_norm_sq_map_smul_stdGaussian`). -/
theorem one_sub_norm_charFun_map_smul_stdGaussian_spatialPart_sub_le_of_integral_norm_sq_eq
    {d : ℕ} {σ R : ℝ}
    (hR : ∫ r, ‖r‖ ^ 2 ∂((stdGaussian (EuclideanSpace ℝ (Fin d))).map (σ • ·)) = R ^ 2)
    {p p' : Lorentz.Vector d} {m : ℝ} (hm : m ≠ 0) (hp : p.spatialPart = 0)
    (hp0 : p.timeComponent = m) (hp' : ⟪p', p'⟫ₘ = m ^ 2) :
    1 - ‖charFun ((stdGaussian (EuclideanSpace ℝ (Fin d))).map (σ • ·)) (p - p').spatialPart‖ ≤
      -⟪p - p', p - p'⟫ₘ * (1 + -⟪p - p', p - p'⟫ₘ / (4 * m ^ 2)) * R ^ 2 / (2 * d) := by
  -- the mean square radius is `R² = σ² d`
  rw [integral_norm_sq_map_smul_stdGaussian, finrank_euclideanSpace_fin] at hR
  rcases eq_or_ne d 0 with rfl | hd
  · -- in no dimensions space is a point, where the form factor is one and the bound is zero
    rw [Nat.cast_zero, mul_zero, div_zero, Subsingleton.elim (p - p').spatialPart 0, charFun_zero]
    simp
  · have hrhs : -⟪p - p', p - p'⟫ₘ * (1 + -⟪p - p', p - p'⟫ₘ / (4 * m ^ 2)) * R ^ 2 / (2 * d) =
        -⟪p - p', p - p'⟫ₘ * (1 + -⟪p - p', p - p'⟫ₘ / (4 * m ^ 2)) * σ ^ 2 / 2 := by
      rw [← hR]
      field_simp
    rw [hrhs]
    exact one_sub_norm_charFun_map_smul_stdGaussian_spatialPart_sub_le σ hm hp hp0 hp'

/-- **Beyond the coherence scale the coherent rate of a Gaussian source is exponentially
suppressed.** For the isotropic Gaussian charge distribution of width `σ` in `d` dimensions, the
squared form factor at the spatial part of a four-momentum transfer `q` of virtuality
`Q² = -⟪q, q⟫ₘ` is at most `exp (-σ² Q²)`. Since the mean square radius is `R² = d σ²`
(`ProbabilityTheory.integral_norm_sq_map_smul_stdGaussian`), this is `exp (-Q² R² / d)`
(`norm_sq_charFun_map_smul_stdGaussian_spatialPart_le_of_integral_norm_sq_eq`). As a
mathematical statement the bound is frame-agnostic: it holds for the spatial part of `q` in every
frame. It is the suppression factor of the coherent rate when `q.spatialPart` is the momentum
transfer in the rest frame of the source, the frame in which the dilated Gaussian is its charge
distribution. -/
theorem norm_sq_charFun_map_smul_stdGaussian_spatialPart_le {d : ℕ} (σ : ℝ)
    (q : Lorentz.Vector d) :
    ‖charFun ((stdGaussian (EuclideanSpace ℝ (Fin d))).map (σ • ·)) q.spatialPart‖ ^ 2 ≤
      Real.exp (-(σ ^ 2 * -⟪q, q⟫ₘ)) := by
  rw [norm_sq_charFun_map_smul_stdGaussian]
  -- the virtuality is at most the squared spatial momentum,
  -- `Q² = ‖q.spatialPart‖² - (q⁰)² ≤ ‖q.spatialPart‖²`, in every frame
  have hQ : -⟪q, q⟫ₘ ≤ ‖q.spatialPart‖ ^ 2 :=
    Lorentz.Vector.neg_minkowskiProduct_self_le_norm_spatialPart_sq q
  exact Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_left hQ (sq_nonneg σ)))

/-- **Beyond the coherence scale the coherent rate of a Gaussian source is exponentially
suppressed**, in its mean square radius. For the isotropic Gaussian charge distribution `ν` of
width `σ` in `d` dimensions with mean square radius `R² = ∫ ‖r‖² dν`, the squared form factor at the
spatial part of a four-momentum transfer `q` of virtuality `Q² = -⟪q, q⟫ₘ` is at most
`exp (-Q² R² / d)`, which is `exp (-Q² R² / 3)` in three dimensions; this is
`norm_sq_charFun_map_smul_stdGaussian_spatialPart_le` through `R² = d σ²`
(`ProbabilityTheory.integral_norm_sq_map_smul_stdGaussian`), frame-agnostic in the same sense. -/
theorem norm_sq_charFun_map_smul_stdGaussian_spatialPart_le_of_integral_norm_sq_eq {d : ℕ}
    {σ R : ℝ}
    (hR : ∫ r, ‖r‖ ^ 2 ∂((stdGaussian (EuclideanSpace ℝ (Fin d))).map (σ • ·)) = R ^ 2)
    (q : Lorentz.Vector d) :
    ‖charFun ((stdGaussian (EuclideanSpace ℝ (Fin d))).map (σ • ·)) q.spatialPart‖ ^ 2 ≤
      Real.exp (-(-⟪q, q⟫ₘ * R ^ 2 / d)) := by
  -- the mean square radius is `R² = σ² d`
  rw [integral_norm_sq_map_smul_stdGaussian, finrank_euclideanSpace_fin] at hR
  rcases eq_or_ne d 0 with rfl | hd
  · -- in no dimensions the exponent vanishes, and the form factor has modulus at most one
    rw [Nat.cast_zero, div_zero, neg_zero, Real.exp_zero]
    exact pow_le_one₀ (norm_nonneg _) (norm_charFun_le_one _)
  · have hexp : -⟪q, q⟫ₘ * R ^ 2 / d = σ ^ 2 * -⟪q, q⟫ₘ := by
      rw [← hR]
      field_simp
    rw [hexp]
    exact norm_sq_charFun_map_smul_stdGaussian_spatialPart_le σ q

end Photoproduction
end Scattering
end QFT
end EpsilonEridani
