/-
Copyright (c) 2026 The EpsilonEridani contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The EpsilonEridani contributors
-/
module

public import EpsilonEridani.QFT.Scattering.Photoproduction.Kinematics.Basic
public import EpsilonEridani.Mathematics.MeasureTheory.Measure.CharacteristicFunction.BasicExtensions
public import EpsilonEridani.Mathematics.Probability.Distributions.Gaussian.MultivariateExtensions

/-!
# The coherence condition for an extended source

A source of finite size emits an equivalent photon coherently, from its whole charge at once, only
if the photon does not resolve the charge distribution. Write the normalised charge distribution
of the source in its rest frame as a probability measure `μ` on space, with root-mean-square radius
`R`, `R² = ∫ ‖r‖² dμ`. A photon that leaves the source with four-momentum transfer `q` probes
`μ` through its form factor `F(q) = ∫ exp (i ⟪r, q⟫) dμ`, Mathlib's characteristic function
`MeasureTheory.charFun μ` evaluated at the spatial momentum `q` of the photon in that frame. The
coherent emission amplitude is that of a point charge times `F(q)`, so the coherent rate carries
`‖F(q)‖²`.

This file derives the coherence bound `Q² ≲ 1 / R²` on the virtuality `Q² = -⟪q, q⟫ₘ` from the
form factor, and then its consequence for the photon energy in the collider frame.

* Below the bound the source is not resolved, for any charge distribution of finite radius:
  in the source rest frame the spatial momentum transfer is fixed by the virtuality,
  `‖q‖² = Q² (1 + Q² / (4 m²))`
  (`Lorentz.Vector.norm_spatialPart_sub_sq_of_spatialPart_eq_zero_of_minkowskiProduct_self_eq`),
  and `1 - ‖F(q)‖ ≤ ‖q‖² R² / 2`
  (`one_sub_norm_charFun_spatialPart_sub_le`). So `‖F‖` stays close to one, the value for a point
  charge, while `Q² R²` is small against one.
* Beyond the bound the coherent rate is suppressed by the square of the form factor. For the
  isotropic Gaussian charge distribution in `d` dimensions, `‖F(q)‖² ≤ exp (-Q² R² / d)`
  (`norm_sq_charFun_map_smul_stdGaussian_spatialPart_le`), which is `exp (-Q² R² / 3)` in three
  dimensions. It is composed from the general squared form factor
  `ProbabilityTheory.norm_sq_charFun_map_smul_stdGaussian` and second moment
  `ProbabilityTheory.integral_norm_sq_map_smul_stdGaussian` of the dilated Gaussian, and uses
  only `Q² ≤ ‖q‖²`, which holds in every frame
  (`Lorentz.Vector.neg_minkowskiProduct_self_le_norm_spatialPart_sq`). Some shape assumption
  is needed here: the form factor of two point charges a distance `2 R` apart is `cos ⟪r₀, q⟫`
  and does not decay at all.
* The photon energy in the collider frame is bounded by the Lorentz factor over the radius. The
  `Kinematics.ChargedSource` lemmas
  `energy_sq_lt_gamma_sq_mul_one_sub_energyFraction_mul_virtuality_of_mem_photonRegion` and
  `energy_mul_radius_lt_gamma_of_virtuality_mul_radius_sq_le_one` bound the energy of a photon
  in the photon region by the virtuality, `k² < γ² (1 - x) Q²`, and then, within the coherence
  bound `Q² R² ≤ 1`, by the Lorentz factor over the radius, `k R < γ`. Here `R` is the radius
  `s.radius` of the source: the charge radius that `ChargedSource` carries as an independent
  datum, not a quantity derived from the charge measure `μ` of the opening paragraph, and the
  coherence bound `Q² R² ≤ 1` enters as a hypothesis of the energy bound, not as a consequence
  of the two form-factor bounds above.

## References

* J. D. Jackson, *Classical Electrodynamics*, 3rd ed., Wiley (1999), section 15.5.
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

/-- **Below the coherence bound the source is not resolved.** Let a source of mass `m ≠ 0` sit at
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
  rw [← Lorentz.Vector.norm_spatialPart_sub_sq_of_spatialPart_eq_zero_of_minkowskiProduct_self_eq
    hm hp hp0 hp']
  exact one_sub_norm_charFun_le hμ _

/-- **Beyond the coherence bound the coherent rate of a Gaussian source is exponentially
suppressed.** For the isotropic Gaussian charge distribution `μ` of width `σ` in `d` dimensions,
whose mean square radius is `R² = ∫ ‖r‖² dμ = d σ²`, the squared form factor at the spatial part
of a four-momentum transfer `q` of virtuality `Q² = -⟪q, q⟫ₘ` is at most `exp (-Q² R² / d)`. -/
theorem norm_sq_charFun_map_smul_stdGaussian_spatialPart_le {d : ℕ} (σ : ℝ)
    (q : Lorentz.Vector d) :
    ‖charFun ((stdGaussian (EuclideanSpace ℝ (Fin d))).map (σ • ·)) q.spatialPart‖ ^ 2 ≤
      Real.exp (-(-⟪q, q⟫ₘ *
        (∫ r, ‖r‖ ^ 2 ∂(stdGaussian (EuclideanSpace ℝ (Fin d))).map (σ • ·)) / d)) := by
  rw [norm_sq_charFun_map_smul_stdGaussian, integral_norm_sq_map_smul_stdGaussian,
    finrank_euclideanSpace_fin]
  -- the virtuality is at most the squared spatial momentum, `Q² = ‖q‖² - (q⁰)² ≤ ‖q‖²`, in
  -- every frame
  have hQ : -⟪q, q⟫ₘ ≤ ‖q.spatialPart‖ ^ 2 :=
    Lorentz.Vector.neg_minkowskiProduct_self_le_norm_spatialPart_sq q
  refine Real.exp_le_exp.2 ?_
  -- the `d = 0` branch only handles the `0 / 0` degeneracy of the statement, in which the
  -- right-hand side is `exp 0 = 1`
  rcases eq_or_ne d 0 with rfl | hd
  · simp only [Nat.cast_zero, mul_zero, zero_div, neg_zero]
    nlinarith [sq_nonneg σ, sq_nonneg ‖q.spatialPart‖]
  · have hd' : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hd
    rw [show -⟪q, q⟫ₘ * (σ ^ 2 * d) / d = σ ^ 2 * -⟪q, q⟫ₘ by field_simp]
    nlinarith [mul_le_mul_of_nonneg_left hQ (sq_nonneg σ)]

namespace Kinematics
namespace ChargedSource

variable {s : ChargedSource}

/-- **The photon energy of coherent emission is bounded by the Lorentz factor over the radius.**
If a massive source of radius `R` and Lorentz factor `γ` emits a photon of its photon region within
the coherence bound `Q² R² ≤ 1`, the photon energy in the collider frame satisfies `k R < γ`. -/
theorem energy_mul_radius_lt_gamma_of_virtuality_mul_radius_sq_le_one
    (hm : 0 < s.mass) {θmax : ℝ} {k : PhotonKinematics} (hk : k ∈ s.photonRegion θmax)
    (hcoh : k.virtuality * s.radius ^ 2 ≤ 1) : k.energy * s.radius < s.gamma := by
  have hγ := gamma_pos_of_mem_photonRegion hm hk
  have hx0 := energyFraction_pos_of_mem_photonRegion hm.le hk
  have hx1 := energyFraction_lt_one_of_mem_photonRegion hm.le hk
  have hc : 0 ≤ s.gamma ^ 2 * (1 - k.energyFraction s) :=
    mul_nonneg (sq_nonneg _) (by linarith)
  -- `(k R)² ≤ γ² (1 - x) Q² R² ≤ γ² (1 - x) < γ²`
  have hsq : (k.energy * s.radius) ^ 2 < s.gamma ^ 2 :=
    calc (k.energy * s.radius) ^ 2 = k.energy ^ 2 * s.radius ^ 2 := mul_pow _ _ _
      _ ≤ s.gamma ^ 2 * (1 - k.energyFraction s) * (k.virtuality * s.radius ^ 2) := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right
          (energy_sq_lt_gamma_sq_mul_one_sub_energyFraction_mul_virtuality_of_mem_photonRegion
            hm hk).le (sq_nonneg _)
      _ ≤ s.gamma ^ 2 * (1 - k.energyFraction s) := mul_le_of_le_one_right hc hcoh
      _ < s.gamma ^ 2 := by nlinarith [mul_pos (pow_pos hγ 2) hx0]
  exact lt_of_abs_lt (abs_lt_of_sq_lt_sq hsq hγ.le)

end ChargedSource
end Kinematics

end Photoproduction
end Scattering
end QFT
end EpsilonEridani
