/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.QFT.Scattering.DIS.Kinematics.Bounds

/-!
# The target mass and the kinematic factor `γ`

`DisKinematics` carries no mass field, so the squared target mass is recovered from the hadron
momentum as the invariant `M² := p·p` (`DisKinematics.M2`). It is the mass that enters the
hadronic invariant mass, `W² = M² + 2 p·q - Q²` (`W2_eq_M2_add`).

The kinematic factor

  `γ² := 4 M² x² / Q²`

measures the target mass against the hard scale. In polarised deep-inelastic scattering `γ` is
the coefficient with which `g₂` enters the longitudinal asymmetry and `g₁ + g₂` the transverse
one, so it decides how well each asymmetry constrains each structure function; in unpolarised
scattering `1 + γ²` is the target-mass factor of the longitudinal structure function.

## Main results

* `DisKinematics.gammaSq_eq_M2_mul_Q2_div`: the equivalent invariant form
  `γ² = M² Q² / (p·q)²`, which needs no hypotheses.
* `DisKinematics.gammaSq_pos`, `DisKinematics.gamma_pos`: on the physical region of
  `BasicAssumptions` and for a massive target, `γ² > 0` and `γ > 0`.
* `DisKinematics.tendsto_gammaSq_zero`, `DisKinematics.tendsto_gamma_zero`: in the Bjorken
  limit `Q² → ∞` at fixed `x` and fixed target mass, `γ → 0`.

## References

* M. Anselmino, A. Efremov and E. Leader, *The theory and phenomenology of polarized deep
  inelastic scattering*, Phys. Rept. **261** (1995) 1; arXiv:hep-ph/9501369, §2.
* B. Lampe and E. Reya, *Spin physics and polarized structure functions*, Phys. Rept. **332**
  (2000) 1; arXiv:hep-ph/9810270, §2.
-/

public section

noncomputable section

namespace EpsilonEridani
namespace QFT
namespace Scattering
namespace DIS
namespace Kinematics

namespace DisKinematics

open Filter Topology

variable {V : Type} [AddCommGroup V] [Module ℝ V]

/-- The squared target mass `M² := p·p`, the invariant of the hadron momentum.
`DisKinematics` has no mass field, and this is how the target mass is recovered. -/
def M2 (g : Bilin V) (K : DisKinematics V) : ℝ :=
  g K.p K.p

lemma M2_def (g : Bilin V) (K : DisKinematics V) : K.M2 g = g K.p K.p := (rfl)

/-- The squared target mass is the invariant appearing in the hadronic invariant mass:
`W² = M² + 2 p·q - Q²`. -/
lemma W2_eq_M2_add (g : Bilin V) (K : DisKinematics V) (hSymm : g.IsSymm) :
    K.W2 g = K.M2 g + 2 * g K.p K.q - K.Q2 g :=
  W2_eq_with_Q2 g K hSymm

/-- The kinematic factor `γ² := 4 M² x² / Q²`. -/
def gammaSq (g : Bilin V) (K : DisKinematics V) : ℝ :=
  4 * K.M2 g * K.xBj g ^ 2 / K.Q2 g

lemma gammaSq_def (g : Bilin V) (K : DisKinematics V) :
    K.gammaSq g = 4 * K.M2 g * K.xBj g ^ 2 / K.Q2 g := (rfl)

/-- **The invariant form of `γ²`**: `γ² = M² Q² / (p·q)²`. Both sides are junk-valued `0` when
`Q² = 0` or `p·q = 0`, so the identity holds with no hypotheses. -/
theorem gammaSq_eq_M2_mul_Q2_div (g : Bilin V) (K : DisKinematics V) :
    K.gammaSq g = K.M2 g * K.Q2 g / g K.p K.q ^ 2 := by
  rw [gammaSq, xBj]
  rcases eq_or_ne (K.Q2 g) 0 with hQ | hQ
  · simp [hQ]
  rcases eq_or_ne (g K.p K.q) 0 with hpq | hpq
  · simp [hpq]
  field_simp
  ring

/-- `γ²` is non-negative for a target of non-negative squared mass and a spacelike probe. -/
lemma gammaSq_nonneg (g : Bilin V) (K : DisKinematics V) (hM : 0 ≤ K.M2 g)
    (hQ : 0 ≤ K.Q2 g) : 0 ≤ K.gammaSq g := by
  rw [gammaSq]
  positivity

/-- On the physical region of `BasicAssumptions`, `γ² > 0` for a massive target. -/
theorem gammaSq_pos (g : Bilin V) (K : DisKinematics V) (h : BasicAssumptions g K)
    (hM : 0 < K.M2 g) : 0 < K.gammaSq g := by
  have hx := xBj_pos g K h
  have hQ := h.q2_pos
  rw [gammaSq]
  positivity

/-- **The Bjorken limit of `γ²`.** Along a family of kinematics with fixed target mass and
fixed Bjorken variable `x` whose hard scale `Q²` tends to infinity, `γ² → 0`. -/
theorem tendsto_gammaSq_zero (g : Bilin V) {ι : Type*} {l : Filter ι}
    (K : ι → DisKinematics V) {M2 x : ℝ} (hM : ∀ i, (K i).M2 g = M2)
    (hx : ∀ i, (K i).xBj g = x) (hQ : Tendsto (fun i => (K i).Q2 g) l atTop) :
    Tendsto (fun i => (K i).gammaSq g) l (𝓝 0) := by
  have h := (hQ.inv_tendsto_atTop).const_mul (4 * M2 * x ^ 2)
  rw [mul_zero] at h
  refine h.congr fun i => ?_
  simp only [Pi.inv_apply, gammaSq, hM, hx, div_eq_mul_inv]

/-- The kinematic factor `γ := √γ²`; on the physical region this is `2 M x / Q`. -/
def gamma (g : Bilin V) (K : DisKinematics V) : ℝ :=
  Real.sqrt (K.gammaSq g)

lemma gamma_def (g : Bilin V) (K : DisKinematics V) :
    K.gamma g = Real.sqrt (K.gammaSq g) := (rfl)

lemma gamma_nonneg (g : Bilin V) (K : DisKinematics V) : 0 ≤ K.gamma g :=
  Real.sqrt_nonneg _

/-- `γ` squares to `γ²` whenever `γ²` is non-negative, in particular for a target of
non-negative squared mass and a spacelike probe (`gammaSq_nonneg`). -/
lemma gamma_sq (g : Bilin V) (K : DisKinematics V) (h : 0 ≤ K.gammaSq g) :
    K.gamma g ^ 2 = K.gammaSq g :=
  Real.sq_sqrt h

/-- On the physical region of `BasicAssumptions`, `γ > 0` for a massive target. -/
theorem gamma_pos (g : Bilin V) (K : DisKinematics V) (h : BasicAssumptions g K)
    (hM : 0 < K.M2 g) : 0 < K.gamma g :=
  Real.sqrt_pos.mpr (gammaSq_pos g K h hM)

/-- **The Bjorken limit of `γ`.** Along a family of kinematics with fixed target mass and
fixed Bjorken variable `x` whose hard scale `Q²` tends to infinity, `γ → 0`. -/
theorem tendsto_gamma_zero (g : Bilin V) {ι : Type*} {l : Filter ι}
    (K : ι → DisKinematics V) {M2 x : ℝ} (hM : ∀ i, (K i).M2 g = M2)
    (hx : ∀ i, (K i).xBj g = x) (hQ : Tendsto (fun i => (K i).Q2 g) l atTop) :
    Tendsto (fun i => (K i).gamma g) l (𝓝 0) := by
  simpa [gamma] using (tendsto_gammaSq_zero g K hM hx hQ).sqrt

end DisKinematics

end Kinematics
end DIS
end Scattering
end QFT
end EpsilonEridani
