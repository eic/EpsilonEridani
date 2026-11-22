/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.Relativity.Tensors.RealTensor.Vector.MinkowskiProductExtensions
public import EpsilonEridani.Relativity.LorentzGroup.Boosts.GeneralizedExtensions
public import Physlib.Relativity.Causality.CausallyFollows
public import Physlib.Relativity.LorentzGroup.Restricted.Basic
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
# Target data and elastic kinematics for gravitational form factors

The gravitational form factors of a hadron are scalar functions of the momentum transfer of an
elastic transition `h(p) → h(p')` through the energy-momentum tensor. This module fixes the target
data, the kinematics of the transition, the frame in which spatial densities are defined, and the
dictionary between the variable `t ≤ 0` of the literature and the variable `Q² = -t ≥ 0` in which
the form factors are written.

* `Target` records the mass `M > 0` and the spin of the hadron (as `twiceSpin = 2 s`), so that a
  statement about a spin-zero and one about a spin-half target take visibly different arguments.
* `ElasticKinematics T d` is a pair of on-shell momenta `p`, `p'` of the target `T` in
  `d + 1`-dimensional Minkowski space, both with positive energy. It defines the average momentum
  `P = (p + p') / 2`, the transfer `Δ = p' - p`, `t = Δ²` and `qSq = Q² = -t` as an element of
  `ℝ≥0`. The identities `P · Δ = 0`, `P² = M² - t / 4`, `p · p' = M² - t / 2` hold for any two
  vectors on a common mass shell and are taken from
  `EpsilonEridani.Relativity.Tensors.RealTensor.Vector.MinkowskiProductExtensions`. The constraint
  `t ≤ 0` (`ElasticKinematics.tMom_nonpos`) is proved from the mass shell and positive energy, by
  the reverse Cauchy–Schwarz inequality `M² ≤ p · p'`, and `t = 0` exactly in the forward
  direction `p = p'` (`ElasticKinematics.tMom_eq_zero_iff`). Every `Q² ≥ 0` is attained once there
  is a spatial dimension (`ElasticKinematics.range_qSq`).
* `ElasticKinematics.IsBreitFrame` is the frame in which `P` has no spatial part. In it
  `Δ⁰ = 0`, `p = (E, -Δ/2)`, `p' = (E, Δ/2)` with `E = √(M² + Q²/4)`, and `Q² = |Δ|²` is the
  square of the three-momentum transfer
  (`ElasticKinematics.IsBreitFrame.coe_qSq_eq_sq_norm_spatialPart_delta`). Every transition is
  carried by some restricted Lorentz transformation to a transition of the same target in its
  Breit frame (`ElasticKinematics.exists_isBreitFrame`), and `t` is unchanged by it
  (`ElasticKinematics.tMom_eq_of_smul`).
* `ofLiteratureT` turns a function of `t ≤ 0`, as the literature writes form factors, into a
  function of `Q² ≥ 0`. Its slope at the origin is minus the `t`-slope
  (`hasDerivWithinAt_ofLiteratureT_iff`, `derivWithin_ofLiteratureT`), and `∫_0^∞ dQ²` of it is
  `∫_{-∞}^0 dt` of the original (`setIntegral_ofLiteratureT`). A slope or a radius integral read
  off in the wrong variable changes sign, which is why every transcribed formula goes through
  this map.

The momenta, `P`, `Δ` and `t` are named as in `EpsilonEridani.Particles.Parton.GPD.Kinematics`,
whose `OffForwardKinematics` describes the same transition together with a light-like direction
and positive plus-momenta; the form factors depend on neither, and here `t ≤ 0` comes from
positive energy.

## References

* M. V. Polyakov and P. Schweitzer, *Forces inside hadrons: pressure, surface tension, mechanical
  radius, and all that*, Int. J. Mod. Phys. A **33** (2018) 1830025 (arXiv:1805.06596), §2.
* X. Ji, *Deeply virtual Compton scattering*, Phys. Rev. D **55** (1997) 7114
  (arXiv:hep-ph/9609381).
-/

public section

noncomputable section

namespace EpsilonEridani
namespace Particles
namespace Hadron
namespace GravitationalFormFactors

open Lorentz Lorentz.Vector Set MeasureTheory
open scoped InnerProductSpace NNReal

/-- A target hadron: its mass `M > 0` and its spin `s`, recorded as the natural number `2 s`
(`0` for a spin-zero target such as the pion, `1` for a spin-half target such as the nucleon). -/
@[ext]
structure Target where
  /-- The mass `M` of the target. -/
  mass : ℝ
  /-- The mass is positive. -/
  mass_pos : 0 < mass
  /-- Twice the spin of the target. -/
  twiceSpin : ℕ

/-- Elastic kinematics `h(p) → h(p')` of a target `T` in `d + 1`-dimensional Minkowski space:
both momenta are on the mass shell of `T` and carry positive energy. -/
@[ext]
structure ElasticKinematics (T : Target) (d : ℕ) where
  /-- The incoming target momentum. -/
  p : Vector d
  /-- The outgoing target momentum. -/
  pPrime : Vector d
  /-- The incoming target is on its mass shell. -/
  minkowskiProduct_p_self : ⟪p, p⟫ₘ = T.mass ^ 2
  /-- The outgoing target is on its mass shell. -/
  minkowskiProduct_pPrime_self : ⟪pPrime, pPrime⟫ₘ = T.mass ^ 2
  /-- The incoming target has positive energy. -/
  timeComponent_p_pos : 0 < p.timeComponent
  /-- The outgoing target has positive energy. -/
  timeComponent_pPrime_pos : 0 < pPrime.timeComponent

namespace ElasticKinematics

attribute [simp] minkowskiProduct_p_self minkowskiProduct_pPrime_self

variable {T : Target} {d : ℕ} (K : ElasticKinematics T d)

/-- The average target momentum `P = (p + p') / 2`. -/
def avgMomentum : Vector d := (2⁻¹ : ℝ) • (K.p + K.pPrime)

lemma avgMomentum_def : K.avgMomentum = (2⁻¹ : ℝ) • (K.p + K.pPrime) := (rfl)

/-- The momentum transfer `Δ = p' - p`. -/
def delta : Vector d := K.pPrime - K.p

lemma delta_def : K.delta = K.pPrime - K.p := (rfl)

/-- The invariant momentum transfer `t = Δ²`. -/
def tMom : ℝ := ⟪K.delta, K.delta⟫ₘ

lemma tMom_def : K.tMom = ⟪K.delta, K.delta⟫ₘ := (rfl)

lemma p_eq_avgMomentum_sub : K.p = K.avgMomentum - (2⁻¹ : ℝ) • K.delta := by
  rw [avgMomentum_def, delta_def]
  module

lemma pPrime_eq_avgMomentum_add : K.pPrime = K.avgMomentum + (2⁻¹ : ℝ) • K.delta := by
  rw [avgMomentum_def, delta_def]
  module

/-- The two target momenta have the same Minkowski square. -/
lemma minkowskiProduct_p_self_eq_minkowskiProduct_pPrime_self :
    ⟪K.p, K.p⟫ₘ = ⟪K.pPrime, K.pPrime⟫ₘ := by
  rw [K.minkowskiProduct_p_self, K.minkowskiProduct_pPrime_self]

/-- The product of the two target momenta is `p · p' = M² - t / 2`. -/
lemma minkowskiProduct_p_pPrime_eq : ⟪K.p, K.pPrime⟫ₘ = T.mass ^ 2 - K.tMom / 2 :=
  minkowskiProduct_eq_of_minkowskiProduct_self_eq K.minkowskiProduct_p_self
    K.minkowskiProduct_pPrime_self

/-- For an elastic transition the average momentum is orthogonal to the transfer, `P · Δ = 0`. -/
@[simp]
lemma minkowskiProduct_avgMomentum_delta_eq_zero : ⟪K.avgMomentum, K.delta⟫ₘ = 0 :=
  minkowskiProduct_inv_two_smul_add_sub_eq_zero
    K.minkowskiProduct_p_self_eq_minkowskiProduct_pPrime_self

/-- For an elastic transition the transfer is orthogonal to the average momentum, `Δ · P = 0`. -/
@[simp]
lemma minkowskiProduct_delta_avgMomentum_eq_zero : ⟪K.delta, K.avgMomentum⟫ₘ = 0 := by
  rw [minkowskiProduct_symm, minkowskiProduct_avgMomentum_delta_eq_zero]

/-- The invariant mass squared of the average momentum, `P² = M² - t / 4`. -/
@[simp]
lemma minkowskiProduct_avgMomentum_self_eq :
    ⟪K.avgMomentum, K.avgMomentum⟫ₘ = T.mass ^ 2 - K.tMom / 4 :=
  minkowskiProduct_inv_two_smul_add_self_eq K.minkowskiProduct_p_self
    K.minkowskiProduct_pPrime_self

/-- The incoming momentum paired with the transfer is `p · Δ = -t / 2`. -/
lemma minkowskiProduct_p_delta_eq : ⟪K.p, K.delta⟫ₘ = -K.tMom / 2 :=
  minkowskiProduct_left_sub_eq_neg_minkowskiProduct_sub_self_div_two
    K.minkowskiProduct_p_self_eq_minkowskiProduct_pPrime_self

/-- The outgoing momentum paired with the transfer is `p' · Δ = t / 2`. -/
lemma minkowskiProduct_pPrime_delta_eq : ⟪K.pPrime, K.delta⟫ₘ = K.tMom / 2 :=
  minkowskiProduct_right_sub_eq_minkowskiProduct_sub_self_div_two
    K.minkowskiProduct_p_self_eq_minkowskiProduct_pPrime_self

/-- The average momentum paired with the incoming momentum is `P · p = M² - t / 4`. -/
lemma minkowskiProduct_avgMomentum_p_eq : ⟪K.avgMomentum, K.p⟫ₘ = T.mass ^ 2 - K.tMom / 4 := by
  simp [K.p_eq_avgMomentum_sub]

/-- The average momentum paired with the outgoing momentum is `P · p' = M² - t / 4`. -/
lemma minkowskiProduct_avgMomentum_pPrime_eq :
    ⟪K.avgMomentum, K.pPrime⟫ₘ = T.mass ^ 2 - K.tMom / 4 := by
  simp [K.pPrime_eq_avgMomentum_add]

/-- The incoming momentum lies in the causal future of the origin. -/
lemma causallyFollows_zero_p : causallyFollows 0 K.p :=
  causallyFollows_zero_iff.mpr
    ⟨by rw [K.minkowskiProduct_p_self]; positivity, K.timeComponent_p_pos.le⟩

/-- The outgoing momentum lies in the causal future of the origin. -/
lemma causallyFollows_zero_pPrime : causallyFollows 0 K.pPrime :=
  causallyFollows_zero_iff.mpr
    ⟨by rw [K.minkowskiProduct_pPrime_self]; positivity, K.timeComponent_pPrime_pos.le⟩

/-- The reverse Cauchy–Schwarz inequality for the two target momenta, `M² ≤ p · p'`. -/
theorem sq_mass_le_minkowskiProduct_p_pPrime : T.mass ^ 2 ≤ ⟪K.p, K.pPrime⟫ₘ := by
  have h := sqrt_mul_sqrt_le_minkowskiProduct_of_causallyFollows K.causallyFollows_zero_p
    K.causallyFollows_zero_pPrime
  rwa [K.minkowskiProduct_p_self, K.minkowskiProduct_pPrime_self,
    Real.sqrt_sq T.mass_pos.le, ← sq] at h

/-- The invariant momentum transfer of an elastic transition is non-positive, `t ≤ 0`. -/
theorem tMom_nonpos : K.tMom ≤ 0 := by
  linarith [K.sq_mass_le_minkowskiProduct_p_pPrime, K.minkowskiProduct_p_pPrime_eq]

/-- The momentum transfer vanishes exactly in the forward direction: `t = 0 ↔ p = p'`. -/
theorem tMom_eq_zero_iff : K.tMom = 0 ↔ K.p = K.pPrime := by
  refine ⟨fun ht => ?_, fun h => by simp [tMom_def, delta_def, h]⟩
  have hM := T.mass_pos
  have heq : ⟪K.p, K.pPrime⟫ₘ = √⟪K.p, K.p⟫ₘ * √⟪K.pPrime, K.pPrime⟫ₘ := by
    rw [K.minkowskiProduct_p_pPrime_eq, ht, K.minkowskiProduct_p_self,
      K.minkowskiProduct_pPrime_self, Real.sqrt_sq hM.le]
    ring
  -- equality in reverse Cauchy–Schwarz makes the momenta proportional, and the common mass
  -- shell fixes the factor to one
  have hp : ⟪K.p, K.p⟫ₘ ≠ 0 := by rw [K.minkowskiProduct_p_self]; positivity
  have hp' : ⟪K.pPrime, K.pPrime⟫ₘ ≠ 0 := by rw [K.minkowskiProduct_pPrime_self]; positivity
  have hpp := K.minkowskiProduct_p_self_eq_minkowskiProduct_pPrime_self
  obtain ⟨μ, hμ, h | h⟩ := (minkowskiProduct_eq_iff_of_causallyFollows K.causallyFollows_zero_p
    K.causallyFollows_zero_pPrime).mp heq
  · exact (eq_of_eq_smul_of_minkowskiProduct_self_eq hμ hp hpp.symm h).symm
  · exact eq_of_eq_smul_of_minkowskiProduct_self_eq hμ hp' hpp h

/-- The non-negative momentum-transfer variable `Q² = -t ≥ 0`, in which the gravitational form
factors are written. -/
def qSq : ℝ≥0 := ⟨-K.tMom, neg_nonneg.mpr K.tMom_nonpos⟩

/-- The dictionary `Q² = -t`. This is deliberately not a `simp` lemma: `Q²` is the variable in
which statements about form factors are written, so `simp` should not rewrite it into `t`. -/
lemma coe_qSq : (K.qSq : ℝ) = -K.tMom := (rfl)

/-- `Q² = 0` exactly in the forward direction `p = p'`. -/
lemma qSq_eq_zero_iff : K.qSq = 0 ↔ K.p = K.pPrime := by
  rw [← NNReal.coe_eq_zero, coe_qSq, neg_eq_zero, tMom_eq_zero_iff]

/-- The invariant mass squared of the average momentum in terms of `Q²`, `P² = M² + Q² / 4`. -/
lemma minkowskiProduct_avgMomentum_self_eq_add_qSq :
    ⟪K.avgMomentum, K.avgMomentum⟫ₘ = T.mass ^ 2 + K.qSq / 4 := by
  rw [minkowskiProduct_avgMomentum_self_eq, coe_qSq]
  ring

/-- The average momentum is time-like, `0 < P²`. -/
lemma minkowskiProduct_avgMomentum_self_pos : 0 < ⟪K.avgMomentum, K.avgMomentum⟫ₘ := by
  rw [minkowskiProduct_avgMomentum_self_eq_add_qSq]
  positivity [T.mass_pos]

/-- The average momentum has positive energy. -/
lemma timeComponent_avgMomentum_pos : 0 < K.avgMomentum.timeComponent := by
  have h1 := K.timeComponent_p_pos
  have h2 := K.timeComponent_pPrime_pos
  simp only [avgMomentum_def, timeComponent, apply_smul, apply_add]
  positivity

/-! ### Attained momentum transfers -/

/-- Every target has an elastic transition, for instance the forward one at rest,
`p = p' = (M, 0)`. -/
instance : Nonempty (ElasticKinematics T d) :=
  ⟨{ p := ofTimeAndSpatial T.mass 0
     pPrime := ofTimeAndSpatial T.mass 0
     minkowskiProduct_p_self := by simp [sq]
     minkowskiProduct_pPrime_self := by simp [sq]
     timeComponent_p_pos := by simpa using T.mass_pos
     timeComponent_pPrime_pos := by simpa using T.mass_pos }⟩

/-- With at least one spatial dimension every `Q² ≥ 0` is the momentum transfer of an elastic
transition of `T`: the transition with energies `√(M² + Q² / 4)` and opposite three-momenta of
length `√Q² / 2`. -/
theorem range_qSq (hd : 1 ≤ d) : range (qSq : ElasticKinematics T d → ℝ≥0) = univ := by
  refine eq_univ_of_forall fun q => ?_
  set E := √(T.mass ^ 2 + q / 4)
  set s : EuclideanSpace ℝ (Fin d) := (√(q : ℝ) / 2) • EuclideanSpace.single ⟨0, hd⟩ 1
  have hs : ⟪s, s⟫_ℝ = q / 4 := by
    rw [real_inner_self_eq_norm_sq, norm_smul, PiLp.norm_single, norm_one, mul_one,
      Real.norm_eq_abs, sq_abs, div_pow, Real.sq_sqrt q.coe_nonneg]
    norm_num
  have hE : E * E = T.mass ^ 2 + q / 4 := Real.mul_self_sqrt (by positivity)
  have hE0 : 0 < E := Real.sqrt_pos.mpr (by positivity [T.mass_pos])
  refine ⟨{ p := ofTimeAndSpatial E (-s)
            pPrime := ofTimeAndSpatial E s
            minkowskiProduct_p_self := ?_
            minkowskiProduct_pPrime_self := ?_
            timeComponent_p_pos := by simpa using hE0
            timeComponent_pPrime_pos := by simpa using hE0 }, ?_⟩
  · rw [minkowskiProduct_ofTimeAndSpatial_eq, inner_neg_left, inner_neg_right, neg_neg, hE, hs]
    ring
  · rw [minkowskiProduct_ofTimeAndSpatial_eq, hE, hs]
    ring
  · refine NNReal.eq ?_
    rw [coe_qSq, tMom_def, delta_def, minkowskiProduct_sub_self]
    simp only [minkowskiProduct_ofTimeAndSpatial_eq, inner_neg_left, inner_neg_right, neg_neg,
      hE, hs]
    ring

/-! ### Lorentz invariance of the momentum transfer -/

/-- Two elastic transitions related by a Lorentz transformation have the same `t`. -/
lemma tMom_eq_of_smul {K' : ElasticKinematics T d} {Λ : LorentzGroup d}
    (hp : K'.p = Λ • K.p) (hp' : K'.pPrime = Λ • K.pPrime) : K'.tMom = K.tMom := by
  rw [tMom_def, tMom_def, delta_def, delta_def, hp, hp', ← smul_sub, minkowskiProduct_invariant]

/-- Two elastic transitions related by a Lorentz transformation have the same `Q²`. -/
lemma qSq_eq_of_smul {K' : ElasticKinematics T d} {Λ : LorentzGroup d}
    (hp : K'.p = Λ • K.p) (hp' : K'.pPrime = Λ • K.pPrime) : K'.qSq = K.qSq :=
  NNReal.eq <| by rw [coe_qSq, coe_qSq, K.tMom_eq_of_smul hp hp']

/-! ### The Breit frame -/

/-- The Breit frame of an elastic transition: the average momentum `P` has no spatial part, so
that `p = (E, -Δ/2)` and `p' = (E, Δ/2)`. Spatial densities of the energy-momentum tensor are
Fourier transforms in this frame. -/
def IsBreitFrame : Prop := K.avgMomentum.spatialPart = 0

/-- The defining property of the Breit frame, `P = (P⁰, 0)`. -/
lemma isBreitFrame_iff : K.IsBreitFrame ↔ K.avgMomentum.spatialPart = 0 := Iff.rfl

/-- The spatial part of the average momentum is the average of the two three-momenta. -/
lemma spatialPart_avgMomentum_eq :
    K.avgMomentum.spatialPart = (2⁻¹ : ℝ) • (K.p.spatialPart + K.pPrime.spatialPart) := by
  rw [avgMomentum_def, spatialPart_smul, spatialPart_add]

/-- The Breit frame is the frame in which the two target three-momenta are opposite. -/
lemma isBreitFrame_iff_spatialPart_pPrime_eq_neg :
    K.IsBreitFrame ↔ K.pPrime.spatialPart = -K.p.spatialPart := by
  rw [isBreitFrame_iff, spatialPart_avgMomentum_eq, smul_eq_zero, eq_neg_iff_add_eq_zero,
    add_comm]
  simp

namespace IsBreitFrame

variable {K}

/-- In the Breit frame the average momentum has no spatial part. -/
lemma spatialPart_avgMomentum_eq_zero (h : K.IsBreitFrame) : K.avgMomentum.spatialPart = 0 :=
  K.isBreitFrame_iff.mp h

/-- In the Breit frame the energy transfer vanishes, `Δ⁰ = 0`. -/
lemma timeComponent_delta_eq_zero (h : K.IsBreitFrame) : K.delta.timeComponent = 0 := by
  have hPΔ := K.minkowskiProduct_avgMomentum_delta_eq_zero
  rw [minkowskiProduct_eq_timeComponent_spatialPart, h.spatialPart_avgMomentum_eq_zero,
    inner_zero_left, sub_zero] at hPΔ
  exact (mul_eq_zero.mp hPΔ).resolve_left K.timeComponent_avgMomentum_pos.ne'

/-- In the Breit frame `Q²` is the square of the three-momentum transfer, `Q² = |Δ|²`. -/
lemma coe_qSq_eq_sq_norm_spatialPart_delta (h : K.IsBreitFrame) :
    (K.qSq : ℝ) = ‖K.delta.spatialPart‖ ^ 2 := by
  rw [coe_qSq, tMom_def, minkowskiProduct_self_eq_sq_sub, h.timeComponent_delta_eq_zero]
  ring

/-- In the Breit frame the energy of the average momentum is `P⁰ = √(M² + Q² / 4)`. -/
lemma timeComponent_avgMomentum_eq (h : K.IsBreitFrame) :
    K.avgMomentum.timeComponent = √(T.mass ^ 2 + K.qSq / 4) := by
  have hP := K.minkowskiProduct_avgMomentum_self_eq_add_qSq
  rw [minkowskiProduct_self_eq_sq_sub, h.spatialPart_avgMomentum_eq_zero, norm_zero] at hP
  rw [← hP, zero_pow two_ne_zero, sub_zero, Real.sqrt_sq K.timeComponent_avgMomentum_pos.le]

/-- In the Breit frame the incoming energy is `p⁰ = √(M² + Q² / 4)`. -/
lemma timeComponent_p_eq (h : K.IsBreitFrame) :
    K.p.timeComponent = √(T.mass ^ 2 + K.qSq / 4) := by
  rw [← h.timeComponent_avgMomentum_eq]
  conv_lhs => rw [K.p_eq_avgMomentum_sub]
  simp [timeComponent, h.timeComponent_delta_eq_zero]

/-- In the Breit frame the outgoing energy is `p'⁰ = √(M² + Q² / 4)`. -/
lemma timeComponent_pPrime_eq (h : K.IsBreitFrame) :
    K.pPrime.timeComponent = √(T.mass ^ 2 + K.qSq / 4) := by
  rw [← h.timeComponent_avgMomentum_eq]
  conv_lhs => rw [K.pPrime_eq_avgMomentum_add]
  simp [timeComponent, h.timeComponent_delta_eq_zero]

/-- In the Breit frame the incoming three-momentum is `-Δ / 2`. -/
lemma spatialPart_p_eq (h : K.IsBreitFrame) :
    K.p.spatialPart = -((2⁻¹ : ℝ) • K.delta.spatialPart) := by
  rw [K.p_eq_avgMomentum_sub, spatialPart_sub, spatialPart_smul,
    h.spatialPart_avgMomentum_eq_zero, zero_sub]

/-- In the Breit frame the outgoing three-momentum is `Δ / 2`. -/
lemma spatialPart_pPrime_eq (h : K.IsBreitFrame) :
    K.pPrime.spatialPart = (2⁻¹ : ℝ) • K.delta.spatialPart := by
  rw [K.pPrime_eq_avgMomentum_add, spatialPart_add, spatialPart_smul,
    h.spatialPart_avgMomentum_eq_zero, zero_add]

end IsBreitFrame

/-- Every elastic transition is carried by some restricted Lorentz transformation `Λ` to an elastic
transition of the same target, with momenta `Λ p`, `Λ p'`, in its Breit frame. By
`tMom_eq_of_smul` the transformed transition has the same `t`. -/
theorem exists_isBreitFrame :
    ∃ Λ ∈ LorentzGroup.restricted d, ∃ K' : ElasticKinematics T d,
      K'.p = Λ • K.p ∧ K'.pPrime = Λ • K.pPrime ∧ K'.IsBreitFrame := by
  -- the witness is the generalised boost taking the velocity `P / √(P²)` of the average momentum
  -- to rest
  obtain ⟨Λ, hΛ, hΛP, hpos⟩ := LorentzGroup.exists_mem_restricted_spatialPart_smul_eq_zero
    K.minkowskiProduct_avgMomentum_self_pos K.timeComponent_avgMomentum_pos
  have hM := pow_pos T.mass_pos 2
  have hp : 0 < ⟪K.avgMomentum, K.p⟫ₘ := by
    rw [K.minkowskiProduct_avgMomentum_p_eq]
    linarith [K.tMom_nonpos]
  have hp' : 0 < ⟪K.avgMomentum, K.pPrime⟫ₘ := by
    rw [K.minkowskiProduct_avgMomentum_pPrime_eq]
    linarith [K.tMom_nonpos]
  let K' : ElasticKinematics T d :=
    { p := Λ • K.p
      pPrime := Λ • K.pPrime
      minkowskiProduct_p_self := by rw [minkowskiProduct_invariant, K.minkowskiProduct_p_self]
      minkowskiProduct_pPrime_self := by
        rw [minkowskiProduct_invariant, K.minkowskiProduct_pPrime_self]
      timeComponent_p_pos := hpos _ hp
      timeComponent_pPrime_pos := hpos _ hp' }
  have hav : K'.avgMomentum = Λ • K.avgMomentum := by
    rw [avgMomentum_def, avgMomentum_def, smul_comm, Lorentz.Vector.smul_add]
  exact ⟨Λ, hΛ, K', rfl, rfl, by rw [isBreitFrame_iff, hav, hΛP]⟩

end ElasticKinematics

/-! ### The literature dictionary `t ↦ Q² = -t` -/

/-- The dictionary from the literature's variable `t ≤ 0` to `Q² = -t ≥ 0`: a function `f` of `t`
becomes the function `Q² ↦ f (-Q²)` on `ℝ≥0`. Only the values of `f` on `t ≤ 0` enter
(`ofLiteratureT_eq_ofLiteratureT_iff`). -/
def ofLiteratureT (f : ℝ → ℝ) : ℝ≥0 → ℝ := fun q => f (-(q : ℝ))

@[simp]
lemma ofLiteratureT_apply (f : ℝ → ℝ) (q : ℝ≥0) : ofLiteratureT f q = f (-(q : ℝ)) := (rfl)

/-- On an elastic transition, the translated function evaluated at `Q²` is the original evaluated
at `t`. This is not a `simp` lemma: its left-hand side is rewritten by `ofLiteratureT_apply`. -/
lemma ofLiteratureT_qSq {T : Target} {d : ℕ} (f : ℝ → ℝ) (K : ElasticKinematics T d) :
    ofLiteratureT f K.qSq = f K.tMom := by
  rw [ofLiteratureT_apply, ElasticKinematics.coe_qSq, neg_neg]

/-- On `Q² ≥ 0` read as a real number, the translated function is `Q² ↦ f (-Q²)`. -/
lemma ofLiteratureT_toNNReal (f : ℝ → ℝ) {q : ℝ} (hq : 0 ≤ q) :
    ofLiteratureT f q.toNNReal = f (-q) := by
  rw [ofLiteratureT_apply, Real.coe_toNNReal q hq]

/-- On `Q² ≥ 0` read as a real number, the translated function agrees with `Q² ↦ f (-Q²)`. -/
lemma eqOn_ofLiteratureT_toNNReal (f : ℝ → ℝ) :
    EqOn (fun q : ℝ => ofLiteratureT f q.toNNReal) (fun q => f (-q)) (Ici 0) :=
  fun _ hq => ofLiteratureT_toNNReal f hq

/-- Two functions of `t` give the same function of `Q²` exactly when they agree on `t ≤ 0`. -/
lemma ofLiteratureT_eq_ofLiteratureT_iff {f g : ℝ → ℝ} :
    ofLiteratureT f = ofLiteratureT g ↔ EqOn f g (Iic 0) := by
  refine ⟨fun h t ht => ?_, fun h => funext fun q => h (neg_nonpos.mpr q.2)⟩
  have h' := congrFun h (-t).toNNReal
  rwa [ofLiteratureT_toNNReal f (neg_nonneg.mpr ht), ofLiteratureT_toNNReal g (neg_nonneg.mpr ht),
    neg_neg] at h'

open scoped Pointwise in
/-- The slope in `Q²` at the origin is minus the slope in `t`: `ofLiteratureT f`, read on `Q² ≥ 0`,
has right derivative `f'` at `0` exactly when `f` has left derivative `-f'` at `0`. -/
theorem hasDerivWithinAt_ofLiteratureT_iff {f : ℝ → ℝ} {f' : ℝ} :
    HasDerivWithinAt (fun q : ℝ => ofLiteratureT f q.toNNReal) f' (Ici 0) 0 ↔
      HasDerivWithinAt f (-f') (Iic 0) 0 := by
  rw [(Filter.eventuallyEq_of_mem self_mem_nhdsWithin (eqOn_ofLiteratureT_toNNReal f)
    ).hasDerivWithinAt_iff_of_mem (by simp)]
  -- `x ↦ f (-x)` is `f` composed with multiplication by `-1`
  simpa [neg_one_mul, MulAction.one_smul] using
    hasDerivWithinAt_comp_mul_left_smul_iff (c := (-1 : ℝ)) (f := f) (f' := -f') (s := Ici 0)
      (x := 0)

/-- The slope in `Q²` at the origin is minus the slope in `t` at the origin. -/
theorem derivWithin_ofLiteratureT (f : ℝ → ℝ) :
    derivWithin (fun q : ℝ => ofLiteratureT f q.toNNReal) (Ici 0) 0 =
      -derivWithin f (Iic 0) 0 := by
  rw [derivWithin_congr (eqOn_ofLiteratureT_toNNReal f) (by simp), derivWithin_comp_neg,
    neg_zero, Set.neg_Ici, neg_zero]

/-- `∫_0^∞ dQ²` of the translated function is `∫_{-∞}^0 dt` of the original. -/
theorem setIntegral_ofLiteratureT (f : ℝ → ℝ) :
    ∫ q in Ioi (0 : ℝ), ofLiteratureT f q.toNNReal = ∫ t in Iic (0 : ℝ), f t := by
  rw [setIntegral_congr_fun measurableSet_Ioi
    (fun q (hq : q ∈ Ioi 0) => ofLiteratureT_toNNReal f (le_of_lt hq)), integral_comp_neg_Ioi,
    neg_zero]

end GravitationalFormFactors
end Hadron
end Particles
end EpsilonEridani
