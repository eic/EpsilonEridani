/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.Relativity.Tensors.RealTensor.Vector.MinkowskiProductExtensions
public import Physlib.Relativity.Causality.CausallyFollows
public import Physlib.Relativity.LorentzGroup.Boosts.Generalized
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
  `ℝ≥0`. The constraint `t ≤ 0` (`ElasticKinematics.tMom_nonpos`) is proved from the mass shell
  and positive energy, by the reverse Cauchy–Schwarz inequality `M² ≤ p · p'`, and `t = 0` exactly
  in the forward direction `p = p'` (`ElasticKinematics.tMom_eq_zero_iff`).
* `ElasticKinematics.IsBreitFrame` is the frame in which `P` has no spatial part. In it
  `Δ⁰ = 0`, `p = (E, -Δ/2)`, `p' = (E, Δ/2)` with `E = √(M² + Q²/4)`, and `Q² = |Δ|²` is the
  square of the three-momentum transfer (`ElasticKinematics.IsBreitFrame.coe_qSq`). Every
  transition is brought to its Breit frame by the generalised boost taking the velocity of `P` to
  rest (`ElasticKinematics.exists_isBreitFrame`), and `t` is unchanged by it.
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
* X. Ji, *Off-forward parton distributions*, Phys. Rev. D **55** (1997) 7114
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

/-- The product of the two target momenta is `p · p' = M² - t / 2`. -/
lemma minkowskiProduct_p_pPrime_eq : ⟪K.p, K.pPrime⟫ₘ = T.mass ^ 2 - K.tMom / 2 := by
  have h := minkowskiProduct_sub_self K.pPrime K.p
  rw [← delta_def, ← tMom_def, K.minkowskiProduct_p_self, K.minkowskiProduct_pPrime_self,
    minkowskiProduct_symm K.pPrime K.p] at h
  linarith

/-- For an elastic transition the average momentum is orthogonal to the transfer, `P · Δ = 0`. -/
@[simp]
lemma minkowskiProduct_avgMomentum_delta_eq_zero : ⟪K.avgMomentum, K.delta⟫ₘ = 0 := by
  simp only [avgMomentum_def, delta_def, map_smul, map_add, map_sub, _root_.smul_apply,
    _root_.add_apply, smul_eq_mul, minkowskiProduct_p_self, minkowskiProduct_pPrime_self,
    minkowskiProduct_symm K.pPrime K.p]
  ring

/-- For an elastic transition the transfer is orthogonal to the average momentum, `Δ · P = 0`. -/
@[simp]
lemma minkowskiProduct_delta_avgMomentum_eq_zero : ⟪K.delta, K.avgMomentum⟫ₘ = 0 := by
  rw [minkowskiProduct_symm]
  simp

/-- The invariant mass squared of the average momentum, `P² = M² - t / 4`. -/
@[simp]
lemma minkowskiProduct_avgMomentum_self_eq :
    ⟪K.avgMomentum, K.avgMomentum⟫ₘ = T.mass ^ 2 - K.tMom / 4 := by
  have h := K.minkowskiProduct_p_self
  rw [p_eq_avgMomentum_sub, minkowskiProduct_sub_self, map_smul, smul_eq_mul,
    minkowskiProduct_smul_self, K.minkowskiProduct_avgMomentum_delta_eq_zero] at h
  rw [tMom_def]
  linarith

/-- The incoming momentum lies in the causal future of the origin. -/
lemma causallyFollows_zero_p : causallyFollows 0 K.p :=
  causallyFollows_zero_iff.mpr ⟨K.minkowskiProduct_p_self ▸ sq_nonneg _, K.timeComponent_p_pos.le⟩

/-- The outgoing momentum lies in the causal future of the origin. -/
lemma causallyFollows_zero_pPrime : causallyFollows 0 K.pPrime :=
  causallyFollows_zero_iff.mpr
    ⟨K.minkowskiProduct_pPrime_self ▸ sq_nonneg _, K.timeComponent_pPrime_pos.le⟩

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
  have hunit : ∀ {x y : Vector d} {μ : ℝ}, 0 ≤ μ → ⟪x, x⟫ₘ = T.mass ^ 2 →
      ⟪y, y⟫ₘ = T.mass ^ 2 → y = μ • x → y = x := by
    intro x y μ hμ hx hy hyx
    rw [hyx, minkowskiProduct_smul_self, hx] at hy
    have hμ1 : μ = 1 := by
      have h1 : μ ^ 2 = 1 := by
        have := pow_pos hM 2
        field_simp at hy
        linarith
      nlinarith
    rw [hyx, hμ1, one_smul]
  obtain ⟨μ, hμ, h | h⟩ := (minkowskiProduct_eq_iff_of_causallyFollows K.causallyFollows_zero_p
    K.causallyFollows_zero_pPrime).mp heq
  · exact (hunit hμ K.minkowskiProduct_p_self K.minkowskiProduct_pPrime_self h).symm
  · exact hunit hμ K.minkowskiProduct_pPrime_self K.minkowskiProduct_p_self h

/-- The positive momentum-transfer variable `Q² = -t`, in which the gravitational form factors are
written. -/
def qSq : ℝ≥0 := ⟨-K.tMom, neg_nonneg.mpr K.tMom_nonpos⟩

@[simp]
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

/-- The pairing of either target momentum with the average momentum is at least `M²`. -/
private lemma sq_mass_le_minkowskiProduct_avgMomentum :
    T.mass ^ 2 ≤ ⟪K.avgMomentum, K.p⟫ₘ ∧ T.mass ^ 2 ≤ ⟪K.avgMomentum, K.pPrime⟫ₘ := by
  have h := K.sq_mass_le_minkowskiProduct_p_pPrime
  simp only [avgMomentum_def, map_smul, map_add, _root_.smul_apply, _root_.add_apply,
    smul_eq_mul, minkowskiProduct_p_self, minkowskiProduct_pPrime_self,
    minkowskiProduct_symm K.pPrime K.p]
  constructor <;> linarith

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

/-- The Breit frame is the frame in which the two target three-momenta are opposite. -/
lemma isBreitFrame_iff_spatialPart_pPrime :
    K.IsBreitFrame ↔ K.pPrime.spatialPart = -K.p.spatialPart := by
  rw [IsBreitFrame, avgMomentum_def, eq_neg_iff_add_eq_zero]
  constructor <;> intro h <;> ext i <;> have := congrFun (congrArg (⇑) h) i
  · simp only [apply_smul, apply_add, PiLp.zero_apply] at this
    simp only [PiLp.add_apply, PiLp.zero_apply]
    linarith
  · simp only [PiLp.add_apply, PiLp.zero_apply] at this
    simp only [apply_smul, apply_add, PiLp.zero_apply]
    linarith

namespace IsBreitFrame

variable {K}

/-- In the Breit frame the average momentum has no spatial part. -/
lemma spatialPart_avgMomentum (h : K.IsBreitFrame) : K.avgMomentum.spatialPart = 0 := h

/-- In the Breit frame the energy transfer vanishes, `Δ⁰ = 0`. -/
lemma timeComponent_delta (h : K.IsBreitFrame) : K.delta.timeComponent = 0 := by
  have hPΔ := K.minkowskiProduct_avgMomentum_delta_eq_zero
  rw [minkowskiProduct_eq_timeComponent_spatialPart, h.spatialPart_avgMomentum, inner_zero_left,
    sub_zero] at hPΔ
  exact (mul_eq_zero.mp hPΔ).resolve_left K.timeComponent_avgMomentum_pos.ne'

/-- In the Breit frame `Q²` is the square of the three-momentum transfer, `Q² = |Δ|²`. -/
lemma coe_qSq (h : K.IsBreitFrame) : (K.qSq : ℝ) = ‖K.delta.spatialPart‖ ^ 2 := by
  rw [ElasticKinematics.coe_qSq, tMom_def, minkowskiProduct_self_eq_sq_sub,
    h.timeComponent_delta]
  ring

/-- In the Breit frame the energy of the average momentum is `P⁰ = √(M² + Q² / 4)`. -/
lemma timeComponent_avgMomentum (h : K.IsBreitFrame) :
    K.avgMomentum.timeComponent = √(T.mass ^ 2 + K.qSq / 4) := by
  have hP := K.minkowskiProduct_avgMomentum_self_eq_add_qSq
  rw [minkowskiProduct_self_eq_sq_sub, h.spatialPart_avgMomentum, norm_zero] at hP
  rw [← hP, zero_pow two_ne_zero, sub_zero, Real.sqrt_sq K.timeComponent_avgMomentum_pos.le]

/-- In the Breit frame the incoming energy is `p⁰ = √(M² + Q² / 4)`. -/
lemma timeComponent_p (h : K.IsBreitFrame) :
    K.p.timeComponent = √(T.mass ^ 2 + K.qSq / 4) := by
  rw [← h.timeComponent_avgMomentum]
  conv_lhs => rw [K.p_eq_avgMomentum_sub]
  simp [timeComponent, h.timeComponent_delta]

/-- In the Breit frame the outgoing energy is `p'⁰ = √(M² + Q² / 4)`. -/
lemma timeComponent_pPrime (h : K.IsBreitFrame) :
    K.pPrime.timeComponent = √(T.mass ^ 2 + K.qSq / 4) := by
  rw [← h.timeComponent_avgMomentum]
  conv_lhs => rw [K.pPrime_eq_avgMomentum_add]
  simp [timeComponent, h.timeComponent_delta]

/-- In the Breit frame the incoming three-momentum is `-Δ / 2`. -/
lemma spatialPart_p (h : K.IsBreitFrame) :
    K.p.spatialPart = -((2⁻¹ : ℝ) • K.delta.spatialPart) := by
  have h0 : ∀ i, K.avgMomentum (Sum.inr i) = 0 := fun i => by
    simpa using congrFun (congrArg (⇑) h) i
  ext i
  conv_lhs => rw [K.p_eq_avgMomentum_sub]
  simp [h0]

/-- In the Breit frame the outgoing three-momentum is `Δ / 2`. -/
lemma spatialPart_pPrime (h : K.IsBreitFrame) :
    K.pPrime.spatialPart = (2⁻¹ : ℝ) • K.delta.spatialPart := by
  have h0 : ∀ i, K.avgMomentum (Sum.inr i) = 0 := fun i => by
    simpa using congrFun (congrArg (⇑) h) i
  ext i
  conv_lhs => rw [K.pPrime_eq_avgMomentum_add]
  simp [h0]

end IsBreitFrame

/-- Every elastic transition has a Breit frame: the generalised boost `Λ` taking the velocity
`P / √(P²)` of the average momentum to rest is a restricted Lorentz transformation, and the boosted
momenta `Λ p`, `Λ p'` are again an elastic transition of `T`, in its Breit frame. By
`tMom_eq_of_smul` the boosted transition has the same `t`. -/
theorem exists_isBreitFrame :
    ∃ Λ ∈ LorentzGroup.restricted d, ∃ K' : ElasticKinematics T d,
      K'.p = Λ • K.p ∧ K'.pPrime = Λ • K.pPrime ∧ K'.IsBreitFrame := by
  set P := K.avgMomentum with hPdef
  have hPP := K.minkowskiProduct_avgMomentum_self_pos
  set m := √⟪P, P⟫ₘ with hm
  have hm0 : 0 < m := Real.sqrt_pos.mpr hPP
  -- the velocity of the average momentum
  have hu : m⁻¹ • P ∈ Velocity d := by
    refine Velocity.mem_iff.mpr ⟨?_, ?_⟩
    · rw [minkowskiProduct_smul_self, inv_pow, hm, Real.sq_sqrt hPP.le, inv_mul_cancel₀ hPP.ne']
    · simp only [timeComponent, apply_smul]
      exact mul_pos (inv_pos.mpr hm0) K.timeComponent_avgMomentum_pos
  set Λ := LorentzGroup.generalizedBoost ⟨m⁻¹ • P, hu⟩ 0 with hΛ
  have hΛP : Λ • P = m • (0 : Velocity d).1 := by
    have h := LorentzGroup.generalizedBoost_apply_fst ⟨m⁻¹ • P, hu⟩ 0
    rw [← hΛ, smul_comm] at h
    rw [← h, smul_smul, mul_inv_cancel₀ hm0.ne', one_smul]
  -- the rest velocity has no spatial part, by `‖u.spatialPart‖² = (u⁰)² - 1`
  have hz : (0 : Velocity d).1.spatialPart = 0 := by
    have h := Velocity.norm_spatialPart_sq_eq (0 : Velocity d)
    have h1 : (0 : Velocity d).1 (Sum.inl 0) = 1 := Velocity.zero_timeComponent
    rwa [h1, one_pow, sub_self, sq_eq_zero_iff, norm_eq_zero] at h
  -- pairing with the boosted average momentum reads off `m` times the boosted energy
  have hpair : ∀ x : Vector d, ⟪P, x⟫ₘ = m * (Λ • x).timeComponent := fun x => by
    rw [← minkowskiProduct_invariant P x Λ, hΛP, minkowskiProduct_apply,
      minkowskiProductMap_smul_fst, ← minkowskiProduct_apply,
      minkowskiProduct_eq_timeComponent_spatialPart, Velocity.zero_timeComponent, hz,
      inner_zero_left, one_mul, sub_zero]
  have hpos : ∀ x : Vector d, T.mass ^ 2 ≤ ⟪P, x⟫ₘ → 0 < (Λ • x).timeComponent := by
    intro x hx
    have := hpair x
    have hM := pow_pos T.mass_pos 2
    nlinarith
  obtain ⟨hp, hp'⟩ := K.sq_mass_le_minkowskiProduct_avgMomentum
  let K' : ElasticKinematics T d :=
    { p := Λ • K.p
      pPrime := Λ • K.pPrime
      minkowskiProduct_p_self := by rw [minkowskiProduct_invariant, K.minkowskiProduct_p_self]
      minkowskiProduct_pPrime_self := by
        rw [minkowskiProduct_invariant, K.minkowskiProduct_pPrime_self]
      timeComponent_p_pos := hpos _ hp
      timeComponent_pPrime_pos := hpos _ hp' }
  have hav : K'.avgMomentum = Λ • P := by
    rw [avgMomentum_def, hPdef, avgMomentum_def, smul_comm, Lorentz.Vector.smul_add]
  refine ⟨Λ, LorentzGroup.generalizedBoost_mem_restricted _ _, K', rfl, rfl, ?_⟩
  rw [IsBreitFrame, hav, hΛP]
  ext i
  simpa using Or.inr (congrArg (· i) hz)

end ElasticKinematics

/-! ### The literature dictionary `t ↦ Q² = -t` -/

/-- The dictionary from the literature's variable `t ≤ 0` to `Q² = -t ≥ 0`: a function `f` of `t`
becomes the function `Q² ↦ f (-Q²)` on `ℝ≥0`. Only the values of `f` on `t ≤ 0` enter
(`ofLiteratureT_eq_ofLiteratureT_iff`). -/
def ofLiteratureT (f : ℝ → ℝ) : ℝ≥0 → ℝ := fun q => f (-(q : ℝ))

@[simp]
lemma ofLiteratureT_apply (f : ℝ → ℝ) (q : ℝ≥0) : ofLiteratureT f q = f (-(q : ℝ)) := (rfl)

/-- On an elastic transition, the translated function evaluated at `Q²` is the original evaluated
at `t`. This is deliberately not a `simp` lemma: the rewrite is already performed by
`ofLiteratureT_apply`, `ElasticKinematics.coe_qSq` and `neg_neg`. -/
lemma ofLiteratureT_qSq {T : Target} {d : ℕ} (f : ℝ → ℝ) (K : ElasticKinematics T d) :
    ofLiteratureT f K.qSq = f K.tMom := by
  simp

/-- On `Q² ≥ 0` read as a real number, the translated function is `Q² ↦ f (-Q²)`. -/
lemma ofLiteratureT_toNNReal (f : ℝ → ℝ) {q : ℝ} (hq : 0 ≤ q) :
    ofLiteratureT f q.toNNReal = f (-q) := by
  rw [ofLiteratureT_apply, Real.coe_toNNReal q hq]

/-- Two functions of `t` give the same function of `Q²` exactly when they agree on `t ≤ 0`. -/
lemma ofLiteratureT_eq_ofLiteratureT_iff {f g : ℝ → ℝ} :
    ofLiteratureT f = ofLiteratureT g ↔ EqOn f g (Iic 0) := by
  refine ⟨fun h t ht => ?_, fun h => funext fun q => h (neg_nonpos.mpr q.2)⟩
  have h' := congrFun h (-t).toNNReal
  rwa [ofLiteratureT_toNNReal f (neg_nonneg.mpr ht), ofLiteratureT_toNNReal g (neg_nonneg.mpr ht),
    neg_neg] at h'

/-- The slope in `Q²` at the origin is minus the slope in `t`: `ofLiteratureT f`, read on `Q² ≥ 0`,
has right derivative `f'` at `0` exactly when `f` has left derivative `-f'` at `0`. -/
theorem hasDerivWithinAt_ofLiteratureT_iff {f : ℝ → ℝ} {f' : ℝ} :
    HasDerivWithinAt (fun q : ℝ => ofLiteratureT f q.toNNReal) f' (Ici 0) 0 ↔
      HasDerivWithinAt f (-f') (Iic 0) 0 := by
  have hEq : EqOn (fun q : ℝ => ofLiteratureT f q.toNNReal) (fun q => f (-q)) (Ici 0) :=
    fun q hq => ofLiteratureT_toNNReal f hq
  rw [(Filter.eventuallyEq_of_mem self_mem_nhdsWithin hEq).hasDerivWithinAt_iff_of_mem
    (by simp)]
  -- composing with `x ↦ -x` negates the derivative and reflects the set
  have key : ∀ {g : ℝ → ℝ} {g' : ℝ} {s : Set ℝ}, HasDerivWithinAt g g' (-s) 0 →
      HasDerivWithinAt (fun x => g (-x)) (-g') s 0 := fun {g g' s} h => by
    have := HasDerivWithinAt.scomp (0 : ℝ) (by simpa using h)
      ((hasDerivAt_neg (0 : ℝ)).hasDerivWithinAt (s := s)) (fun x hx => by simpa using hx)
    simpa [Function.comp_def] using this
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simpa using key (g := fun x => f (-x)) (s := Iic 0) (by simpa using h)
  · have h' := key (g := f) (s := Ici 0) (by simpa using h)
    rwa [neg_neg] at h'

/-- The slope in `Q²` at the origin is minus the slope in `t` at the origin. -/
theorem derivWithin_ofLiteratureT (f : ℝ → ℝ) :
    derivWithin (fun q : ℝ => ofLiteratureT f q.toNNReal) (Ici 0) 0 =
      -derivWithin f (Iic 0) 0 := by
  have hEq : EqOn (fun q : ℝ => ofLiteratureT f q.toNNReal) (fun q => f (-q)) (Ici 0) :=
    fun q hq => ofLiteratureT_toNNReal f hq
  rw [derivWithin_congr hEq (by simp), derivWithin_comp_neg, neg_zero, Set.neg_Ici, neg_zero]

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
