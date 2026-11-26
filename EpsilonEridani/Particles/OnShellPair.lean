/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.Relativity.Tensors.RealTensor.Vector.MinkowskiProductExtensions

/-!
# Two momenta on a common mass shell

`OnShellPair d M` is a pair of momenta `p`, `p'` on the mass shell `⟪p, p⟫ₘ = ⟪p', p'⟫ₘ = M²` in
`d + 1`-dimensional Minkowski space: the incoming and outgoing momenta of an elastic transition
`h(p) → h(p')` of a particle of mass `M`. It is the common base of the off-forward kinematics
`EpsilonEridani.Particles.Parton.GPD.OffForwardKinematics` of generalized parton distributions,
which adds a light-like direction and positive plus-momenta, and of the elastic kinematics
`EpsilonEridani.Particles.Hadron.GravitationalFormFactors.ElasticKinematics` of gravitational
form factors, which adds positive energies.

The derived vectors are the average momentum `P = (p + p') / 2` (`avgMomentum`) and the momentum
transfer `Δ = p' - p` (`delta`), with the invariant `t = Δ²` (`tMom`). Every Minkowski pairing
among `p`, `p'`, `P`, `Δ` is a function of `M²` and `t`: `P · Δ = 0`, `P² = M² - t / 4`,
`p · p' = M² - t / 2`, `p · Δ = -t / 2`, `p' · Δ = t / 2` and `P · p = P · p' = M² - t / 4`.
They are the identities for two vectors of equal Minkowski square of
`EpsilonEridani.Relativity.Tensors.RealTensor.Vector.MinkowskiProductExtensions`. Pairings are
stated with the arguments in the order `p`, `p'`, `P`, `Δ`; the other order follows from
`Lorentz.Vector.minkowskiProduct_symm`, except for `P · Δ = 0`, which is stated in both orders.

The spatial part of `P` is the average of those of `p` and `p'` (`spatialPart_avgMomentum_eq`),
and `t` is invariant under Lorentz transformations of the pair (`tMom_eq_of_smul`).

## References

* M. Diehl, *Generalized parton distributions*, Phys. Rept. **388** (2003) 41
  (arXiv:hep-ph/0307382), §3.
-/

public section

noncomputable section

namespace EpsilonEridani
namespace Particles

open Lorentz Lorentz.Vector
open scoped InnerProductSpace

/-- Two momenta `p`, `p'` on the mass shell of a particle of mass `M` in `d + 1`-dimensional
Minkowski space, the incoming and outgoing momenta of an elastic transition `h(p) → h(p')`. -/
@[ext]
structure OnShellPair (d : ℕ) (M : ℝ) where
  /-- The incoming momentum. -/
  p : Vector d
  /-- The outgoing momentum. -/
  pPrime : Vector d
  /-- The incoming momentum is on the mass shell. -/
  minkowskiProduct_p_self : ⟪p, p⟫ₘ = M ^ 2
  /-- The outgoing momentum is on the mass shell. -/
  minkowskiProduct_pPrime_self : ⟪pPrime, pPrime⟫ₘ = M ^ 2

namespace OnShellPair

attribute [simp] minkowskiProduct_p_self minkowskiProduct_pPrime_self

variable {d : ℕ} {M : ℝ} (K : OnShellPair d M)

/-- The average momentum `P = (p + p') / 2`. -/
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

/-- The two momenta have the same Minkowski square. -/
lemma minkowskiProduct_p_self_eq_minkowskiProduct_pPrime_self :
    ⟪K.p, K.p⟫ₘ = ⟪K.pPrime, K.pPrime⟫ₘ := by
  rw [K.minkowskiProduct_p_self, K.minkowskiProduct_pPrime_self]

/-- The product of the two momenta is `p · p' = M² - t / 2`. -/
lemma minkowskiProduct_p_pPrime_eq : ⟪K.p, K.pPrime⟫ₘ = M ^ 2 - K.tMom / 2 := by
  rw [tMom_def, delta_def]
  exact minkowskiProduct_eq_of_minkowskiProduct_self_eq K.minkowskiProduct_p_self
    K.minkowskiProduct_pPrime_self

/-- For an elastic transition the average momentum is orthogonal to the transfer, `P · Δ = 0`. -/
@[simp]
lemma minkowskiProduct_avgMomentum_delta_eq_zero : ⟪K.avgMomentum, K.delta⟫ₘ = 0 := by
  rw [avgMomentum_def, delta_def, map_smul, _root_.smul_apply, minkowskiProduct_add_sub_eq,
    K.minkowskiProduct_p_self_eq_minkowskiProduct_pPrime_self, sub_self, _root_.smul_zero]

/-- For an elastic transition the transfer is orthogonal to the average momentum, `Δ · P = 0`. -/
@[simp]
lemma minkowskiProduct_delta_avgMomentum_eq_zero : ⟪K.delta, K.avgMomentum⟫ₘ = 0 := by
  rw [minkowskiProduct_symm, minkowskiProduct_avgMomentum_delta_eq_zero]

/-- The invariant mass squared of the average momentum, `P² = M² - t / 4`. -/
@[simp]
lemma minkowskiProduct_avgMomentum_self_eq :
    ⟪K.avgMomentum, K.avgMomentum⟫ₘ = M ^ 2 - K.tMom / 4 := by
  rw [avgMomentum_def, minkowskiProduct_smul_self,
    minkowskiProduct_add_self_eq_of_minkowskiProduct_self_eq K.minkowskiProduct_p_self
      K.minkowskiProduct_pPrime_self, tMom_def, delta_def]
  ring

/-- The incoming momentum paired with the transfer is `p · Δ = -t / 2`. -/
lemma minkowskiProduct_p_delta_eq : ⟪K.p, K.delta⟫ₘ = -K.tMom / 2 := by
  rw [tMom_def, delta_def]
  exact minkowskiProduct_sub_right_eq_neg_minkowskiProduct_self_div_two
    K.minkowskiProduct_p_self_eq_minkowskiProduct_pPrime_self

/-- The outgoing momentum paired with the transfer is `p' · Δ = t / 2`. -/
lemma minkowskiProduct_pPrime_delta_eq : ⟪K.pPrime, K.delta⟫ₘ = K.tMom / 2 := by
  rw [tMom_def, delta_def, minkowskiProduct_symm]
  exact minkowskiProduct_sub_left_eq_minkowskiProduct_self_div_two
    K.minkowskiProduct_p_self_eq_minkowskiProduct_pPrime_self

/-- The average momentum paired with the incoming momentum is `P · p = M² - t / 4`. -/
lemma minkowskiProduct_avgMomentum_p_eq : ⟪K.avgMomentum, K.p⟫ₘ = M ^ 2 - K.tMom / 4 := by
  simp [K.p_eq_avgMomentum_sub]

/-- The average momentum paired with the outgoing momentum is `P · p' = M² - t / 4`. -/
lemma minkowskiProduct_avgMomentum_pPrime_eq :
    ⟪K.avgMomentum, K.pPrime⟫ₘ = M ^ 2 - K.tMom / 4 := by
  simp [K.pPrime_eq_avgMomentum_add]

/-- The spatial part of the average momentum is the average of the two spatial momenta. -/
lemma spatialPart_avgMomentum_eq :
    K.avgMomentum.spatialPart = (2⁻¹ : ℝ) • (K.p.spatialPart + K.pPrime.spatialPart) := by
  rw [avgMomentum_def, spatialPart_smul, spatialPart_add]

/-! ### Lorentz invariance of the momentum transfer -/

/-- Two pairs related by a Lorentz transformation `Λ`, `p₂ = Λ p₁` and `p₂' = Λ p₁'`, have the
same `t`. -/
lemma tMom_eq_of_smul {K' : OnShellPair d M} {Λ : LorentzGroup d}
    (hp : K'.p = Λ • K.p) (hp' : K'.pPrime = Λ • K.pPrime) : K'.tMom = K.tMom := by
  rw [tMom_def, tMom_def, delta_def, delta_def, hp, hp', ← smul_sub, minkowskiProduct_invariant]

end OnShellPair

end Particles
end EpsilonEridani
