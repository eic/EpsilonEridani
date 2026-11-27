/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import EpsilonEridani.Particles.Parton.TMD.Basic
public import EpsilonEridani.Mathematics.Analysis.Asymptotics.ApproximatesToOrder
/-!

# Kinematic Power Corrections to TMD Factorization

A TMD factorization theorem is an approximation, and the phrase *kinematic power
correction* is a claim about how good it is: the leading-power term reproduces a structure
function up to a remainder suppressed by a power of `λ = q_T / Q`, and a correction is a
term that improves that suppression by one further power. This module states that claim
with the remainder bound explicit, and proves the facts that stop the statement from being
empty.

## A. What is, and is not, formalized here

The anchor papers for this target do something considerably stronger than what is stated
below. arXiv:2510.14496 evaluates the *complete* set of kinematic power corrections to the
leading-power SIDIS TMD factorization theorem, and arXiv:2603.19833 derives the quasi-TMD
factorization theorem with kinematic power corrections to all orders; in both the
corrections are *constructed* out of twist-two TMD distributions, and both emphasise that
the resulting expressions are gauge and frame invariant. None of that construction is
here. This module does not know what a twist-two distribution is, carries no Lorentz frame,
and has no notion of a soft function.

What is here is the *shape* of the resulting statement — an approximation carrying an
explicit remainder bound — together with the TMD interface built on the results that make
a power correction a determination rather than a convention; those results are generic and
live in `EpsilonEridani.Mathematics.Analysis.Asymptotics.ApproximatesToOrder`:

* `EpsilonEridani.ApproximatesToOrder.coeff_unique`: the coefficient of the order-`n`
  correction is fixed by the structure function and the leading-power term. It is not a
  scheme choice. Taking the leading-power term to be zero, a structure function that vanishes
  at leading power is determined at its first nonvanishing order entirely by its kinematic power
  correction; arXiv:2510.14496 reports this situation for SIDIS, where structure functions that
  vanish in the leading-power TMD factorization theorem, the longitudinal-photon contributions
  among them, receive their first prediction from the kinematic power corrections.
* `EpsilonEridani.ApproximatesToOrder.not_succ_of_coeff_ne_zero`: if that
  coefficient is nonzero, the leading-power term on its own is *not* accurate at the next
  order. A correction that could be dropped without changing the accuracy order would not
  be a correction.
* `EpsilonEridani.ApproximatesToOrder.of_add_mul_pow`: the complementary
  fact that the correction is genuinely subleading — adding it does not disturb the accuracy
  the leading-power term already had.
* `monomialKpc` and `monomialKpc_leadingPower_not_approx_succ`: the interface is inhabited
  with a *nonzero* coefficient, so the sharpness statement is not vacuously true.

The remainder bound is `EpsilonEridani.ApproximatesToOrder` in the power-counting ratio
`λ = q_T / Q`. These are statements of real analysis about the `λ → 0⁺` expansion; they are
not statements about QCD. The interface below stays in the TMD namespace because the power
counting it encodes is the TMD power counting, and because `Kpc` is the interface that a future
derivation of a factorization theorem in this library should be asked to produce. A definition
that merely named a correction term without bounding anything would carry none of this content.

## B. Not captured

* The all-orders resummation of kinematic power corrections. Only a single order is
  described; `Kpc` bounds the remainder after one correction, not after a series.
* Frame and gauge invariance of the corrected expression, which both anchors stress.
* The observation of arXiv:2603.19833 that once kinematic power corrections are included
  the TMD evolution factor enters as a convolution with the nonperturbative distribution
  rather than multiplicatively. The Collins-Soper system in
  `EpsilonEridani.Particles.Parton.TMD.CollinsSoper` is multiplicative and is in that respect a
  leading-power statement.
* Any link to the transverse-momentum integrals of `EpsilonEridani.Particles.Parton.TMD.Basic`:
  the structure function here is an abstract function of `λ`, not one built from a `Tmd`.

## C. References

* arXiv:2510.14496, *Kinematic power corrections for TMD factorization theorem of
  semi-inclusive deep-inelastic scattering*.
* arXiv:2603.19833, *Factorization theorem for quasi-TMD distributions with kinematic power
  corrections*.
* R. Boussarie *et al.*, *TMD Handbook*, arXiv:2304.03302.

-/

@[expose] public section

noncomputable section

namespace EpsilonEridani
namespace Particles
namespace Parton
namespace TMD
namespace PowerCorrections

open Filter Topology Asymptotics

/-- The TMD power-counting ratio `λ = q_T / Q`. The power expansion of a TMD factorization
theorem is an expansion in this ratio, and the limit in which the theorem is a theorem is
`λ → 0⁺`. -/
def powerRatio (qT Q : ℝ) : ℝ := qT / Q

/-- The data of a TMD factorization formula at one order in the power counting: a
leading-power term, the coefficient of the kinematic power correction at order `n`, and the
remainder bound that is their joint content.

There is exactly one hypothesis field and it is the bound itself. Nothing here stands in
for physics that has not been done: `leadingPower` is whatever function a factorization
theorem produces, and `remainder` is the claim that adding `coeff * λ ^ n` to it improves
the accuracy by one power of `λ`. -/
structure Kpc (W : ℝ → ℝ) (n : ℕ) where
  /-- The leading-power term of the factorization formula. -/
  leadingPower : ℝ → ℝ
  /-- The coefficient of the order-`n` kinematic power correction. -/
  coeff : ℝ
  /-- The remainder bound: including the correction leaves an error `O(λ ^ (n + 1))`. -/
  remainder : ApproximatesToOrder W (fun lam => leadingPower lam + coeff * lam ^ n) (n + 1)

namespace Kpc

variable {W : ℝ → ℝ} {n : ℕ}

/-- The leading-power term of a `Kpc` is itself accurate to order `n`. -/
lemma leadingPower_approx (K : Kpc W n) : ApproximatesToOrder W K.leadingPower n :=
  K.remainder.of_add_mul_pow

/-- Two power-correction data for the same structure function with the same leading-power
term carry the same coefficient. -/
lemma coeff_eq (K L : Kpc W n) (h : K.leadingPower = L.leadingPower) : K.coeff = L.coeff := by
  refine K.remainder.coeff_unique (Wlp := K.leadingPower) ?_
  rw [h]
  exact L.remainder

/-- A nonzero correction cannot be absorbed into the leading-power term: that term alone is
not accurate to order `n + 1`. -/
lemma leadingPower_not_approx_succ (K : Kpc W n) (hc : K.coeff ≠ 0) :
    ¬ ApproximatesToOrder W K.leadingPower (n + 1) :=
  K.remainder.not_succ_of_coeff_ne_zero hc

end Kpc

/-- A structure function whose leading-power term vanishes and whose order-`n` kinematic
power correction is the whole of it.

This witnesses that `Kpc` is inhabited with a *nonzero* coefficient, so that
`Kpc.leadingPower_not_approx_succ` is not vacuously true. -/
def monomialKpc (n : ℕ) : Kpc (fun lam : ℝ => lam ^ n) n where
  leadingPower := fun _ => 0
  coeff := 1
  remainder :=
    (ApproximatesToOrder.refl (fun lam : ℝ => lam ^ n) (n + 1)).congr_sub fun lam => by ring

/-- **The order gap is real.** `λ ^ n` is not `O(λ ^ (n + 1))` as `λ → 0⁺`, so the vanishing
leading-power term of `monomialKpc` is accurate to order `n` and no further.

Without a statement of this kind the whole interface would be satisfiable by taking every
correction coefficient to be zero. -/
lemma monomialKpc_leadingPower_not_approx_succ (n : ℕ) :
    ¬ ApproximatesToOrder (fun lam : ℝ => lam ^ n) (fun _ => 0) (n + 1) :=
  (monomialKpc n).leadingPower_not_approx_succ one_ne_zero

/-- The power-counting ratio tends to zero from above as the hard scale grows at fixed
transverse momentum. -/
lemma tendsto_powerRatio_atTop {qT : ℝ} (hqT : 0 < qT) :
    Tendsto (fun Q : ℝ => powerRatio qT Q) atTop (𝓝[>] 0) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · have hdiv : Tendsto (fun Q : ℝ => qT / Q) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    exact hdiv
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with Q hQ
    exact div_pos hqT hQ

/-- **Power counting in `λ` is power counting in the hard scale.** An approximation accurate
to order `n` in the power-counting ratio has, at fixed transverse momentum, an error
suppressed by `n` powers of the hard scale as `Q → ∞`.

This is the bridge between the abstract `λ → 0⁺` statement used throughout this module and
the form in which a power correction is quoted in the literature, as a contribution of
relative size `(q_T / Q) ^ n`. -/
lemma isBigO_inv_pow_atTop {W Wapp : ℝ → ℝ} {n : ℕ} (h : ApproximatesToOrder W Wapp n)
    {qT : ℝ} (hqT : 0 < qT) :
    (fun Q : ℝ => W (powerRatio qT Q) - Wapp (powerRatio qT Q)) =O[atTop]
      fun Q : ℝ => (Q ^ n)⁻¹ := by
  have h' : (fun lam : ℝ => W lam - Wapp lam) =O[𝓝[>] 0] fun lam : ℝ => lam ^ n :=
    approximatesToOrder_def.1 h
  have hcomp := h'.comp_tendsto (tendsto_powerRatio_atTop hqT)
  have hconv : (fun Q : ℝ => powerRatio qT Q ^ n) =O[atTop] fun Q : ℝ => (Q ^ n)⁻¹ := by
    refine ((isBigO_refl (fun Q : ℝ => (Q ^ n)⁻¹) atTop).const_mul_left (qT ^ n)).congr_left ?_
    intro Q
    change qT ^ n * (Q ^ n)⁻¹ = (qT / Q) ^ n
    rw [div_pow, div_eq_mul_inv]
  exact hcomp.trans hconv

end PowerCorrections
end TMD
end Parton
end Particles
end EpsilonEridani
