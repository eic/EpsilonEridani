/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import EpsilonEridani.QFT.Factorization.DIS.LO
public import EpsilonEridani.QFT.Scattering.DIS.Tensors.Basic
/-!

# The longitudinal structure function and the Callan-Gross relation

This module defines the longitudinal structure function `F_L := F₂ - 2 x F₁` and its
target-mass-exact form `F_L^{exact} := (1 + 4 M² x² / Q²) F₂ - 2 x F₁`, identifies the latter
with the absorption of a longitudinally polarized virtual photon, and proves the Callan-Gross
relation `F₂ = 2 x F₁` for spin-1/2 partons, together with its spin-0 counterpart `F₁ = 0`.

## Scope: leading order in `α_s`, leading twist

Everything proved here is a **leading-order, leading-twist** statement, and both restrictions
are visible in the hypotheses rather than buried in prose:

* *Leading order in `α_s`.* The structure functions are taken to be represented by the
  leading-order factorization interface `Factorization.DIS.IsLOFactorized`, with hard kernels
  built from the **elastic** photon-parton vertex and nothing else. Beyond leading order
  `F_L ≠ 0`: the gluon-emission and gluon-Compton graphs give
  `F_L = (α_s/2π) x² ∫ (dz/z³) [(8/3) F₂(z) + 4 Σ e_i² (1 - x/z) z g(z)] + O(α_s²)`
  (Altarelli-Martinelli; see Dokshitzer, *Sov. Phys. JETP* **46** (1977) 641). Nothing in this
  module bounds that correction.
* *Leading twist.* `Longitudinal.isCallanGross_iff_apply_pTransverse_eq_zero` carries the
  explicit hypothesis `g p p = 0`, i.e. the target-mass term is dropped. The exact identity
  `Longitudinal.two_xBj_mul_Q2_mul_apply_pTransverse` keeps that term, and exhibits it as the
  familiar `4 x² M² / Q²` target-mass correction: `F_L` is the *leading-twist* name for the
  longitudinal combination, and `FLExact` is the name that keeps the target mass. Genuine
  twist-4 corrections are a separate matter and are not modelled here at all.

## What the relation is a statement about

`F_L` is not an arbitrary linear combination: it measures the absorption of a **longitudinally
polarized** virtual photon. The longitudinal polarization direction is, up to normalization,
the transverse hadron momentum `p_T` of `Tensors.Hadronic` — the unique direction in the `p`-`q`
plane that is orthogonal to `q`. Contracting an `F₁`/`F₂`-decomposed hadronic tensor into that
direction gives, exactly,

  `2 x Q² · W(p_T, p_T) = (p_T · p_T) · (Q² F_L + 4 x² M² F₂)`,

so at leading twist `W(p_T, p_T) = 0` and `F_L = 0` are the same statement
(`isCallanGross_iff_apply_pTransverse_eq_zero`). At finite target mass the target-mass term is
absorbed into `F_L^{exact}`:

  `2 x W(p_T, p_T) = (p_T · p_T) F_L^{exact}`,  `p_T · p_T = ((p·q)² / Q²) (1 + 4 x² M² / Q²)`

(`two_xBj_mul_apply_pTransverse`, `pTransverse_self_eq`). The factor `1 + 4 x² M² / Q²` is the
amount by which the longitudinal direction is longer than its massless value, and since
`p_T · p_T > 0` in the physical region, `F_L^{exact}` has the sign and the zeros of the
longitudinal absorption (`FLExact_nonneg_iff_apply_pTransverse_nonneg`,
`FLExact_eq_zero_iff_apply_pTransverse_eq_zero`), whereas `F_L` has them in general only at
`M = 0`.

## Where the factor `2 x` comes from

The relation is a statement about *dynamics*, so the two hard kernels are fixed **independently**
from the elastic photon-parton tensor and the factor `2 x` is derived, not assumed. An
`ElasticChannel` carries the two coefficients of the elastic partonic tensor in the transverse
basis `{-g + q ⊗ q / q², p_T ⊗ p_T}` of `Tensors.Hadronic`, as functions of the light-cone
fraction `z` of the struck parton:

* massless **spin-1/2** parton, from `(1/2) Tr[k̸ γ^μ (k̸ + q̸) γ^ν]
  = 2[k^μ (k+q)^ν + (k+q)^μ k^ν - g^{μν} (k·q)]` at `k = z p`, hence `k_T = z p_T`:
  transverse coefficient `2 z (p·q)`, `p_T ⊗ p_T` coefficient `4 z²`;
* **spin-0** parton, from the scalar-QED vertex `(2k+q)^μ`, giving
  `T^{μν} = (2k+q)^μ (2k+q)^ν = 4 k_T^μ k_T^ν + (q ⊗ q term removed by conservation)`:
  transverse coefficient `0`, `p_T ⊗ p_T` coefficient `4 z²`.

The two spins therefore share the *same* `p_T ⊗ p_T` coefficient and differ only in the
transverse one. From those inputs the longitudinal hard kernel of the spin-1/2 channel is

  `hardF₂ - 2 x hardF₁ = 4 e_i² (p·q) z (z - x) · weight(x, z, Q²)`
  (`spinHalfChannel_longitudinalKernel`),

which vanishes precisely because the elastic channel is on shell, `z = x`. That single
arithmetic fact is the Callan-Gross relation; for the scalar channel `hardF₁ = 0` identically
and `F_L = F₂`, so the relation fails maximally. The contrast is what shows the relation is
dynamics and not a kinematic identity.

Normalization convention: the `F₂` slot of `Tensors.Hadronic.IsF1F2Decomposition` is the
literature's `F₂/(p·q)`, so the physical `F₂` is recovered by `structureF2`. With the physical
elastic weight `weight(x, z, Q²) = δ(z - x) / (4 z (p·q))` the kernels of `spinHalfChannel`
reproduce the textbook parton model, `F₁ = (1/2) Σ e_i² q_i(x)` and `F₂ = x Σ e_i² q_i(x)`.
The `x` convention is that of `Kinematics.DisKinematics.xBj`.

## Status and limitations

`Factorization.Convolution.convolveAt` is a Bochner integral of a **function** kernel against
Lebesgue measure on `[0,1]`, so the parton-model delta `δ(z - x)` is not representable in it.
`IsOnShell` therefore records the one distributional property the derivation uses,
`(z - x) δ(z - x) = 0`, as a pointwise identity on the weight. That identity is satisfied by
the delta, but a Lebesgue *function* satisfying it vanishes off the diagonal and hence almost
everywhere, so every function-valued instance of `callan_gross` has `F₁ = F₂ = 0`. The content
that survives for an arbitrary weight is carried by the two remainder results, which assume no
on-shell condition at all: `spinHalfChannel_longitudinalKernel` (pointwise, unconditional) and
`loStructureFunction_longitudinalKernel` (integrated, needing only integrability). Making
`callan_gross` itself non-degenerate requires generalizing `convolveAt` to a measure-valued
kernel — `Measure.dirac x` is then the physical choice — which is a change to
`Factorization/Convolution/Basic.lean` and is deliberately not made here.

## References

* C. G. Callan and D. J. Gross, *High-energy electroproduction and the constitution of the
  electric current*, Phys. Rev. Lett. **22** (1969) 156.
* Yu. L. Dokshitzer, *Calculation of the structure functions for deep inelastic scattering and
  e⁺e⁻ annihilation by perturbation theory in quantum chromodynamics*,
  Sov. Phys. JETP **46** (1977) 641.
* J. Collins, *Foundations of Perturbative QCD*, Cambridge University Press (2011).
* R. Devenish and A. Cooper-Sarkar, *Deep Inelastic Scattering*, Oxford University Press
  (2004).

-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace EpsilonEridani
namespace QFT
namespace Scattering
namespace DIS
namespace Tensors
namespace Longitudinal

open Hadronic
open Kinematics (Bilin DisKinematics)
open EpsilonEridani.QFT.Factorization.DIS (HardKernel loChannel loStructureFunction IsLOFactorized)
open EpsilonEridani.QFT.Factorization.Convolution
  (convolveAt integrand convolveAt_eq_zero_of_integrand_zero)
open EpsilonEridani.Particles.Parton.PDF (Pdf)

variable {V : Type} [AddCommGroup V] [Module ℝ V]

/-!

## The longitudinal structure function

-/

/-- The longitudinal structure function `F_L := F₂ - 2 x F₁`, as a function of the Bjorken
variable and the two transverse structure functions. -/
def FL (x F1 F2 : ℝ) : ℝ := F2 - 2 * x * F1

/-- The Callan-Gross relation, as a predicate on a pair of structure functions at a given
value of the Bjorken variable: the longitudinal structure function vanishes. -/
def IsCallanGross (x F1 F2 : ℝ) : Prop := FL x F1 F2 = 0

/-- The Callan-Gross predicate unfolded: `F_L = 0` is the same as `F₂ = 2 x F₁`. -/
lemma isCallanGross_iff (x F1 F2 : ℝ) : IsCallanGross x F1 F2 ↔ F2 = 2 * x * F1 := by
  unfold IsCallanGross FL
  constructor
  · intro h
    linarith
  · intro h
    linarith

/-- The target-mass-exact longitudinal structure function
`F_L^{exact} := (1 + 4 M² x² / Q²) F₂ - 2 x F₁`, as a function of the target mass `M`, the Bjorken
variable `x`, the hard scale `Q²` and the two transverse structure functions. This, and not
the massless `FL`, is the combination that measures longitudinal absorption at finite target
mass (`two_xBj_mul_apply_pTransverse`); the two agree at `M = 0` (`FLExact_zero`). -/
def FLExact (M x Q2 F1 F2 : ℝ) : ℝ := (1 + 4 * M ^ 2 * x ^ 2 / Q2) * F2 - 2 * x * F1

/-- The defining formula of the target-mass-exact longitudinal structure function. -/
lemma FLExact_def (M x Q2 F1 F2 : ℝ) :
    FLExact M x Q2 F1 F2 = (1 + 4 * M ^ 2 * x ^ 2 / Q2) * F2 - 2 * x * F1 := rfl

/-- At zero target mass the target-mass-exact longitudinal structure function is the massless
one. -/
@[simp] lemma FLExact_zero (x Q2 F1 F2 : ℝ) : FLExact 0 x Q2 F1 F2 = FL x F1 F2 := by
  unfold FLExact FL
  ring

/-- The two longitudinal structure functions differ by the target-mass term
`4 M² x² F₂ / Q²`. -/
lemma FLExact_eq_FL_add (M x Q2 F1 F2 : ℝ) :
    FLExact M x Q2 F1 F2 = FL x F1 F2 + 4 * M ^ 2 * x ^ 2 / Q2 * F2 := by
  unfold FLExact FL
  ring

/-- The target-mass-exact longitudinal structure function cleared of its denominator:
`Q² F_L^{exact} = Q² F_L + 4 x² M² F₂`. -/
lemma Q2_mul_FLExact (M x F1 F2 : ℝ) {Q2 : ℝ} (hQ2 : Q2 ≠ 0) :
    Q2 * FLExact M x Q2 F1 F2 = Q2 * FL x F1 F2 + 4 * x ^ 2 * M ^ 2 * F2 := by
  unfold FLExact FL
  field_simp
  ring

/-- The physical second structure function. `Tensors.Hadronic.IsF1F2Decomposition` carries
`F₂/(p·q)` in its last slot, so the physical `F₂` is that coefficient times `p·q`. -/
def structureF2 (g : Bilin V) (K : DisKinematics V) (F2c : ℝ) : ℝ := g K.p K.q * F2c

/-!

## `F_L` as the longitudinal photon absorption

The longitudinal polarization direction of the virtual photon is the transverse hadron
momentum `p_T = p - (p·q/q²) q`: it lies in the `p`-`q` plane and is `g`-orthogonal to `q`.
The results below contract a decomposed hadronic tensor into that direction.

-/

/-- The transverse projector `-g + q ⊗ q / q²` acts as minus the identity on the transverse
hadron momentum, because `p_T` is orthogonal to `q`. -/
lemma transverseMetric_pTransverse_self (g : Bilin V) (K : DisKinematics V)
    (hSymm : g.IsSymm) (hQ2 : g K.q K.q ≠ 0) :
    transverseMetric g K (pTransverse g K) (pTransverse g K)
      = - g (pTransverse g K) (pTransverse g K) := by
  have hqpT : g K.q (pTransverse g K) = 0 := by
    rw [hSymm.eq K.q (pTransverse g K)]
    exact pTransverse_orthogonal_q g K hQ2
  rw [transverseMetric_apply, hqpT]
  ring

/-- The `g`-norm of the transverse hadron momentum, in division-free form:
`q² (p_T · p_T) = q² M² - (p·q)²`. -/
lemma q_sq_mul_pTransverse_self (g : Bilin V) (K : DisKinematics V)
    (hSymm : g.IsSymm) (hQ2 : g K.q K.q ≠ 0) :
    g K.q K.q * g (pTransverse g K) (pTransverse g K)
      = g K.q K.q * g K.p K.p - g K.p K.q ^ 2 := by
  have hqpT : g K.q (pTransverse g K) = 0 := by
    rw [hSymm.eq K.q (pTransverse g K)]
    exact pTransverse_orthogonal_q g K hQ2
  have hppT : g K.p (pTransverse g K)
      = g K.p K.p - g K.p K.q / g K.q K.q * g K.p K.q := by
    simp only [pTransverse, map_sub, map_smul, smul_eq_mul]
  have hc : g K.p K.q / g K.q K.q * g K.q K.q = g K.p K.q := by
    rw [div_eq_mul_inv, mul_assoc, inv_mul_cancel₀ hQ2, mul_one]
  have hT : g (pTransverse g K) (pTransverse g K)
      = g K.p K.p - g K.p K.q / g K.q K.q * g K.p K.q := by
    rw [pTransverse_pairing, hppT, hqpT]
    ring
  rw [hT]
  linear_combination (- g K.p K.q) * hc

/-- The same statement written with the hard scale: `Q² (p_T · p_T) = Q² M² + (p·q)²`. In the
`+---` convention of `Kinematics` this is positive for a spacelike probe. -/
lemma Q2_mul_pTransverse_self (g : Bilin V) (K : DisKinematics V)
    (hSymm : g.IsSymm) (hQ2 : g K.q K.q ≠ 0) :
    K.Q2 g * g (pTransverse g K) (pTransverse g K)
      = K.Q2 g * g K.p K.p + g K.p K.q ^ 2 := by
  have h := q_sq_mul_pTransverse_self g K hSymm hQ2
  rw [q_sq_eq_neg_Q2 g K] at h
  linear_combination -h

/-- The Bjorken variable cleared of its denominator: `2 x (p·q) = Q²`. -/
lemma two_xBj_mul_pq (g : Bilin V) (K : DisKinematics V) (hpq : g K.p K.q ≠ 0) :
    2 * K.xBj g * g K.p K.q = K.Q2 g := by
  have h2P : (2 : ℝ) * g K.p K.q ≠ 0 := mul_ne_zero (by norm_num) hpq
  have hcancel : K.Q2 g / (2 * g K.p K.q) * (2 * g K.p K.q) = K.Q2 g := by
    rw [div_eq_mul_inv, mul_assoc, inv_mul_cancel₀ h2P, mul_one]
  unfold Kinematics.DisKinematics.xBj
  linear_combination hcancel

/-- Value of a decomposed hadronic tensor on the longitudinal direction. -/
lemma apply_pTransverse_self (g : Bilin V) (K : DisKinematics V) (W : Bilin V)
    (hSymm : g.IsSymm) (hQ2 : g K.q K.q ≠ 0) (F1 F2c : ℝ)
    (hW : IsF1F2Decomposition g K W F1 F2c) :
    W (pTransverse g K) (pTransverse g K)
      = g (pTransverse g K) (pTransverse g K)
        * (F2c * g (pTransverse g K) (pTransverse g K) - F1) := by
  rw [hW (pTransverse g K) (pTransverse g K),
    transverseMetric_pTransverse_self g K hSymm hQ2]
  ring

/-- **The longitudinal projection, exactly.** Contracting a decomposed hadronic tensor into
the longitudinal polarization direction `p_T` gives the longitudinal structure function
together with its exact target-mass term:

  `2 x Q² W(p_T, p_T) = (p_T · p_T) (Q² F_L + 4 x² M² F₂)`.

No leading-twist approximation has been made; `M² = g p p` is the exact target mass squared.
This is the identity that makes `FL` a physical quantity rather than a name for a
combination. -/
theorem two_xBj_mul_Q2_mul_apply_pTransverse (g : Bilin V) (K : DisKinematics V) (W : Bilin V)
    (hSymm : g.IsSymm) (hQ2 : g K.q K.q ≠ 0) (hpq : g K.p K.q ≠ 0) (F1 F2c : ℝ)
    (hW : IsF1F2Decomposition g K W F1 F2c) :
    2 * K.xBj g * K.Q2 g * W (pTransverse g K) (pTransverse g K)
      = g (pTransverse g K) (pTransverse g K)
        * (K.Q2 g * FL (K.xBj g) F1 (structureF2 g K F2c)
          + 4 * K.xBj g ^ 2 * g K.p K.p * structureF2 g K F2c) := by
  have hdec := apply_pTransverse_self g K W hSymm hQ2 F1 F2c hW
  have h1 := Q2_mul_pTransverse_self g K hSymm hQ2
  have h2 := two_xBj_mul_pq g K hpq
  rw [hdec]
  unfold FL structureF2
  linear_combination
    (2 * K.xBj g * F2c * g (pTransverse g K) (pTransverse g K)) * h1
      + (g (pTransverse g K) (pTransverse g K) * F2c
        * (g K.p K.q - 2 * K.xBj g * g K.p K.p)) * h2

/-!

### The target-mass-exact longitudinal projection

-/

/-- **The length of the longitudinal direction.** The `g`-norm of the transverse hadron
momentum is its massless value `(p·q)² / Q²` times the target-mass factor
`1 + 4 M² x² / Q²`, with `M² = g p p`. The same factor is the one by which `FLExact` weights
`F₂` relative to `FL`. -/
theorem pTransverse_self_eq (g : Bilin V) (K : DisKinematics V) (hSymm : g.IsSymm)
    (hQ2 : g K.q K.q ≠ 0) (hpq : g K.p K.q ≠ 0) :
    g (pTransverse g K) (pTransverse g K)
      = g K.p K.q ^ 2 / K.Q2 g * (1 + 4 * g K.p K.p * K.xBj g ^ 2 / K.Q2 g) := by
  have hQne : K.Q2 g ≠ 0 := (q_sq_ne_zero_iff g K).mp hQ2
  have h1 := Q2_mul_pTransverse_self g K hSymm hQ2
  have h2 := two_xBj_mul_pq g K hpq
  field_simp
  linear_combination K.Q2 g * h1 - g K.p K.p * (2 * K.xBj g * g K.p K.q + K.Q2 g) * h2

/-- For a spacelike probe and a target of non-negative mass squared the longitudinal direction
has positive `g`-norm. -/
lemma pTransverse_self_pos (g : Bilin V) (K : DisKinematics V) (hSymm : g.IsSymm)
    (hQ2 : 0 < K.Q2 g) (hpq : g K.p K.q ≠ 0) (hM : 0 ≤ g K.p K.p) :
    0 < g (pTransverse g K) (pTransverse g K) := by
  have h1 := Q2_mul_pTransverse_self g K hSymm ((q_sq_ne_zero_iff g K).mpr hQ2.ne')
  have h : 0 < K.Q2 g * g (pTransverse g K) (pTransverse g K) := by
    rw [h1]
    positivity
  exact pos_of_mul_pos_right h hQ2.le

/-- **`FLExact` is the longitudinal absorption.** Contracting a decomposed hadronic tensor into
the longitudinal polarization direction `p_T` gives the target-mass-exact longitudinal
structure function, with no target-mass term left over:

  `2 x W(p_T, p_T) = (p_T · p_T) F_L^{exact}`,

where `M² = g p p`. The factor `p_T · p_T` is evaluated by `pTransverse_self_eq` and is
positive in the physical region (`pTransverse_self_pos`). -/
theorem two_xBj_mul_apply_pTransverse (g : Bilin V) (K : DisKinematics V) (W : Bilin V)
    (hSymm : g.IsSymm) (hQ2 : g K.q K.q ≠ 0) (hpq : g K.p K.q ≠ 0) {M : ℝ}
    (hM : g K.p K.p = M ^ 2) (F1 F2c : ℝ) (hW : IsF1F2Decomposition g K W F1 F2c) :
    2 * K.xBj g * W (pTransverse g K) (pTransverse g K)
      = g (pTransverse g K) (pTransverse g K)
        * FLExact M (K.xBj g) (K.Q2 g) F1 (structureF2 g K F2c) := by
  have hQne : K.Q2 g ≠ 0 := (q_sq_ne_zero_iff g K).mp hQ2
  have hmain := two_xBj_mul_Q2_mul_apply_pTransverse g K W hSymm hQ2 hpq F1 F2c hW
  have hE := Q2_mul_FLExact M (K.xBj g) F1 (structureF2 g K F2c) hQne
  rw [hM] at hmain
  apply mul_left_cancel₀ hQne
  linear_combination hmain - g (pTransverse g K) (pTransverse g K) * hE

/-- **`F_L^{exact} = 0` is exactly the vanishing of longitudinal absorption**, at finite target
mass. This is the massive form of `isCallanGross_iff_apply_pTransverse_eq_zero`, which is its
`M = 0` case. -/
theorem FLExact_eq_zero_iff_apply_pTransverse_eq_zero (g : Bilin V) (K : DisKinematics V)
    (W : Bilin V) (hSymm : g.IsSymm) {M : ℝ} (hM : g K.p K.p = M ^ 2) (hx : K.xBj g ≠ 0)
    (hT : g (pTransverse g K) (pTransverse g K) ≠ 0) (F1 F2c : ℝ)
    (hW : IsF1F2Decomposition g K W F1 F2c) :
    FLExact M (K.xBj g) (K.Q2 g) F1 (structureF2 g K F2c) = 0
      ↔ W (pTransverse g K) (pTransverse g K) = 0 := by
  have hpq : g K.p K.q ≠ 0 := by
    intro h
    apply hx
    simp [Kinematics.DisKinematics.xBj, h]
  have hQ2 : g K.q K.q ≠ 0 := by
    intro h
    apply hx
    simp [Kinematics.DisKinematics.xBj, Kinematics.DisKinematics.Q2, h]
  have key := two_xBj_mul_apply_pTransverse g K W hSymm hQ2 hpq hM F1 F2c hW
  constructor
  · intro h
    rw [h, mul_zero] at key
    exact (mul_eq_zero.mp key).resolve_left (mul_ne_zero two_ne_zero hx)
  · intro h
    rw [h, mul_zero] at key
    exact (mul_eq_zero.mp key.symm).resolve_left hT

/-- **Positivity of `F_L^{exact}` is positivity of longitudinal absorption.** In the physical
region (`Q² > 0`, `x > 0`, real target mass) the target-mass-exact longitudinal structure
function has the sign of the hadronic tensor on the longitudinal direction. -/
theorem FLExact_nonneg_iff_apply_pTransverse_nonneg (g : Bilin V) (K : DisKinematics V)
    (W : Bilin V) (hSymm : g.IsSymm) (hQ2 : 0 < K.Q2 g) {M : ℝ} (hM : g K.p K.p = M ^ 2)
    (hx : 0 < K.xBj g) (F1 F2c : ℝ) (hW : IsF1F2Decomposition g K W F1 F2c) :
    0 ≤ FLExact M (K.xBj g) (K.Q2 g) F1 (structureF2 g K F2c)
      ↔ 0 ≤ W (pTransverse g K) (pTransverse g K) := by
  have hpq : g K.p K.q ≠ 0 := by
    intro h
    apply hx.ne'
    simp [Kinematics.DisKinematics.xBj, h]
  have key := two_xBj_mul_apply_pTransverse g K W hSymm
    ((q_sq_ne_zero_iff g K).mpr hQ2.ne') hpq hM F1 F2c hW
  have hT := pTransverse_self_pos g K hSymm hQ2 hpq (hM ▸ sq_nonneg M)
  rw [← mul_nonneg_iff_of_pos_left hT, ← key, mul_nonneg_iff_of_pos_left (by positivity)]

/-- **Leading twist: `F_L = 0` is exactly the vanishing of longitudinal absorption.** With the
target-mass term dropped (`g p p = 0`), the Callan-Gross relation holds if and only if the
hadronic tensor annihilates the longitudinal polarization direction. The hypothesis
`g p p = 0` is the leading-twist idealization; it is the `M = 0` case of
`FLExact_eq_zero_iff_apply_pTransverse_eq_zero`. -/
theorem isCallanGross_iff_apply_pTransverse_eq_zero (g : Bilin V) (K : DisKinematics V)
    (W : Bilin V) (hSymm : g.IsSymm) (hTwist : g K.p K.p = 0) (hx : K.xBj g ≠ 0) (F1 F2c : ℝ)
    (hW : IsF1F2Decomposition g K W F1 F2c) :
    IsCallanGross (K.xBj g) F1 (structureF2 g K F2c)
      ↔ W (pTransverse g K) (pTransverse g K) = 0 := by
  have hpq : g K.p K.q ≠ 0 := by
    intro h
    apply hx
    simp [Kinematics.DisKinematics.xBj, h]
  have hQ2 : g K.q K.q ≠ 0 := by
    intro h
    apply hx
    simp [Kinematics.DisKinematics.xBj, Kinematics.DisKinematics.Q2, h]
  have hT : g (pTransverse g K) (pTransverse g K) ≠ 0 := by
    have h1 := Q2_mul_pTransverse_self g K hSymm hQ2
    rw [hTwist, mul_zero, zero_add] at h1
    exact right_ne_zero_of_mul (h1 ▸ pow_ne_zero 2 hpq)
  have h := FLExact_eq_zero_iff_apply_pTransverse_eq_zero g K W hSymm
    (M := 0) (by rw [hTwist]; ring) hx hT F1 F2c hW
  rw [FLExact_zero] at h
  unfold IsCallanGross
  exact h

/-!

## The elastic photon-parton channel

-/

variable {Flavor : Type}

/-- An elastic photon-parton channel of the parton model. It is pure data: the two
coefficients of the elastic partonic tensor in the transverse basis of `Tensors.Hadronic`,
the parton charges, the invariant `p·q` of the external kinematics, and the elastic weight
that carries the on-shell condition. The spin of the struck parton enters **only** through
`transverseCoeff` and `longitudinalCoeff`; see `spinHalfChannel` and `scalarChannel`. -/
structure ElasticChannel (Flavor : Type) where
  /-- Electric charge of each parton flavour, in units of the positron charge. -/
  charge : Flavor → ℝ
  /-- The invariant `p·q` of the external kinematics. -/
  pq : ℝ
  /-- The elastic weight `D(x, z, Q²)`. Physically `δ(z - x) / (4 z (p·q))`; every statement
  below holds for an arbitrary weight, and the on-shell property that the parton-model delta
  supplies is isolated in `IsOnShell`. -/
  weight : ℝ → ℝ → ℝ → ℝ
  /-- Coefficient of the transverse projector `-g + q ⊗ q / q²` in the elastic partonic
  tensor, as a function of the light-cone fraction `z` of the struck parton. -/
  transverseCoeff : ℝ → ℝ
  /-- Coefficient of `p_T ⊗ p_T` in the elastic partonic tensor, as a function of the
  light-cone fraction `z` of the struck parton. -/
  longitudinalCoeff : ℝ → ℝ

/-- The `F₁` hard kernel of an elastic channel: charge squared times the transverse
coefficient of the partonic tensor, times the elastic weight. -/
def ElasticChannel.hardF1 (E : ElasticChannel Flavor) : HardKernel Flavor :=
  fun i x z Q2 => E.charge i ^ 2 * E.transverseCoeff z * E.weight x z Q2

/-- The `F₂` hard kernel of an elastic channel. The extra factor `p·q` converts the
`p_T ⊗ p_T` coefficient of `Tensors.Hadronic.IsF1F2Decomposition`, which is `F₂/(p·q)`, into
the physical `F₂`. -/
def ElasticChannel.hardF2 (E : ElasticChannel Flavor) : HardKernel Flavor :=
  fun i x z Q2 => E.charge i ^ 2 * (E.pq * E.longitudinalCoeff z) * E.weight x z Q2

/-- The **longitudinal hard kernel** of an elastic channel, `hardF₂ - 2 x hardF₁`: the kernel
whose leading-order convolution with the densities is `F_L`. -/
def ElasticChannel.longitudinalKernel (E : ElasticChannel Flavor) : HardKernel Flavor :=
  fun i x z Q2 => E.hardF2 i x z Q2 - 2 * x * E.hardF1 i x z Q2

/-- **`F_L` is itself leading-order factorized, with the longitudinal hard kernel.** This is
the exact remainder of the Callan-Gross relation: it assumes no on-shell condition and no
property of the elastic weight, only that the two channel integrands are integrable. -/
theorem loStructureFunction_longitudinalKernel [Fintype Flavor] (E : ElasticChannel Flavor)
    (f : Pdf Flavor) (x Q2 : ℝ)
    (hInt2 : ∀ i : Flavor, MeasureTheory.IntegrableOn
      (fun z => E.hardF2 i x z Q2 * f i z Q2) (Set.Icc (0 : ℝ) 1))
    (hInt1 : ∀ i : Flavor, MeasureTheory.IntegrableOn
      (fun z => E.hardF1 i x z Q2 * f i z Q2) (Set.Icc (0 : ℝ) 1)) :
    loStructureFunction E.hardF2 f x Q2 - 2 * x * loStructureFunction E.hardF1 f x Q2
      = loStructureFunction E.longitudinalKernel f x Q2 := by
  simp only [loStructureFunction]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hsmul : MeasureTheory.IntegrableOn
      (fun z => 2 * x * (E.hardF1 i x z Q2 * f i z Q2)) (Set.Icc (0 : ℝ) 1) :=
    MeasureTheory.Integrable.const_mul (hInt1 i) (2 * x)
  have hpt : ∀ z : ℝ,
      E.hardF2 i x z Q2 * f i z Q2 - 2 * x * (E.hardF1 i x z Q2 * f i z Q2)
        = E.longitudinalKernel i x z Q2 * f i z Q2 := by
    intro z
    simp only [ElasticChannel.longitudinalKernel]
    ring
  have hsplit : (∫ z in Set.Icc (0 : ℝ) 1,
        (E.hardF2 i x z Q2 * f i z Q2 - 2 * x * (E.hardF1 i x z Q2 * f i z Q2)))
      = (∫ z in Set.Icc (0 : ℝ) 1, E.hardF2 i x z Q2 * f i z Q2)
        - ∫ z in Set.Icc (0 : ℝ) 1, 2 * x * (E.hardF1 i x z Q2 * f i z Q2) :=
    MeasureTheory.integral_sub (hInt2 i) hsmul
  have hconst : (∫ z in Set.Icc (0 : ℝ) 1, 2 * x * (E.hardF1 i x z Q2 * f i z Q2))
      = 2 * x * ∫ z in Set.Icc (0 : ℝ) 1, E.hardF1 i x z Q2 * f i z Q2 :=
    MeasureTheory.integral_const_mul (2 * x) _
  simp only [loChannel, convolveAt, integrand]
  rw [← hconst, ← hsplit]
  simp_rw [hpt]

/-- On-shellness of the elastic channel: the elastic weight is supported on `z = x`.

This is the only property of the parton-model delta function that the Callan-Gross derivation
uses — it is the distributional identity `(z - x) δ(z - x) = 0` written pointwise. See the
module docstring for why a Lebesgue *function* satisfying it is necessarily degenerate. -/
def IsOnShell (weight : ℝ → ℝ → ℝ → ℝ) : Prop := ∀ x z Q2, (z - x) * weight x z Q2 = 0

/-!

## Spin 1/2: the Callan-Gross relation

-/

/-- The elastic channel of a massless **spin-1/2** parton. Its two coefficients come from the
Dirac trace `(1/2) Tr[k̸ γ^μ (k̸ + q̸) γ^ν] = 2[k^μ (k+q)^ν + (k+q)^μ k^ν - g^{μν} (k·q)]`
evaluated at `k = z p`, so that `k·q = z (p·q)` and `k_T = z p_T`: the `-g^{μν} (k·q)` term
gives the transverse coefficient `2 z (p·q)` and the `2 k^μ k^ν` term gives the `p_T ⊗ p_T`
coefficient `4 z²`. The trace algebra itself is not formalized here — it needs Dirac matrices
on `Lorentz.Vector 3`, which this abstract-`V` module does not carry — so the two coefficients
are the physics input. They are fixed *independently of each other*, which is what makes the
factor `2 x` below a derivation rather than a restatement. -/
def spinHalfChannel (charge : Flavor → ℝ) (pq : ℝ) (weight : ℝ → ℝ → ℝ → ℝ) :
    ElasticChannel Flavor where
  charge := charge
  pq := pq
  weight := weight
  transverseCoeff := fun z => 2 * z * pq
  longitudinalCoeff := fun z => 4 * z ^ 2

/-- **The longitudinal remainder of the spin-1/2 channel, unconditionally.** No on-shell
condition and no property of the weight are used: the factor `(z - x)` is what the elastic
kinematics has to supply, and it is the whole of the Callan-Gross relation. -/
lemma spinHalfChannel_longitudinalKernel (charge : Flavor → ℝ) (pq : ℝ)
    (weight : ℝ → ℝ → ℝ → ℝ) (i : Flavor) (x z Q2 : ℝ) :
    (spinHalfChannel charge pq weight).longitudinalKernel i x z Q2
      = 4 * charge i ^ 2 * pq * z * ((z - x) * weight x z Q2) := by
  simp only [ElasticChannel.longitudinalKernel, ElasticChannel.hardF1, ElasticChannel.hardF2,
    spinHalfChannel]
  ring

/-- On shell, the two spin-1/2 hard kernels differ by exactly `2 x`. -/
lemma spinHalfChannel_hardF2_apply (charge : Flavor → ℝ) (pq : ℝ)
    (weight : ℝ → ℝ → ℝ → ℝ) (hOn : IsOnShell weight) (i : Flavor) (x z Q2 : ℝ) :
    (spinHalfChannel charge pq weight).hardF2 i x z Q2
      = 2 * x * (spinHalfChannel charge pq weight).hardF1 i x z Q2 := by
  have hz : (z - x) * weight x z Q2 = 0 := hOn x z Q2
  simp only [ElasticChannel.hardF1, ElasticChannel.hardF2, spinHalfChannel]
  linear_combination (4 * charge i ^ 2 * pq * z) * hz

/-- The relation survives the convolution channel by channel: the factor `2 x` is constant in
the convolution variable `z`, so it passes through the integral. -/
lemma loChannel_spinHalfChannel_hardF2 (charge : Flavor → ℝ) (pq : ℝ)
    (weight : ℝ → ℝ → ℝ → ℝ) (hOn : IsOnShell weight) (f : Pdf Flavor) (i : Flavor)
    (x Q2 : ℝ) :
    loChannel (spinHalfChannel charge pq weight).hardF2 f i x Q2
      = 2 * x * loChannel (spinHalfChannel charge pq weight).hardF1 f i x Q2 := by
  have hpt : ∀ z : ℝ,
      (spinHalfChannel charge pq weight).hardF2 i x z Q2 * f i z Q2
        = 2 * x * ((spinHalfChannel charge pq weight).hardF1 i x z Q2 * f i z Q2) := by
    intro z
    rw [spinHalfChannel_hardF2_apply charge pq weight hOn i x z Q2]
    ring
  have hconst : (∫ z in Set.Icc (0 : ℝ) 1,
        2 * x * ((spinHalfChannel charge pq weight).hardF1 i x z Q2 * f i z Q2))
      = 2 * x * ∫ z in Set.Icc (0 : ℝ) 1,
        (spinHalfChannel charge pq weight).hardF1 i x z Q2 * f i z Q2 :=
    MeasureTheory.integral_const_mul (2 * x) _
  simp only [loChannel, convolveAt, integrand]
  simp_rw [hpt]
  exact hconst

/-- The relation survives the flavour sum. -/
lemma loStructureFunction_spinHalfChannel_hardF2 [Fintype Flavor] (charge : Flavor → ℝ)
    (pq : ℝ) (weight : ℝ → ℝ → ℝ → ℝ) (hOn : IsOnShell weight) (f : Pdf Flavor) (x Q2 : ℝ) :
    loStructureFunction (spinHalfChannel charge pq weight).hardF2 f x Q2
      = 2 * x * loStructureFunction (spinHalfChannel charge pq weight).hardF1 f x Q2 := by
  simp only [loStructureFunction]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl
    (fun i _ => loChannel_spinHalfChannel_hardF2 charge pq weight hOn f i x Q2)

/-- **The Callan-Gross relation.** If `F₁` and `F₂` are leading-order factorized with the two
hard kernels of the elastic spin-1/2 channel, and the channel is on shell, then
`F₂(x, Q²) = 2 x F₁(x, Q²)` at every `x` and every `Q²` separately.

The two kernels are fixed independently in `spinHalfChannel`, from the two terms of the
photon-quark Dirac trace; the factor `2 x` is produced by the arithmetic
`4 z² - 2 x · 2 z = 4 z (z - x)` together with the on-shell condition, and is not assumed. -/
theorem callan_gross [Fintype Flavor] (charge : Flavor → ℝ) (pq : ℝ)
    (weight : ℝ → ℝ → ℝ → ℝ) (hOn : IsOnShell weight) (f : Pdf Flavor) (F1 F2 : ℝ → ℝ → ℝ)
    (h1 : IsLOFactorized F1 (spinHalfChannel charge pq weight).hardF1 f)
    (h2 : IsLOFactorized F2 (spinHalfChannel charge pq weight).hardF2 f) (x Q2 : ℝ) :
    IsCallanGross x (F1 x Q2) (F2 x Q2) := by
  unfold IsCallanGross FL
  rw [h1 x Q2, h2 x Q2,
    loStructureFunction_spinHalfChannel_hardF2 charge pq weight hOn f x Q2]
  ring

/-!

## Spin 0: the contrast

-/

/-- The elastic channel of a **spin-0** parton. The scalar-QED vertex `(2k+q)^μ` gives
`T^{μν} = (2k+q)^μ (2k+q)^ν`, which expands as `4 k_T^μ k_T^ν` plus a `q ⊗ q` term removed by
current conservation: there is **no** `g^{μν}` term, so the transverse coefficient vanishes
identically while the `p_T ⊗ p_T` coefficient is the same `4 z²` as for spin 1/2. -/
def scalarChannel (charge : Flavor → ℝ) (pq : ℝ) (weight : ℝ → ℝ → ℝ → ℝ) :
    ElasticChannel Flavor where
  charge := charge
  pq := pq
  weight := weight
  transverseCoeff := fun _ => 0
  longitudinalCoeff := fun z => 4 * z ^ 2

/-- **The two spins differ only in the transverse coefficient.** The `F₂` hard kernels of the
spin-0 and spin-1/2 elastic channels are literally the same function; everything below is
caused by the transverse coefficient alone. -/
lemma scalarChannel_hardF2_apply (charge : Flavor → ℝ) (pq : ℝ) (weight : ℝ → ℝ → ℝ → ℝ)
    (i : Flavor) (x z Q2 : ℝ) :
    (scalarChannel charge pq weight).hardF2 i x z Q2
      = (spinHalfChannel charge pq weight).hardF2 i x z Q2 := rfl

/-- The spin-0 `F₁` hard kernel vanishes identically. -/
lemma scalarChannel_hardF1_apply (charge : Flavor → ℝ) (pq : ℝ) (weight : ℝ → ℝ → ℝ → ℝ)
    (i : Flavor) (x z Q2 : ℝ) :
    (scalarChannel charge pq weight).hardF1 i x z Q2 = 0 := by
  simp [ElasticChannel.hardF1, scalarChannel]

/-- The leading-order `F₁` of a scalar-parton model vanishes. -/
lemma loStructureFunction_scalarChannel_hardF1 [Fintype Flavor] (charge : Flavor → ℝ)
    (pq : ℝ) (weight : ℝ → ℝ → ℝ → ℝ) (f : Pdf Flavor) (x Q2 : ℝ) :
    loStructureFunction (scalarChannel charge pq weight).hardF1 f x Q2 = 0 := by
  simp only [loStructureFunction]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  simp only [loChannel]
  refine convolveAt_eq_zero_of_integrand_zero _ _ _ (fun z => ?_)
  simp [integrand, scalarChannel_hardF1_apply]

/-- **Spin-0 partons give `F₁ = 0`.** No on-shell condition is needed: the scalar vertex has
no transverse structure at all. -/
theorem scalar_F1_eq_zero [Fintype Flavor] (charge : Flavor → ℝ) (pq : ℝ)
    (weight : ℝ → ℝ → ℝ → ℝ) (f : Pdf Flavor) (F1 : ℝ → ℝ → ℝ)
    (h1 : IsLOFactorized F1 (scalarChannel charge pq weight).hardF1 f) (x Q2 : ℝ) :
    F1 x Q2 = 0 := by
  rw [h1 x Q2, loStructureFunction_scalarChannel_hardF1]

/-- For spin-0 partons the longitudinal structure function is the whole of `F₂`. -/
theorem scalar_FL_eq_F2 [Fintype Flavor] (charge : Flavor → ℝ) (pq : ℝ)
    (weight : ℝ → ℝ → ℝ → ℝ) (f : Pdf Flavor) (F1 F2 : ℝ → ℝ → ℝ)
    (h1 : IsLOFactorized F1 (scalarChannel charge pq weight).hardF1 f) (x Q2 : ℝ) :
    FL x (F1 x Q2) (F2 x Q2) = F2 x Q2 := by
  unfold FL
  rw [scalar_F1_eq_zero charge pq weight f F1 h1 x Q2]
  ring

/-- **The Callan-Gross relation is dynamics, not a kinematic identity.** With spin-0 partons
the relation fails wherever `F₂` is non-zero, even though the kinematics, the basis, the
charges, the densities and the elastic weight are the same as in `callan_gross`. This is the
statement that makes the spin-1/2 theorem informative. -/
theorem scalar_not_isCallanGross [Fintype Flavor] (charge : Flavor → ℝ) (pq : ℝ)
    (weight : ℝ → ℝ → ℝ → ℝ) (f : Pdf Flavor) (F1 F2 : ℝ → ℝ → ℝ)
    (h1 : IsLOFactorized F1 (scalarChannel charge pq weight).hardF1 f) (x Q2 : ℝ)
    (hne : F2 x Q2 ≠ 0) :
    ¬ IsCallanGross x (F1 x Q2) (F2 x Q2) := by
  unfold IsCallanGross
  rw [scalar_FL_eq_F2 charge pq weight f F1 F2 h1 x Q2]
  exact hne

end Longitudinal
end Tensors
end DIS
end Scattering
end QFT
end EpsilonEridani
