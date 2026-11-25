/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.QFT.Scattering.DIS.Inclusive.CrossSection
public import EpsilonEridani.QFT.Scattering.DIS.PVES.Electroweak.Parameters

/-!
# The electroweak neutral-current cross section and its three terms

A charged lepton scatters off a nucleon by exchanging a photon or a `Z` boson. The amplitude is
the sum of the two exchange amplitudes, so the cross section is a quadratic form in them: a
pure-photon term, a photon-`Z` interference term and a pure-`Z` term. This file writes the
neutral-current cross section of a massless lepton of definite helicity in that form, each term
the product of a propagator factor, a coupling factor and the inclusive cross section
`Inclusive.dSigmaDxDQ2` evaluated on the hadronic structure functions of the corresponding pair
of currents, and proves how each term behaves under reversal of the beam helicity. Reading
`Inclusive.dSigmaDxDQ2` as the contraction of the helicity-projected leptonic tensor with the
hadronic tensor is the intended interpretation; it is not derived here.

## The beam coupling

A massless fermion of helicity `λ = ±1` has only one chiral component, with chirality equal to
its helicity, so the `Z` vertex `γ^μ (g_V - g_A γ⁵)` acts on it as the number
`g_V - λ g_A` (`FermionNeutralCurrentCouplings.helicityCoupling`): `2 g_R` for `λ = 1` and
`2 g_L` for `λ = -1`. The photon vertex acts as the charge `q`. Both leptonic currents of the
squared amplitude then see the same helicity-projected spin trace, so the leptonic factor of
the term with currents `i, j` is the product `c_i c_j` of the beam couplings `c_γ = q` and
`c_Z = g_V - λ g_A`, times one universal contraction. This factorisation is not derived here
from the leptonic tensor: it is taken as the definition of `CrossSection.neutralCurrent`, whose
structure functions are the coupling-weighted sums of those of the individual pairs of
currents. That contraction is
`Inclusive.dSigmaDxDQ2` with the helicity sign `λ` in the slot of the parity-odd sign: its
parity-odd term `-λ Y₋ x F₃` is `+Y₋ x F₃` for a left-handed beam, the sign that
`Inclusive.crossSectionBracket` assigns to an electron or neutrino.

An antilepton beam is described by the same formulas with the charge-conjugate couplings: charge
`-q`, vector coupling `-g_V` and axial coupling `g_A`.

The relative normalisation of the two exchanges is a free real parameter `η`, the ratio of the
`Z`-exchange to the photon-exchange propagator-and-coupling factor. Its tree-level value is not
used in this file.

## Main results

* `CrossSection.neutralCurrent_eq_add`: by the linearity of `Inclusive.dSigmaDxDQ2` in the
  structure functions, the defining expression of `neutralCurrent` regroups into the sum of
  `photonTerm`, `gammaZTerm` and `zBosonTerm`, with coupling factors `q²`, `q (g_V - λ g_A)` and
  `(g_V - λ g_A)²` and propagator factors `1`, `η` and `η²`.
* `CrossSection.photonTerm_eq_sq_mul_loNCdSigma`: at the photon flux factor `K = 2π α² / Q²`,
  zero target mass and with the Callan-Gross relation, the pure-photon term is `q²` times the
  one-photon-exchange cross section `loNCdSigma` of
  `EpsilonEridani.QFT.Scattering.DIS.CrossSection`; for a beam of unit charge there is no
  residual factor (`CrossSection.photonTerm_eq_loNCdSigma_of_sq_eq_one`). Without `Z` exchange
  the full cross section is its pure-photon term (`CrossSection.neutralCurrent_eta_zero`), and
  `CrossSection.neutralCurrent_eta_zero_eq_loNCdSigma_of_sq_eq_one` is the electromagnetic limit.
* `CrossSection.neutralCurrent_true_sub_false`: the pure-photon term does not depend on the
  helicity, so the helicity difference `σ_R - σ_L` is carried by the interference and pure-`Z`
  terms alone. `CrossSection.gammaZTerm_true_sub_false` and
  `CrossSection.zBosonTerm_true_sub_false` give each piece explicitly: the parity-even
  structure functions enter the interference difference through `g_A` and the parity-odd one
  through `g_V`.
* `CrossSection.gammaZTerm_true_add_false` and `CrossSection.zBosonTerm_true_add_false`: the
  helicity sums `σ_R + σ_L`, twice the helicity-even parts. The interference term is therefore
  not purely odd: its even part is `η q (K / (x Q²)) (g_V B^{γZ} + g_A Y₋ x F₃^{γZ})`, with
  `B^{γZ}` the parity-even bracket. It is odd wherever this combination vanishes
  (`CrossSection.gammaZTerm_true_eq_neg_false_of_helicityEven_eq_zero`) and, where the
  prefactor `η q K / (x Q²)` does not vanish, only there
  (`CrossSection.gammaZTerm_true_eq_neg_false_iff`). The four helicity lemmas and the closed
  forms at a general helicity, `CrossSection.gammaZTerm_eq_crossSectionBracket_sub` and
  `CrossSection.zBosonTerm_eq_crossSectionBracket_sub`, are instances of one fact about a
  coupling `a + λ b` affine in the helicity sign
  (`CrossSection.add_helicitySign_mul_mul_dSigmaDxDQ2` and its `true_sub_false` and
  `true_add_false` corollaries).
* `CrossSection.neutralCurrent_true_add_false_div_two`: the helicity average is the unpolarised
  cross section `Inclusive.dSigmaDxDQ2` at the fixed sign `-1` of the parity-odd term, whatever
  the beam charge (it enters through `q` in the effective structure functions; for an electron
  this is the usual electron sign), with the familiar effective structure functions
  `q² F^γ + q g_V η F^{γZ} + (g_V² + g_A²) η² F^Z` and `q g_A η F₃^{γZ} + 2 g_V g_A η² F₃^Z`.
* `CrossSection.gammaZTerm_electron_true_sub_false`: for the Standard Model electron,
  `σ_R - σ_L` of the interference term is `-η K/(xQ²) (B^{γZ} + Q_W^e Y₋ x F₃^{γZ})`, which
  exhibits the suppression of the parity-odd structure function by the electron weak charge
  `Q_W^e = 1 - 4 sin²θ_W` (`Electroweak.electronWeakCharge`).

## Conventions

The kinematic variables, the target mass `M`, the inelasticity factors `Y₊`, `Y₋` and the flux
factor `K` are those of `Inclusive.CrossSection`; every term is normalised to the photon flux
factor, which is `K = 2π α² / Q²` in the comparison with `loNCdSigma`. The helicity is a
`Bool`, read through `Electroweak.helicitySign`: `true` is right-handed (`λ = 1`) and `false`
left-handed (`λ = -1`). The couplings `g_V`, `g_A` are in the normalisation of
`Electroweak.FermionNeutralCurrentCouplings.ofQuantumNumbers`. The interference structure
functions `F_i^{γZ}` are those of the full interference term of the squared amplitude, so they
include both orderings of the two currents; at leading order
`F₂^{γZ} = 2 x Σ_f e_f g_V^f (f + f_bar)`, with `f_bar` the antiparton density. The hadronic
structure functions are inputs at a fixed kinematic point, bundled as
`CrossSection.NeutralCurrentStructureFunctions` for `neutralCurrent` and passed as bare `F₁`,
`F₂`, `F₃` to each of the three terms; their definitions and parton content are not developed
here.

## References

* H1 and ZEUS Collaborations, *Combination of measurements of inclusive deep inelastic
  e±p scattering cross sections and QCD analysis of HERA data*, Eur. Phys. J. C **75** (2015)
  580, section 2, for the polarised neutral-current cross section in this form.
* Particle Data Group, *Review of Particle Physics*, section "Structure functions".
-/

public section

noncomputable section

namespace EpsilonEridani.QFT.Scattering.DIS.PVES

open Inclusive

namespace CrossSection

open Electroweak

/-- The hadronic input of the neutral-current cross section at a fixed kinematic point: the
structure functions `F₁^γ`, `F₂^γ` of the electromagnetic current, and `F₁`, `F₂`, `F₃` of the
photon-`Z` interference and of the `Z` current. The electromagnetic current conserves parity,
so it has no `F₃`. -/
@[ext]
structure NeutralCurrentStructureFunctions where
  /-- `F₁^γ`. -/
  photonF1 : ℝ
  /-- `F₂^γ`. -/
  photonF2 : ℝ
  /-- `F₁^{γZ}`, from both orderings of the two currents. -/
  gammaZF1 : ℝ
  /-- `F₂^{γZ}`, from both orderings of the two currents. -/
  gammaZF2 : ℝ
  /-- `F₃^{γZ}`, from both orderings of the two currents. -/
  gammaZF3 : ℝ
  /-- `F₁^Z`. -/
  zBosonF1 : ℝ
  /-- `F₂^Z`. -/
  zBosonF2 : ℝ
  /-- `F₃^Z`. -/
  zBosonF3 : ℝ

variable (K M x Q2 y q η : ℝ) (ℓ : FermionNeutralCurrentCouplings)
  (H : NeutralCurrentStructureFunctions) (h : Bool) (F1 F2 F3 : ℝ)

/-- The neutral-current cross section `d²σ/dx dQ²` of a massless lepton of charge `q`,
neutral-current couplings `ℓ` and helicity `helicitySign h`, at photon flux factor `K` and
`Z`-to-photon propagator ratio `η`. It is defined as the inclusive cross section
`Inclusive.dSigmaDxDQ2`, with the helicity sign in the slot of the parity-odd sign, evaluated on
the coupling-weighted structure functions
`F_i = q² F_i^γ + q (η c_Z) F_i^{γZ} + (η c_Z)² F_i^Z` with `c_Z = g_V - λ g_A`. Its reading as
the contraction of the helicity-projected leptonic tensor with the hadronic tensor of the summed
amplitude is the intended interpretation, not established here. -/
def neutralCurrent : ℝ :=
  dSigmaDxDQ2 K M (helicitySign h) x Q2 y
    (q ^ 2 * H.photonF1 + q * (η * ℓ.helicityCoupling h) * H.gammaZF1
      + (η * ℓ.helicityCoupling h) ^ 2 * H.zBosonF1)
    (q ^ 2 * H.photonF2 + q * (η * ℓ.helicityCoupling h) * H.gammaZF2
      + (η * ℓ.helicityCoupling h) ^ 2 * H.zBosonF2)
    (q * (η * ℓ.helicityCoupling h) * H.gammaZF3 + (η * ℓ.helicityCoupling h) ^ 2 * H.zBosonF3)

theorem neutralCurrent_def :
    neutralCurrent K M x Q2 y q η ℓ H h =
      dSigmaDxDQ2 K M (helicitySign h) x Q2 y
        (q ^ 2 * H.photonF1 + q * (η * ℓ.helicityCoupling h) * H.gammaZF1
          + (η * ℓ.helicityCoupling h) ^ 2 * H.zBosonF1)
        (q ^ 2 * H.photonF2 + q * (η * ℓ.helicityCoupling h) * H.gammaZF2
          + (η * ℓ.helicityCoupling h) ^ 2 * H.zBosonF2)
        (q * (η * ℓ.helicityCoupling h) * H.gammaZF3
          + (η * ℓ.helicityCoupling h) ^ 2 * H.zBosonF3) :=
  (rfl)

/-- The pure-photon term of the neutral-current cross section: coupling factor `q²`, propagator
factor `1`, and the contraction with electromagnetic structure functions `F₁ = F₁^γ`,
`F₂ = F₂^γ`. It has no parity-odd structure function, so the sign slot of
`Inclusive.dSigmaDxDQ2` is immaterial (`photonTerm_eq_sq_mul_dSigmaDxDQ2`) and the term does not
depend on the beam helicity. -/
def photonTerm : ℝ :=
  q ^ 2 * dSigmaDxDQ2 K M 0 x Q2 y F1 F2 0

theorem photonTerm_def :
    photonTerm K M x Q2 y q F1 F2 = q ^ 2 * dSigmaDxDQ2 K M 0 x Q2 y F1 F2 0 :=
  (rfl)

/-- The photon-`Z` interference term of the neutral-current cross section: coupling factor
`q (g_V - λ g_A)`, propagator factor `η`, and the contraction with interference structure
functions `F_i = F_i^{γZ}`. -/
def gammaZTerm : ℝ :=
  η * (q * ℓ.helicityCoupling h) * dSigmaDxDQ2 K M (helicitySign h) x Q2 y F1 F2 F3

theorem gammaZTerm_def :
    gammaZTerm K M x Q2 y q η ℓ h F1 F2 F3 =
      η * (q * ℓ.helicityCoupling h) * dSigmaDxDQ2 K M (helicitySign h) x Q2 y F1 F2 F3 :=
  (rfl)

/-- The pure-`Z` term of the neutral-current cross section: coupling factor `(g_V - λ g_A)²`,
propagator factor `η²`, and the contraction with `Z` structure functions `F_i = F_i^Z`. -/
def zBosonTerm : ℝ :=
  η ^ 2 * ℓ.helicityCoupling h ^ 2 * dSigmaDxDQ2 K M (helicitySign h) x Q2 y F1 F2 F3

theorem zBosonTerm_def :
    zBosonTerm K M x Q2 y η ℓ h F1 F2 F3 =
      η ^ 2 * ℓ.helicityCoupling h ^ 2 * dSigmaDxDQ2 K M (helicitySign h) x Q2 y F1 F2 F3 :=
  (rfl)

/-- The pure-photon term is the electromagnetic contraction for every value of the sign of the
parity-odd term, since its parity-odd structure function vanishes. -/
theorem photonTerm_eq_sq_mul_dSigmaDxDQ2 (s : ℝ) :
    photonTerm K M x Q2 y q F1 F2 = q ^ 2 * dSigmaDxDQ2 K M s x Q2 y F1 F2 0 := by
  rw [photonTerm_def, dSigmaDxDQ2_F3_zero K M s]

/-- **The three terms.** The defining expression of the neutral-current cross section, a single
contraction with the coupling-weighted structure functions of the three pairs of currents,
regroups by linearity into the sum of the pure-photon, interference and pure-`Z` terms. The
pure-photon term may carry the sign slot `0` of `photonTerm` because its parity-odd structure
function vanishes (`photonTerm_eq_sq_mul_dSigmaDxDQ2`). -/
theorem neutralCurrent_eq_add :
    neutralCurrent K M x Q2 y q η ℓ H h =
      photonTerm K M x Q2 y q H.photonF1 H.photonF2
        + gammaZTerm K M x Q2 y q η ℓ h H.gammaZF1 H.gammaZF2 H.gammaZF3
        + zBosonTerm K M x Q2 y η ℓ h H.zBosonF1 H.zBosonF2 H.zBosonF3 := by
  simp only [neutralCurrent_def, photonTerm_def, gammaZTerm_def, zBosonTerm_def,
    dSigmaDxDQ2_def, crossSectionBracket_def]
  ring

/-- At zero target mass, at the photon flux factor `K = 2π α² / Q²` and with electromagnetic
structure functions obeying the Callan-Gross relation, the pure-photon term is `q²` times the
one-photon-exchange cross section `loNCdSigma`. -/
theorem photonTerm_eq_sq_mul_loNCdSigma (α : ℝ) (hCG : Tensors.Longitudinal.IsCallanGross x F1 F2) :
    photonTerm (2 * Real.pi * α ^ 2 / Q2) 0 x Q2 y q F1 F2 = q ^ 2 * loNCdSigma α x Q2 y F2 := by
  rw [photonTerm_eq_sq_mul_dSigmaDxDQ2 (s := 0), dSigmaDxDQ2_eq_loNCdSigma _ _ _ _ _ _ _ hCG]

/-- **The pure-photon term is the one-photon-exchange cross section.** For a beam of unit charge,
zero target mass, the photon flux factor `K = 2π α² / Q²` and electromagnetic structure functions
obeying the Callan-Gross relation, it is `loNCdSigma`, with no residual factor. -/
theorem photonTerm_eq_loNCdSigma_of_sq_eq_one (α : ℝ) {q : ℝ} (hq : q ^ 2 = 1)
    (hCG : Tensors.Longitudinal.IsCallanGross x F1 F2) :
    photonTerm (2 * Real.pi * α ^ 2 / Q2) 0 x Q2 y q F1 F2 = loNCdSigma α x Q2 y F2 := by
  rw [photonTerm_eq_sq_mul_loNCdSigma (hCG := hCG), hq, one_mul]

/-- Without `Z` exchange the interference term vanishes. -/
@[simp]
theorem gammaZTerm_eta_zero : gammaZTerm K M x Q2 y q 0 ℓ h F1 F2 F3 = 0 := by
  simp [gammaZTerm_def]

/-- Without `Z` exchange the pure-`Z` term vanishes. -/
@[simp]
theorem zBosonTerm_eta_zero : zBosonTerm K M x Q2 y 0 ℓ h F1 F2 F3 = 0 := by
  simp [zBosonTerm_def]

/-- Without `Z` exchange the neutral-current cross section is its pure-photon term. -/
@[simp]
theorem neutralCurrent_eta_zero :
    neutralCurrent K M x Q2 y q 0 ℓ H h = photonTerm K M x Q2 y q H.photonF1 H.photonF2 := by
  simp [neutralCurrent_eq_add]

/-- **The electromagnetic limit.** Switching off the `Z` exchange, a beam of unit charge at zero
target mass, at the photon flux factor `K = 2π α² / Q²` and with Callan-Gross structure functions
has the one-photon-exchange cross section `loNCdSigma`, whatever its helicity and its
neutral-current couplings. -/
theorem neutralCurrent_eta_zero_eq_loNCdSigma_of_sq_eq_one (α : ℝ) {q : ℝ} (hq : q ^ 2 = 1)
    (hCG : Tensors.Longitudinal.IsCallanGross x H.photonF1 H.photonF2) :
    neutralCurrent (2 * Real.pi * α ^ 2 / Q2) 0 x Q2 y q 0 ℓ H h =
      loNCdSigma α x Q2 y H.photonF2 := by
  rw [neutralCurrent_eta_zero, photonTerm_eq_loNCdSigma_of_sq_eq_one (hq := hq) (hCG := hCG)]

section helicityAffine

variable (a b : ℝ)

/-- **A coupling affine in the helicity sign.** For `λ = helicitySign h`, the contraction at sign
`λ` weighted by a coupling `a + λ b` splits into its parity-even and parity-odd parts as
`(K / (x Q²)) ((a + λ b) B - (λ a + b) Y₋ x F₃)`, with `B` the parity-even bracket; the
parity-odd coefficient uses `λ² = 1`. The interference and pure-`Z` terms are the instances
`(a, b) = (η q g_V, -η q g_A)` and `(η² (g_V² + g_A²), -2 η² g_V g_A)`. -/
theorem add_helicitySign_mul_mul_dSigmaDxDQ2 :
    (a + helicitySign h * b) * dSigmaDxDQ2 K M (helicitySign h) x Q2 y F1 F2 F3 =
      K / (x * Q2) * ((a + helicitySign h * b) * crossSectionBracket M 0 x Q2 y F1 F2 0
        - (helicitySign h * a + b) * (Yminus y * (x * F3))) := by
  cases h <;>
    simp only [dSigmaDxDQ2_def, crossSectionBracket_def, helicitySign_true, helicitySign_false] <;>
    ring

/-- The helicity difference of a contraction weighted by a coupling affine in the helicity sign:
`σ_R - σ_L = (K / (x Q²)) (2 b B - 2 a Y₋ x F₃)`. -/
theorem add_helicitySign_mul_mul_dSigmaDxDQ2_true_sub_false :
    (a + helicitySign true * b) * dSigmaDxDQ2 K M (helicitySign true) x Q2 y F1 F2 F3
        - (a + helicitySign false * b) * dSigmaDxDQ2 K M (helicitySign false) x Q2 y F1 F2 F3 =
      K / (x * Q2) * (2 * b * crossSectionBracket M 0 x Q2 y F1 F2 0
        - 2 * a * (Yminus y * (x * F3))) := by
  rw [add_helicitySign_mul_mul_dSigmaDxDQ2, add_helicitySign_mul_mul_dSigmaDxDQ2,
    helicitySign_true, helicitySign_false]
  ring

/-- The helicity sum of a contraction weighted by a coupling affine in the helicity sign:
`σ_R + σ_L = (K / (x Q²)) (2 a B - 2 b Y₋ x F₃)`. -/
theorem add_helicitySign_mul_mul_dSigmaDxDQ2_true_add_false :
    (a + helicitySign true * b) * dSigmaDxDQ2 K M (helicitySign true) x Q2 y F1 F2 F3
        + (a + helicitySign false * b) * dSigmaDxDQ2 K M (helicitySign false) x Q2 y F1 F2 F3 =
      K / (x * Q2) * (2 * a * crossSectionBracket M 0 x Q2 y F1 F2 0
        - 2 * b * (Yminus y * (x * F3))) := by
  rw [add_helicitySign_mul_mul_dSigmaDxDQ2, add_helicitySign_mul_mul_dSigmaDxDQ2,
    helicitySign_true, helicitySign_false]
  ring

end helicityAffine

/-- The interference term at helicity `λ = helicitySign h`, split into its parity-even and
parity-odd parts:
`η q (K / (x Q²)) ((g_V - λ g_A) B^{γZ} - (λ g_V - g_A) Y₋ x F₃^{γZ})`, with `B^{γZ}` the
parity-even part of the bracket. -/
theorem gammaZTerm_eq_crossSectionBracket_sub :
    gammaZTerm K M x Q2 y q η ℓ h F1 F2 F3 =
      η * q * (K / (x * Q2)) *
        ((ℓ.gV - helicitySign h * ℓ.gA) * crossSectionBracket M 0 x Q2 y F1 F2 0
          - (helicitySign h * ℓ.gV - ℓ.gA) * (Yminus y * (x * F3))) := by
  rw [gammaZTerm_def, FermionNeutralCurrentCouplings.helicityCoupling_def]
  linear_combination add_helicitySign_mul_mul_dSigmaDxDQ2 K M x Q2 y h F1 F2 F3
    (η * q * ℓ.gV) (-(η * q * ℓ.gA))

/-- The pure-`Z` term at helicity `λ = helicitySign h`, split into its parity-even and
parity-odd parts:
`η² (K / (x Q²)) ((g_V² + g_A² - 2 λ g_V g_A) B^Z - (λ (g_V² + g_A²) - 2 g_V g_A) Y₋ x F₃^Z)`. -/
theorem zBosonTerm_eq_crossSectionBracket_sub :
    zBosonTerm K M x Q2 y η ℓ h F1 F2 F3 =
      η ^ 2 * (K / (x * Q2)) *
        ((ℓ.gV ^ 2 + ℓ.gA ^ 2 - 2 * helicitySign h * ℓ.gV * ℓ.gA)
            * crossSectionBracket M 0 x Q2 y F1 F2 0
          - (helicitySign h * (ℓ.gV ^ 2 + ℓ.gA ^ 2) - 2 * ℓ.gV * ℓ.gA)
            * (Yminus y * (x * F3))) := by
  rw [zBosonTerm_def, FermionNeutralCurrentCouplings.helicityCoupling_sq]
  linear_combination add_helicitySign_mul_mul_dSigmaDxDQ2 K M x Q2 y h F1 F2 F3
    (η ^ 2 * (ℓ.gV ^ 2 + ℓ.gA ^ 2)) (-(2 * η ^ 2 * ℓ.gV * ℓ.gA))

/-- The helicity difference of the interference term. The parity-even structure functions enter
through the axial coupling and the parity-odd one through the vector coupling:
`σ_R - σ_L = -2 η q (K / (x Q²)) (g_A B^{γZ} + g_V Y₋ x F₃^{γZ})`, with `B^{γZ}` the
parity-even part of the bracket. -/
theorem gammaZTerm_true_sub_false :
    gammaZTerm K M x Q2 y q η ℓ true F1 F2 F3 - gammaZTerm K M x Q2 y q η ℓ false F1 F2 F3 =
      -2 * η * q * (K / (x * Q2)) *
        (ℓ.gA * crossSectionBracket M 0 x Q2 y F1 F2 0 + ℓ.gV * (Yminus y * (x * F3))) := by
  simp only [gammaZTerm_def, FermionNeutralCurrentCouplings.helicityCoupling_def]
  linear_combination add_helicitySign_mul_mul_dSigmaDxDQ2_true_sub_false K M x Q2 y F1 F2 F3
    (η * q * ℓ.gV) (-(η * q * ℓ.gA))

/-- The helicity sum of the interference term:
`σ_R + σ_L = 2 η q (K / (x Q²)) (g_V B^{γZ} + g_A Y₋ x F₃^{γZ})`. The interference term is odd
under helicity reversal wherever this combination vanishes
(`gammaZTerm_true_eq_neg_false_of_helicityEven_eq_zero`), and, where the prefactor
`η q K / (x Q²)` does not vanish, only there (`gammaZTerm_true_eq_neg_false_iff`). -/
theorem gammaZTerm_true_add_false :
    gammaZTerm K M x Q2 y q η ℓ true F1 F2 F3 + gammaZTerm K M x Q2 y q η ℓ false F1 F2 F3 =
      2 * η * q * (K / (x * Q2)) *
        (ℓ.gV * crossSectionBracket M 0 x Q2 y F1 F2 0 + ℓ.gA * (Yminus y * (x * F3))) := by
  simp only [gammaZTerm_def, FermionNeutralCurrentCouplings.helicityCoupling_def]
  linear_combination add_helicitySign_mul_mul_dSigmaDxDQ2_true_add_false K M x Q2 y F1 F2 F3
    (η * q * ℓ.gV) (-(η * q * ℓ.gA))

/-- **Oddness of the interference term.** Where the helicity-even combination
`g_V B^{γZ} + g_A Y₋ x F₃^{γZ}` of `gammaZTerm_true_add_false` vanishes, the interference term
is odd under reversal of the beam helicity. The converse holds where the prefactor
`η q K / (x Q²)` does not vanish (`gammaZTerm_true_eq_neg_false_iff`). -/
theorem gammaZTerm_true_eq_neg_false_of_helicityEven_eq_zero
    (hEven : ℓ.gV * crossSectionBracket M 0 x Q2 y F1 F2 0 + ℓ.gA * (Yminus y * (x * F3)) = 0) :
    gammaZTerm K M x Q2 y q η ℓ true F1 F2 F3 = -gammaZTerm K M x Q2 y q η ℓ false F1 F2 F3 := by
  rw [← add_eq_zero_iff_eq_neg, gammaZTerm_true_add_false, hEven, mul_zero]

/-- **When the interference term is odd.** Where the prefactor `η q K / (x Q²)` does not vanish,
the interference term is odd under reversal of the beam helicity if and only if the
helicity-even combination `g_V B^{γZ} + g_A Y₋ x F₃^{γZ}` of `gammaZTerm_true_add_false`
vanishes, so it is not odd for general couplings and structure functions. -/
theorem gammaZTerm_true_eq_neg_false_iff (hK : η * q * (K / (x * Q2)) ≠ 0) :
    gammaZTerm K M x Q2 y q η ℓ true F1 F2 F3 = -gammaZTerm K M x Q2 y q η ℓ false F1 F2 F3 ↔
      ℓ.gV * crossSectionBracket M 0 x Q2 y F1 F2 0 + ℓ.gA * (Yminus y * (x * F3)) = 0 := by
  refine ⟨fun hOdd => ?_, gammaZTerm_true_eq_neg_false_of_helicityEven_eq_zero K M x Q2 y q η ℓ
    F1 F2 F3⟩
  have h2 : 2 * η * q * (K / (x * Q2)) ≠ 0 := by
    simpa only [mul_assoc] using mul_ne_zero two_ne_zero hK
  rwa [← add_eq_zero_iff_eq_neg, gammaZTerm_true_add_false, mul_eq_zero_iff_left h2] at hOdd

/-- The helicity difference of the pure-`Z` term:
`σ_R - σ_L = -2 η² (K / (x Q²)) (2 g_V g_A B^Z + (g_V² + g_A²) Y₋ x F₃^Z)`. -/
theorem zBosonTerm_true_sub_false :
    zBosonTerm K M x Q2 y η ℓ true F1 F2 F3 - zBosonTerm K M x Q2 y η ℓ false F1 F2 F3 =
      -2 * η ^ 2 * (K / (x * Q2)) *
        (2 * ℓ.gV * ℓ.gA * crossSectionBracket M 0 x Q2 y F1 F2 0
          + (ℓ.gV ^ 2 + ℓ.gA ^ 2) * (Yminus y * (x * F3))) := by
  simp only [zBosonTerm_def, FermionNeutralCurrentCouplings.helicityCoupling_sq]
  linear_combination add_helicitySign_mul_mul_dSigmaDxDQ2_true_sub_false K M x Q2 y F1 F2 F3
    (η ^ 2 * (ℓ.gV ^ 2 + ℓ.gA ^ 2)) (-(2 * η ^ 2 * ℓ.gV * ℓ.gA))

/-- The helicity sum of the pure-`Z` term:
`σ_R + σ_L = 2 η² (K / (x Q²)) ((g_V² + g_A²) B^Z + 2 g_V g_A Y₋ x F₃^Z)`. -/
theorem zBosonTerm_true_add_false :
    zBosonTerm K M x Q2 y η ℓ true F1 F2 F3 + zBosonTerm K M x Q2 y η ℓ false F1 F2 F3 =
      2 * η ^ 2 * (K / (x * Q2)) *
        ((ℓ.gV ^ 2 + ℓ.gA ^ 2) * crossSectionBracket M 0 x Q2 y F1 F2 0
          + 2 * ℓ.gV * ℓ.gA * (Yminus y * (x * F3))) := by
  simp only [zBosonTerm_def, FermionNeutralCurrentCouplings.helicityCoupling_sq]
  linear_combination add_helicitySign_mul_mul_dSigmaDxDQ2_true_add_false K M x Q2 y F1 F2 F3
    (η ^ 2 * (ℓ.gV ^ 2 + ℓ.gA ^ 2)) (-(2 * η ^ 2 * ℓ.gV * ℓ.gA))

/-- **The helicity difference comes from `Z` exchange alone.** The pure-photon term cancels from
`σ_R - σ_L`, which is the sum of the helicity differences of the interference and pure-`Z`
terms. -/
theorem neutralCurrent_true_sub_false :
    neutralCurrent K M x Q2 y q η ℓ H true - neutralCurrent K M x Q2 y q η ℓ H false =
      (gammaZTerm K M x Q2 y q η ℓ true H.gammaZF1 H.gammaZF2 H.gammaZF3
          - gammaZTerm K M x Q2 y q η ℓ false H.gammaZF1 H.gammaZF2 H.gammaZF3)
        + (zBosonTerm K M x Q2 y η ℓ true H.zBosonF1 H.zBosonF2 H.zBosonF3
          - zBosonTerm K M x Q2 y η ℓ false H.zBosonF1 H.zBosonF2 H.zBosonF3) := by
  rw [neutralCurrent_eq_add, neutralCurrent_eq_add]
  ring

/-- **The unpolarised cross section.** The helicity average of the neutral-current cross section,
for a beam of either charge, is the inclusive cross section at the fixed sign `-1` of the
parity-odd term, the charge dependence being carried by `q` inside the effective structure
functions `q² F_i^γ + q g_V η F_i^{γZ} + (g_V² + g_A²) η² F_i^Z` for
`i = 1, 2` and `q g_A η F₃^{γZ} + 2 g_V g_A η² F₃^Z`. -/
theorem neutralCurrent_true_add_false_div_two :
    (neutralCurrent K M x Q2 y q η ℓ H true + neutralCurrent K M x Q2 y q η ℓ H false) / 2 =
      dSigmaDxDQ2 K M (-1) x Q2 y
        (q ^ 2 * H.photonF1 + q * ℓ.gV * η * H.gammaZF1
          + (ℓ.gV ^ 2 + ℓ.gA ^ 2) * η ^ 2 * H.zBosonF1)
        (q ^ 2 * H.photonF2 + q * ℓ.gV * η * H.gammaZF2
          + (ℓ.gV ^ 2 + ℓ.gA ^ 2) * η ^ 2 * H.zBosonF2)
        (q * ℓ.gA * η * H.gammaZF3 + 2 * ℓ.gV * ℓ.gA * η ^ 2 * H.zBosonF3) := by
  simp only [neutralCurrent_def, dSigmaDxDQ2_def, crossSectionBracket_def,
    FermionNeutralCurrentCouplings.helicityCoupling_def, helicitySign_true, helicitySign_false]
  ring

/-- **The electron's interference asymmetry.** For the Standard Model electron (`q = -1`,
`g_V = -1/2 + 2 sin²θ_W`, `g_A = -1/2`) the helicity difference of the interference term is
`-η (K / (x Q²)) (B^{γZ} + (1 - 4 sin²θ_W) Y₋ x F₃^{γZ})`: the parity-odd structure function
enters suppressed by the electron weak charge `Q_W^e = 1 - 4 sin²θ_W`. -/
theorem gammaZTerm_electron_true_sub_false (s2 : ℝ) :
    gammaZTerm K M x Q2 y (-1) η (smTreeLevelCouplings s2).electron true F1 F2 F3
        - gammaZTerm K M x Q2 y (-1) η (smTreeLevelCouplings s2).electron false F1 F2 F3 =
      -η * (K / (x * Q2)) *
        (crossSectionBracket M 0 x Q2 y F1 F2 0
          + electronWeakCharge s2 * (Yminus y * (x * F3))) := by
  rw [gammaZTerm_true_sub_false, smTreeLevelCouplings_electron, electronWeakCharge]
  ring

end CrossSection

end EpsilonEridani.QFT.Scattering.DIS.PVES
