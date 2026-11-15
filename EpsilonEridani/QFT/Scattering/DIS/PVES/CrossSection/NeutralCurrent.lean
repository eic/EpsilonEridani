/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.QFT.Scattering.DIS.Inclusive.CrossSection
public import EpsilonEridani.QFT.Scattering.DIS.PVES.Electroweak.PropagatorRatio
public import EpsilonEridani.QFT.Scattering.DIS.PVES.Interference.Basic

/-!
# The electroweak neutral-current cross section and its three terms

A charged lepton scatters off a nucleon by exchanging a photon or a `Z` boson. The amplitude is
the sum of the two exchange amplitudes, so the cross section is a quadratic form in them: a
pure-photon term, a photon-`Z` interference term and a pure-`Z` term. This file writes the
neutral-current cross section of a massless lepton of definite helicity in that form, each term
the product of a propagator factor, a coupling factor and the contraction
`Inclusive.dSigmaDxDQ2` of the leptonic tensor with the hadronic structure functions of the
corresponding pair of currents, and proves how each term behaves under reversal of the beam
helicity.

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

The relative normalisation of the two exchanges is the real number `η`, the ratio of the
`Z`-exchange to the photon-exchange propagator-and-coupling factor
(`Electroweak.zToPhotonRatio`); at tree level `η = Q² / (4 sin²θ_W cos²θ_W (Q² + M_Z²))`
(`Electroweak.zToPhotonRatio_eq`).

## Main results

* `CrossSection.neutralCurrent_eq_add`: by the linearity of `Inclusive.dSigmaDxDQ2` in the
  structure functions, the defining expression of `neutralCurrent` regroups into the sum of
  `photonTerm`, `gammaZTerm` and `zBosonTerm`, with coupling factors `q²`, `q (g_V - λ g_A)` and
  `(g_V - λ g_A)²` and propagator factors `1`, `η` and `η²`. The three terms are the
  `photon`, `gammaZInterference` and `zBoson` fields of
  `CrossSection.neutralCurrentDecomposition`, an `Electroweak.NeutralCurrentDecomposition`.
* `CrossSection.photonTerm_eq_sq_mul_loNCdSigma`: at zero target mass and with the Callan-Gross
  relation, the pure-photon term is `q²` times the one-photon-exchange cross section
  `loNCdSigma` of `EpsilonEridani.QFT.Scattering.DIS.CrossSection`; for a beam of unit charge
  there is no residual factor (`CrossSection.photonTerm_eq_loNCdSigma`), and
  `CrossSection.neutralCurrent_eq_loNCdSigma_of_eta_zero` recovers it from the full cross
  section when the `Z` exchange is switched off.
* `CrossSection.neutralCurrent_true_sub_false`: the pure-photon term does not depend on the
  helicity, so the helicity difference `σ_R - σ_L` is carried by the interference and pure-`Z`
  terms alone. `CrossSection.gammaZTerm_true_sub_false` and
  `CrossSection.zBosonTerm_true_sub_false` give each piece explicitly: the parity-even
  structure functions enter the interference difference through `g_A` and the parity-odd one
  through `g_V`.
* `CrossSection.gammaZTerm_true_add_false` and `CrossSection.zBosonTerm_true_add_false`: the
  helicity-even parts. The interference term is therefore not purely odd: its even part is
  `η q (K / (x Q²)) (g_V B^{γZ} + g_A Y₋ x F₃^{γZ})`, with `B^{γZ}` the parity-even bracket.
* `CrossSection.neutralCurrent_true_add_false_div_two`: the helicity average is the unpolarised
  cross section `Inclusive.dSigmaDxDQ2` with the electron sign `-1`, with the familiar effective
  structure functions `q² F^γ + q g_V η F^{γZ} + (g_V² + g_A²) η² F^Z` and
  `q g_A η F₃^{γZ} + 2 g_V g_A η² F₃^Z`.
* `CrossSection.gammaZTerm_electron_true_sub_false`: for the Standard Model electron,
  `σ_R - σ_L` of the interference term is `-η K/(xQ²) (B^{γZ} + Q_W^e Y₋ x F₃^{γZ})`, which
  exhibits the suppression of the parity-odd structure function by the electron weak charge
  `Q_W^e = 1 - 4 sin²θ_W` (`Electroweak.electronWeakCharge`).

## Conventions

The kinematic variables, the target mass `M`, the inelasticity factors `Y₊`, `Y₋` and the flux
factor `K = 2π α² / Q²` are those of `Inclusive.CrossSection`. The helicity is a `Bool`, read
through `Interference.helicitySign`: `true` is right-handed (`λ = 1`) and `false` left-handed
(`λ = -1`). The couplings `g_V`, `g_A` are in the normalisation of
`Electroweak.FermionNeutralCurrentCouplings.ofQuantumNumbers`. The interference structure
functions `F_i^{γZ}` are those of the full interference term of the squared amplitude, so they
include both orderings of the two currents; at leading order
`F₂^{γZ} = 2 x Σ_f e_f g_V^f (f + f_bar)`, with `f_bar` the antiparton density. The hadronic
structure functions are inputs at a fixed kinematic point; their definitions and parton content
are not developed here.

## References

* H1 and ZEUS Collaborations, *Combination of measurements of inclusive deep inelastic
  e±p scattering cross sections and QCD analysis of HERA data*, Eur. Phys. J. C **75** (2015)
  580, section 2, for the polarised neutral-current cross section in this form.
* Particle Data Group, *Review of Particle Physics*, section "Structure functions".
-/

public section

noncomputable section

namespace EpsilonEridani.QFT.Scattering.DIS.PVES

open Inclusive Interference

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

variable (α M x Q2 y q η : ℝ) (ℓ : FermionNeutralCurrentCouplings)
  (H : NeutralCurrentStructureFunctions) (h : Bool)

/-- The neutral-current cross section `d²σ/dx dQ²` of a massless lepton of charge `q`,
neutral-current couplings `ℓ` and helicity `helicitySign h`, at `Z`-to-photon propagator ratio
`η`. It is the contraction `Inclusive.dSigmaDxDQ2` of the helicity-projected leptonic tensor
with the structure functions of the summed amplitude,
`F_i = q² F_i^γ + q (η c_Z) F_i^{γZ} + (η c_Z)² F_i^Z` with `c_Z = g_V - λ g_A`. -/
def neutralCurrent : ℝ :=
  dSigmaDxDQ2 (2 * Real.pi * α ^ 2 / Q2) M (helicitySign h) x Q2 y
    (q ^ 2 * H.photonF1 + q * (η * ℓ.helicityCoupling h) * H.gammaZF1
      + (η * ℓ.helicityCoupling h) ^ 2 * H.zBosonF1)
    (q ^ 2 * H.photonF2 + q * (η * ℓ.helicityCoupling h) * H.gammaZF2
      + (η * ℓ.helicityCoupling h) ^ 2 * H.zBosonF2)
    (q * (η * ℓ.helicityCoupling h) * H.gammaZF3 + (η * ℓ.helicityCoupling h) ^ 2 * H.zBosonF3)

theorem neutralCurrent_def :
    neutralCurrent α M x Q2 y q η ℓ H h =
      dSigmaDxDQ2 (2 * Real.pi * α ^ 2 / Q2) M (helicitySign h) x Q2 y
        (q ^ 2 * H.photonF1 + q * (η * ℓ.helicityCoupling h) * H.gammaZF1
          + (η * ℓ.helicityCoupling h) ^ 2 * H.zBosonF1)
        (q ^ 2 * H.photonF2 + q * (η * ℓ.helicityCoupling h) * H.gammaZF2
          + (η * ℓ.helicityCoupling h) ^ 2 * H.zBosonF2)
        (q * (η * ℓ.helicityCoupling h) * H.gammaZF3
          + (η * ℓ.helicityCoupling h) ^ 2 * H.zBosonF3) :=
  (rfl)

/-- The pure-photon term of the neutral-current cross section: coupling factor `q²`, propagator
factor `1`, and the contraction with the electromagnetic structure functions. It has no
parity-odd structure function, so the sign slot of `Inclusive.dSigmaDxDQ2` is immaterial
(`photonTerm_eq_sq_mul_dSigmaDxDQ2`) and the term does not depend on the beam helicity. -/
def photonTerm : ℝ :=
  q ^ 2 * dSigmaDxDQ2 (2 * Real.pi * α ^ 2 / Q2) M 0 x Q2 y H.photonF1 H.photonF2 0

theorem photonTerm_def :
    photonTerm α M x Q2 y q H =
      q ^ 2 * dSigmaDxDQ2 (2 * Real.pi * α ^ 2 / Q2) M 0 x Q2 y H.photonF1 H.photonF2 0 :=
  (rfl)

/-- The photon-`Z` interference term of the neutral-current cross section: coupling factor
`q (g_V - λ g_A)`, propagator factor `η`, and the contraction with the interference structure
functions. -/
def gammaZTerm : ℝ :=
  η * (q * ℓ.helicityCoupling h) *
    dSigmaDxDQ2 (2 * Real.pi * α ^ 2 / Q2) M (helicitySign h) x Q2 y
      H.gammaZF1 H.gammaZF2 H.gammaZF3

theorem gammaZTerm_def :
    gammaZTerm α M x Q2 y q η ℓ H h =
      η * (q * ℓ.helicityCoupling h) *
        dSigmaDxDQ2 (2 * Real.pi * α ^ 2 / Q2) M (helicitySign h) x Q2 y
          H.gammaZF1 H.gammaZF2 H.gammaZF3 :=
  (rfl)

/-- The pure-`Z` term of the neutral-current cross section: coupling factor `(g_V - λ g_A)²`,
propagator factor `η²`, and the contraction with the `Z` structure functions. -/
def zBosonTerm : ℝ :=
  η ^ 2 * ℓ.helicityCoupling h ^ 2 *
    dSigmaDxDQ2 (2 * Real.pi * α ^ 2 / Q2) M (helicitySign h) x Q2 y
      H.zBosonF1 H.zBosonF2 H.zBosonF3

theorem zBosonTerm_def :
    zBosonTerm α M x Q2 y η ℓ H h =
      η ^ 2 * ℓ.helicityCoupling h ^ 2 *
        dSigmaDxDQ2 (2 * Real.pi * α ^ 2 / Q2) M (helicitySign h) x Q2 y
          H.zBosonF1 H.zBosonF2 H.zBosonF3 :=
  (rfl)

/-- The pure-photon term is the electromagnetic contraction for every value of the sign of the
parity-odd term, since its parity-odd structure function vanishes. -/
theorem photonTerm_eq_sq_mul_dSigmaDxDQ2 (s : ℝ) :
    photonTerm α M x Q2 y q H =
      q ^ 2 * dSigmaDxDQ2 (2 * Real.pi * α ^ 2 / Q2) M s x Q2 y H.photonF1 H.photonF2 0 := by
  rw [photonTerm_def, dSigmaDxDQ2_def, dSigmaDxDQ2_def,
    crossSectionBracket_eq_sign_zero_sub M s, mul_zero, mul_zero, sub_zero]

/-- **The three terms.** The defining expression of the neutral-current cross section, a single
contraction with the coupling-weighted structure functions of the three pairs of currents,
regroups by linearity into the sum of the pure-photon, interference and pure-`Z` terms. The
pure-photon term may carry the sign slot `0` of `photonTerm` because its parity-odd structure
function vanishes (`photonTerm_eq_sq_mul_dSigmaDxDQ2`). -/
theorem neutralCurrent_eq_add :
    neutralCurrent α M x Q2 y q η ℓ H h =
      photonTerm α M x Q2 y q H + gammaZTerm α M x Q2 y q η ℓ H h
        + zBosonTerm α M x Q2 y η ℓ H h := by
  rw [photonTerm_eq_sq_mul_dSigmaDxDQ2 _ _ _ _ _ _ _ (helicitySign h), gammaZTerm_def,
    zBosonTerm_def, ← dSigmaDxDQ2_const_mul, ← dSigmaDxDQ2_const_mul, ← dSigmaDxDQ2_const_mul,
    ← dSigmaDxDQ2_add, ← dSigmaDxDQ2_add, neutralCurrent_def]
  congr 1 <;> ring

/-- The three terms of the neutral-current cross section at a fixed coupling, propagator ratio
and helicity, as the `photon`, `zBoson` and `gammaZInterference` fields of an
`Electroweak.NeutralCurrentDecomposition` over the Bjorken variable and the inelasticity. -/
def neutralCurrentDecomposition : NeutralCurrentDecomposition where
  photon x y := photonTerm α M x Q2 y q H
  zBoson x y := zBosonTerm α M x Q2 y η ℓ H h
  gammaZInterference x y := gammaZTerm α M x Q2 y q η ℓ H h

/-- The total of `neutralCurrentDecomposition` is the neutral-current cross section. -/
theorem totalNeutralCurrent_neutralCurrentDecomposition :
    totalNeutralCurrent (neutralCurrentDecomposition α M Q2 q η ℓ H h) x y =
      neutralCurrent α M x Q2 y q η ℓ H h := by
  rw [totalNeutralCurrent_decompose, neutralCurrent_eq_add]
  exact add_right_comm _ _ _

/-- At zero target mass and with electromagnetic structure functions obeying the Callan-Gross
relation, the pure-photon term is `q²` times the one-photon-exchange cross section
`loNCdSigma`. -/
theorem photonTerm_eq_sq_mul_loNCdSigma
    (hCG : Tensors.Longitudinal.IsCallanGross x H.photonF1 H.photonF2) :
    photonTerm α 0 x Q2 y q H = q ^ 2 * loNCdSigma α x Q2 y H.photonF2 := by
  rw [photonTerm_eq_sq_mul_dSigmaDxDQ2 _ _ _ _ _ _ _ 0,
    dSigmaDxDQ2_eq_loNCdSigma _ _ _ _ _ _ _ hCG]

/-- **The pure-photon term is the one-photon-exchange cross section.** For a beam of unit charge,
zero target mass and electromagnetic structure functions obeying the Callan-Gross relation, it
is `loNCdSigma`, with no residual factor. -/
theorem photonTerm_eq_loNCdSigma {q : ℝ} (hq : q ^ 2 = 1)
    (hCG : Tensors.Longitudinal.IsCallanGross x H.photonF1 H.photonF2) :
    photonTerm α 0 x Q2 y q H = loNCdSigma α x Q2 y H.photonF2 := by
  rw [photonTerm_eq_sq_mul_loNCdSigma _ _ _ _ _ _ hCG, hq, one_mul]

/-- Without `Z` exchange the interference term vanishes. -/
@[simp]
theorem gammaZTerm_eta_zero : gammaZTerm α M x Q2 y q 0 ℓ H h = 0 := by
  rw [gammaZTerm_def, zero_mul, zero_mul]

/-- Without `Z` exchange the pure-`Z` term vanishes. -/
@[simp]
theorem zBosonTerm_eta_zero : zBosonTerm α M x Q2 y 0 ℓ H h = 0 := by
  rw [zBosonTerm_def, zero_pow two_ne_zero, zero_mul, zero_mul]

/-- Without `Z` exchange the neutral-current cross section is its pure-photon term. -/
@[simp]
theorem neutralCurrent_eta_zero :
    neutralCurrent α M x Q2 y q 0 ℓ H h = photonTerm α M x Q2 y q H := by
  rw [neutralCurrent_eq_add, gammaZTerm_eta_zero, zBosonTerm_eta_zero, add_zero, add_zero]

/-- **The electromagnetic limit.** Switching off the `Z` exchange, a beam of unit charge at zero
target mass and with Callan-Gross structure functions has the one-photon-exchange cross section
`loNCdSigma`, whatever its helicity and its neutral-current couplings. -/
theorem neutralCurrent_eq_loNCdSigma_of_eta_zero {q : ℝ} (hq : q ^ 2 = 1)
    (hCG : Tensors.Longitudinal.IsCallanGross x H.photonF1 H.photonF2) :
    neutralCurrent α 0 x Q2 y q 0 ℓ H h = loNCdSigma α x Q2 y H.photonF2 := by
  rw [neutralCurrent_eta_zero, photonTerm_eq_loNCdSigma _ _ _ _ _ hq hCG]

/-- The helicity difference of the interference term. The parity-even structure functions enter
through the axial coupling and the parity-odd one through the vector coupling:
`σ_R - σ_L = -2 η q (K / (x Q²)) (g_A B^{γZ} + g_V Y₋ x F₃^{γZ})`, with `B^{γZ}` the
parity-even part of the bracket. -/
theorem gammaZTerm_true_sub_false :
    gammaZTerm α M x Q2 y q η ℓ H true - gammaZTerm α M x Q2 y q η ℓ H false =
      -2 * η * q * (2 * Real.pi * α ^ 2 / Q2 / (x * Q2)) *
        (ℓ.gA * crossSectionBracket M 0 x Q2 y H.gammaZF1 H.gammaZF2 0
          + ℓ.gV * (Yminus y * (x * H.gammaZF3))) := by
  simp only [gammaZTerm_def, FermionNeutralCurrentCouplings.helicityCoupling_def, dSigmaDxDQ2_def,
    helicitySign_true, helicitySign_false]
  rw [crossSectionBracket_eq_sign_zero_sub M 1, crossSectionBracket_eq_sign_zero_sub M (-1)]
  ring

/-- The helicity sum of the interference term:
`σ_R + σ_L = 2 η q (K / (x Q²)) (g_V B^{γZ} + g_A Y₋ x F₃^{γZ})`. The interference term is
therefore odd under helicity reversal only where this combination vanishes. -/
theorem gammaZTerm_true_add_false :
    gammaZTerm α M x Q2 y q η ℓ H true + gammaZTerm α M x Q2 y q η ℓ H false =
      2 * η * q * (2 * Real.pi * α ^ 2 / Q2 / (x * Q2)) *
        (ℓ.gV * crossSectionBracket M 0 x Q2 y H.gammaZF1 H.gammaZF2 0
          + ℓ.gA * (Yminus y * (x * H.gammaZF3))) := by
  simp only [gammaZTerm_def, FermionNeutralCurrentCouplings.helicityCoupling_def, dSigmaDxDQ2_def,
    helicitySign_true, helicitySign_false]
  rw [crossSectionBracket_eq_sign_zero_sub M 1, crossSectionBracket_eq_sign_zero_sub M (-1)]
  ring

/-- The helicity difference of the pure-`Z` term:
`σ_R - σ_L = -2 η² (K / (x Q²)) (2 g_V g_A B^Z + (g_V² + g_A²) Y₋ x F₃^Z)`. -/
theorem zBosonTerm_true_sub_false :
    zBosonTerm α M x Q2 y η ℓ H true - zBosonTerm α M x Q2 y η ℓ H false =
      -2 * η ^ 2 * (2 * Real.pi * α ^ 2 / Q2 / (x * Q2)) *
        (2 * ℓ.gV * ℓ.gA * crossSectionBracket M 0 x Q2 y H.zBosonF1 H.zBosonF2 0
          + (ℓ.gV ^ 2 + ℓ.gA ^ 2) * (Yminus y * (x * H.zBosonF3))) := by
  simp only [zBosonTerm_def, FermionNeutralCurrentCouplings.helicityCoupling_def, dSigmaDxDQ2_def,
    helicitySign_true, helicitySign_false]
  rw [crossSectionBracket_eq_sign_zero_sub M 1, crossSectionBracket_eq_sign_zero_sub M (-1)]
  ring

/-- The helicity sum of the pure-`Z` term:
`σ_R + σ_L = 2 η² (K / (x Q²)) ((g_V² + g_A²) B^Z + 2 g_V g_A Y₋ x F₃^Z)`. -/
theorem zBosonTerm_true_add_false :
    zBosonTerm α M x Q2 y η ℓ H true + zBosonTerm α M x Q2 y η ℓ H false =
      2 * η ^ 2 * (2 * Real.pi * α ^ 2 / Q2 / (x * Q2)) *
        ((ℓ.gV ^ 2 + ℓ.gA ^ 2) * crossSectionBracket M 0 x Q2 y H.zBosonF1 H.zBosonF2 0
          + 2 * ℓ.gV * ℓ.gA * (Yminus y * (x * H.zBosonF3))) := by
  simp only [zBosonTerm_def, FermionNeutralCurrentCouplings.helicityCoupling_def, dSigmaDxDQ2_def,
    helicitySign_true, helicitySign_false]
  rw [crossSectionBracket_eq_sign_zero_sub M 1, crossSectionBracket_eq_sign_zero_sub M (-1)]
  ring

/-- **The helicity difference comes from `Z` exchange alone.** The pure-photon term cancels from
`σ_R - σ_L`, which is the sum of the helicity differences of the interference and pure-`Z`
terms. -/
theorem neutralCurrent_true_sub_false :
    neutralCurrent α M x Q2 y q η ℓ H true - neutralCurrent α M x Q2 y q η ℓ H false =
      (gammaZTerm α M x Q2 y q η ℓ H true - gammaZTerm α M x Q2 y q η ℓ H false)
        + (zBosonTerm α M x Q2 y η ℓ H true - zBosonTerm α M x Q2 y η ℓ H false) := by
  rw [neutralCurrent_eq_add, neutralCurrent_eq_add]
  ring

/-- **The unpolarised cross section.** The helicity average of the neutral-current cross section
is the inclusive cross section with the electron sign `-1` of the parity-odd term and the
effective structure functions `q² F_i^γ + q g_V η F_i^{γZ} + (g_V² + g_A²) η² F_i^Z` for
`i = 1, 2` and `q g_A η F₃^{γZ} + 2 g_V g_A η² F₃^Z`. -/
theorem neutralCurrent_true_add_false_div_two :
    (neutralCurrent α M x Q2 y q η ℓ H true + neutralCurrent α M x Q2 y q η ℓ H false) / 2 =
      dSigmaDxDQ2 (2 * Real.pi * α ^ 2 / Q2) M (-1) x Q2 y
        (q ^ 2 * H.photonF1 + q * ℓ.gV * η * H.gammaZF1
          + (ℓ.gV ^ 2 + ℓ.gA ^ 2) * η ^ 2 * H.zBosonF1)
        (q ^ 2 * H.photonF2 + q * ℓ.gV * η * H.gammaZF2
          + (ℓ.gV ^ 2 + ℓ.gA ^ 2) * η ^ 2 * H.zBosonF2)
        (q * ℓ.gA * η * H.gammaZF3 + 2 * ℓ.gV * ℓ.gA * η ^ 2 * H.zBosonF3) := by
  -- The parity-even bracket of the effective structure functions, split by linearity.
  have hB : crossSectionBracket M 0 x Q2 y
        (q ^ 2 * H.photonF1 + q * ℓ.gV * η * H.gammaZF1
          + (ℓ.gV ^ 2 + ℓ.gA ^ 2) * η ^ 2 * H.zBosonF1)
        (q ^ 2 * H.photonF2 + q * ℓ.gV * η * H.gammaZF2
          + (ℓ.gV ^ 2 + ℓ.gA ^ 2) * η ^ 2 * H.zBosonF2) 0 =
      q ^ 2 * crossSectionBracket M 0 x Q2 y H.photonF1 H.photonF2 0
        + q * ℓ.gV * η * crossSectionBracket M 0 x Q2 y H.gammaZF1 H.gammaZF2 0
        + (ℓ.gV ^ 2 + ℓ.gA ^ 2) * η ^ 2
          * crossSectionBracket M 0 x Q2 y H.zBosonF1 H.zBosonF2 0 := by
    rw [← crossSectionBracket_const_mul, ← crossSectionBracket_const_mul,
      ← crossSectionBracket_const_mul, ← crossSectionBracket_add, ← crossSectionBracket_add,
      mul_zero, mul_zero, mul_zero, add_zero, add_zero]
  rw [neutralCurrent_eq_add, neutralCurrent_eq_add, photonTerm_def, dSigmaDxDQ2_def,
    dSigmaDxDQ2_def, crossSectionBracket_eq_sign_zero_sub M (-1), hB]
  linear_combination (gammaZTerm_true_add_false α M x Q2 y q η ℓ H
    + zBosonTerm_true_add_false α M x Q2 y η ℓ H) / 2

/-- **The electron's interference asymmetry.** For the Standard Model electron (`q = -1`,
`g_V = -1/2 + 2 sin²θ_W`, `g_A = -1/2`) the helicity difference of the interference term is
`-η (K / (x Q²)) (B^{γZ} + (1 - 4 sin²θ_W) Y₋ x F₃^{γZ})`: the parity-odd structure function
enters suppressed by the electron weak charge `Q_W^e = 1 - 4 sin²θ_W`. -/
theorem gammaZTerm_electron_true_sub_false (s2 : ℝ) :
    gammaZTerm α M x Q2 y (-1) η (smTreeLevelCouplings s2).electron H true
        - gammaZTerm α M x Q2 y (-1) η (smTreeLevelCouplings s2).electron H false =
      -η * (2 * Real.pi * α ^ 2 / Q2 / (x * Q2)) *
        (crossSectionBracket M 0 x Q2 y H.gammaZF1 H.gammaZF2 0
          + electronWeakCharge s2 * (Yminus y * (x * H.gammaZF3))) := by
  rw [gammaZTerm_true_sub_false, smTreeLevelCouplings_electron, electronWeakCharge]
  ring

end CrossSection

end EpsilonEridani.QFT.Scattering.DIS.PVES
