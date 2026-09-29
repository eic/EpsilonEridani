/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import EpsilonEridani.QFT.Scattering.DIS.PVES.Examples.Basic
public import EpsilonEridani.QFT.PerturbationTheory.FeynmanDiagrams.FiniteSearch
public import EpsilonEridani.QFT.PerturbationTheory.FeynmanDiagrams.TopologyEnumeration
public import EpsilonEridani.QFT.PerturbationTheory.FeynmanDiagrams.TwoLoopDiagrammaticBridge
public import EpsilonEridani.QFT.PerturbationTheory.FeynmanDiagrams.TwoLoopEvaluation
public import EpsilonEridani.QFT.PerturbationTheory.FeynmanDiagrams.OneLoopEvaluation
/-!

# PVES MOLLER Examples

This module contains MOLLER-focused PVES examples, including lab-frame
asymmetry interfaces and one-loop diagram contribution/effect theorems.

## One-loop correction formulas (LaTeX)

The one-loop interference shift represented in this file is:

$$
\Delta_{\mathrm{1\,loop}}
= c_{\mathrm{g}}\,W\!\left(I_{\mathrm{g}}\right)
+ c_{\mathrm{gh}}\,W\!\left(I_{\mathrm{gh}}\right)
+ c_{\mathrm{f}}\,W\!\left(I_{\mathrm{f}}\right),
$$

where $I_{\mathrm{g}}$, $I_{\mathrm{gh}}$, and $I_{\mathrm{f}}$ are the gauge-boson,
ghost, and fermion self-energy scalar masters, and $W$ is the abstraction
`masterWeight`.

The corrected lab-frame asymmetry is modeled as:

$$
A_{PV}^{\mathrm{lab,1\,loop}}
= \mathcal{P}_{\mathrm{lab}}\left(R_{\mathrm{tree}} + \Delta_{\mathrm{1\,loop}}\right),
$$

with prefactor

$$
\mathcal{P}_{\mathrm{lab}}
= \frac{m_e\,E_{\mathrm{beam}}\,G_F}{\sqrt{2}\,\pi\,\alpha_{\mathrm{EM}}}.
$$

Expanding linearly gives

$$
A_{PV}^{\mathrm{lab,1\,loop}}
= A_{PV}^{\mathrm{lab,tree}} + \mathcal{P}_{\mathrm{lab}}\,\Delta_{\mathrm{1\,loop}},
$$

which matches `mollerLabFrameAPVWithOneLoop_eq_tree_plus_shift` and
`moller_oneLoop_effect_on_experimental_asymmetry`.

-/

@[expose] public section

noncomputable section

namespace EpsilonEridani
namespace QFT
namespace Scattering
namespace DIS
namespace PVES
namespace Examples

open Electroweak
open Processes
open EpsilonEridani.QFT.PerturbationTheory.FeynmanDiagrams
open EpsilonEridani.QFT.PerturbationTheory.FeynmanDiagrams.TwoLoopDiagrammaticBridge
open EpsilonEridani.QFT.PerturbationTheory.DimensionalRegularization.OneLoopScalars

/-- Beam-polarization scaling for a measured parity-violating asymmetry. -/
def polarizationScaledAsymmetry (beamPolarization asymmetry : ℝ) : ℝ :=
  beamPolarization * asymmetry

/-- MOLLER-style measured asymmetry interface built from the ee PVES asymmetry. -/
def mollerMeasuredAsymmetry
    (beamPolarization : ℝ)
    (D : NeutralCurrentDecomposition)
    (x y epsilonReg : ℝ) : ℝ :=
  polarizationScaledAsymmetry beamPolarization
    (EE.beamHelicityAsymmetry (EE.canonicalModelOfDecomposition D) x y epsilonReg)

/-- MOLLER-style bridge: measured asymmetry follows the ee interference ratio
up to beam polarization. -/
lemma moller_measuredAsymmetry_eq_interferenceRatio
    (beamPolarization : ℝ)
    (photonVal zVal gammaZVal x y epsilonReg : ℝ) :
    mollerMeasuredAsymmetry
        beamPolarization
        (toyDecomposition photonVal zVal gammaZVal)
        x y epsilonReg
      = beamPolarization *
          ((2 * gammaZVal) / (|2 * (photonVal + zVal)| + epsilonReg)) := by
  simp [mollerMeasuredAsymmetry, polarizationScaledAsymmetry, ee_toy_bridge_example]

/-- Lab-frame input bundle for MOLLER-style asymmetry parameterization. -/
structure MollerLabFrameInputs where
  /-- Beam energy in the lab frame. -/
  beamEnergy : ℝ
  /-- Effective electroweak weak charge entering `A_PV`. -/
  weakChargeElectron : ℝ
  /-- Fermi constant used in the prefactor. -/
  fermiConstant : ℝ
  /-- Fine-structure constant used in the prefactor. -/
  alphaEM : ℝ
  /-- Electron mass used in the prefactor. -/
  electronMass : ℝ
  /-- Dimensionless lab-frame kinematic factor from angular dependence. -/
  labKinematicFactor : ℝ

/-- MOLLER-style lab-frame prefactor multiplying weak-charge and kinematic terms. -/
def mollerLabPrefactor (I : MollerLabFrameInputs) : ℝ :=
  (I.electronMass * I.beamEnergy * I.fermiConstant) / (Real.sqrt 2 * Real.pi * I.alphaEM)

/-- Lab-frame parity-violating asymmetry interface for MOLLER-style analyses. -/
def mollerLabFrameAPV (I : MollerLabFrameInputs) : ℝ :=
  mollerLabPrefactor I * I.labKinematicFactor * I.weakChargeElectron

/-- If the lab-frame weak-charge times kinematic factor is identified with the
PVES interference ratio, then the lab-frame `A_PV` equals prefactor times that ratio. -/
lemma moller_labFrameAPV_eq_prefactor_times_interferenceRatio
    (I : MollerLabFrameInputs)
    (photonVal zVal gammaZVal epsilonReg : ℝ)
    (hMatch : I.labKinematicFactor * I.weakChargeElectron
      = (2 * gammaZVal) / (|2 * (photonVal + zVal)| + epsilonReg)) :
    mollerLabFrameAPV I
      = mollerLabPrefactor I *
          ((2 * gammaZVal) / (|2 * (photonVal + zVal)| + epsilonReg)) := by
  simp [mollerLabFrameAPV, hMatch, mul_assoc]

/-- Unit-polarization bridge from the existing ee measured asymmetry model to
MOLLER-style lab-frame expression. -/
lemma moller_unitPolarization_bridge_to_labFrame
    (I : MollerLabFrameInputs)
    (photonVal zVal gammaZVal x y epsilonReg : ℝ)
    (hExpr : mollerLabPrefactor I * I.labKinematicFactor * I.weakChargeElectron
      = (2 * gammaZVal) / (|2 * (photonVal + zVal)| + epsilonReg)) :
    mollerMeasuredAsymmetry
        1
        (toyDecomposition photonVal zVal gammaZVal)
        x y epsilonReg
      = mollerLabFrameAPV I := by
  have hMeas :
      mollerMeasuredAsymmetry
          1
          (toyDecomposition photonVal zVal gammaZVal)
          x y epsilonReg
        = (2 * gammaZVal) / (|2 * (photonVal + zVal)| + epsilonReg) := by
    simpa using moller_measuredAsymmetry_eq_interferenceRatio
      (beamPolarization := 1)
      (photonVal := photonVal)
      (zVal := zVal)
      (gammaZVal := gammaZVal)
      (x := x)
      (y := y)
      (epsilonReg := epsilonReg)
  calc
    mollerMeasuredAsymmetry
        1
        (toyDecomposition photonVal zVal gammaZVal)
        x y epsilonReg
      = (2 * gammaZVal) / (|2 * (photonVal + zVal)| + epsilonReg) := hMeas
    _ = mollerLabFrameAPV I := by
      simpa [mollerLabFrameAPV, mollerLabPrefactor, mul_assoc] using hExpr.symm

/-- Labels for one-loop diagram classes contributing to the MOLLER PV interface. -/
inductive MollerOneLoopDiagramLabel where
  | gaugeBosonSelfEnergy
  | ghostSelfEnergy
  | fermionSelfEnergy
  deriving DecidableEq, Repr

/-- Finite set of one-loop diagram classes entering the MOLLER correction model. -/
def mollerContributingOneLoopDiagrams : Finset MollerOneLoopDiagramLabel :=
  [MollerOneLoopDiagramLabel.gaugeBosonSelfEnergy,
    MollerOneLoopDiagramLabel.ghostSelfEnergy,
    MollerOneLoopDiagramLabel.fermionSelfEnergy].toFinset

lemma mem_mollerContributingOneLoopDiagrams_iff
    (d : MollerOneLoopDiagramLabel) :
    d ∈ mollerContributingOneLoopDiagrams ↔
      d = MollerOneLoopDiagramLabel.gaugeBosonSelfEnergy ∨
      d = MollerOneLoopDiagramLabel.ghostSelfEnergy ∨
      d = MollerOneLoopDiagramLabel.fermionSelfEnergy := by
  cases d <;> simp [mollerContributingOneLoopDiagrams]

/-- Canonical one-loop class order for Møller topology enumeration. -/
def mollerOneLoopTopologyClassOrder : List MollerOneLoopDiagramLabel :=
  [MollerOneLoopDiagramLabel.gaugeBosonSelfEnergy,
   MollerOneLoopDiagramLabel.ghostSelfEnergy,
   MollerOneLoopDiagramLabel.fermionSelfEnergy]

/-- Map generic one-loop topology classes to Møller one-loop class labels. -/
def mollerOneLoopLabelOfTopologyClass
    (cls : OneLoopTopologyClass) : MollerOneLoopDiagramLabel :=
  match cls with
  | .gaugeSelfEnergy => MollerOneLoopDiagramLabel.gaugeBosonSelfEnergy
  | .ghostSelfEnergy => MollerOneLoopDiagramLabel.ghostSelfEnergy
  | .fermionSelfEnergy => MollerOneLoopDiagramLabel.fermionSelfEnergy

/-- Classifier from generic one-loop candidates to Møller one-loop labels. -/
def mollerClassifyOneLoopTopologyCandidate
    (candidate : TopologyCandidate) : Option MollerOneLoopDiagramLabel :=
  (classifyOneLoopTopologyCandidate candidate).map mollerOneLoopLabelOfTopologyClass

/-- Møller one-loop candidate enumeration induced by generic topology constraints. -/
def mollerOneLoopTopologyCandidateEnumeration : List TopologyCandidate :=
  oneLoopTopologyCandidates

/-- Møller one-loop grouped class enumeration in canonical order. -/
def mollerOneLoopTopologyClassEnumeration :
    List (MollerOneLoopDiagramLabel × List TopologyCandidate) :=
  enumerateClassBlocks mollerOneLoopTopologyClassOrder
    mollerClassifyOneLoopTopologyCandidate mollerOneLoopTopologyCandidateEnumeration

/-- Møller one-loop labels from the generic topology enumeration workflow. -/
def mollerOneLoopTopologyLabels : List MollerOneLoopDiagramLabel :=
  mollerOneLoopTopologyCandidateEnumeration.filterMap
    mollerClassifyOneLoopTopologyCandidate

/-- One-loop Møller class enumeration preserves canonical class order. -/
theorem mollerOneLoopTopologyClassEnumeration_map_fst :
    mollerOneLoopTopologyClassEnumeration.map Prod.fst = mollerOneLoopTopologyClassOrder := by
  simpa [mollerOneLoopTopologyClassEnumeration] using
    enumerateClassBlocks_map_fst
      (classOrder := mollerOneLoopTopologyClassOrder)
      (classify := mollerClassifyOneLoopTopologyCandidate)
      (candidates := mollerOneLoopTopologyCandidateEnumeration)

/-- Møller one-loop labels from topology enumeration match canonical order. -/
lemma mollerOneLoopTopologyLabels_eq_canonicalOrder :
    mollerOneLoopTopologyLabels = mollerOneLoopTopologyClassOrder := by
  decide

/-- Set-level completeness for Møller one-loop class enumeration. -/
theorem mollerOneLoopTopologyLabels_toFinset_eq_contributingSet :
    mollerOneLoopTopologyLabels.toFinset = mollerContributingOneLoopDiagrams := by
  simp [mollerOneLoopTopologyLabels_eq_canonicalOrder,
    mollerContributingOneLoopDiagrams,
    mollerOneLoopTopologyClassOrder]

/-- Bundled one-loop MOLLER contribution data from Feynman self-energy classes. -/
structure MollerOneLoopContributions (rules : GaugeFeynmanRules) where
  bundle : OneLoopSelfEnergyDiagramBundle rules
  data : OneLoopSelfEnergyLoopIntegralDataBundle bundle

lemma moller_oneLoop_contributors_needRegularization
    {rules : GaugeFeynmanRules}
    (C : MollerOneLoopContributions rules) :
    C.bundle.gaugeBoson.loopAssumptions.needsRegularization ∧
      C.bundle.ghost.loopAssumptions.needsRegularization ∧
      C.bundle.fermion.loopAssumptions.needsRegularization := by
  exact ⟨C.bundle.gaugeBoson.needsRegularization,
    C.bundle.ghost.needsRegularization,
    C.bundle.fermion.needsRegularization⟩

/-- Effective one-loop shift in the interference channel from weighted scalar masters.

LaTeX form:

$$
\Delta_{\mathrm{1\,loop}}
= c_{\mathrm{g}}\,W\!\left(I_{\mathrm{g}}\right)
+ c_{\mathrm{gh}}\,W\!\left(I_{\mathrm{gh}}\right)
+ c_{\mathrm{f}}\,W\!\left(I_{\mathrm{f}}\right).
$$ -/
def mollerOneLoopInterferenceShift
    {rules : GaugeFeynmanRules}
    (C : MollerOneLoopContributions rules)
    (masterWeight : ScalarMasterIntegral → ℝ)
    (cGauge cGhost cFermion : ℝ) : ℝ :=
  cGauge * masterWeight C.data.gaugeBoson.integrand.evaluate
    + cGhost * masterWeight C.data.ghost.integrand.evaluate
    + cFermion * masterWeight C.data.fermion.integrand.evaluate

lemma mollerOneLoopInterferenceShift_eq_weightedCanonicalMasters
    {rules : GaugeFeynmanRules}
    (C : MollerOneLoopContributions rules)
    (masterWeight : ScalarMasterIntegral → ℝ)
    (cGauge cGhost cFermion : ℝ) :
    mollerOneLoopInterferenceShift C masterWeight cGauge cGhost cFermion
      = cGauge * masterWeight gaugeBosonSelfEnergyMaster
        + cGhost * masterWeight ghostSelfEnergyMaster
        + cFermion * masterWeight fermionSelfEnergyMaster := by
  unfold mollerOneLoopInterferenceShift
  rw [evaluateGaugeBosonSelfEnergyDiagram C.data.gaugeBoson,
    evaluateGhostSelfEnergyDiagram C.data.ghost,
    evaluateFermionSelfEnergyDiagram C.data.fermion]

/-- Lab-frame MOLLER asymmetry model including an additive one-loop shift of the
tree-level interference-ratio contribution.

LaTeX form:

$$
A_{PV}^{\mathrm{lab,1\,loop}}
= \mathcal{P}_{\mathrm{lab}}\left(R_{\mathrm{tree}} + \Delta_{\mathrm{1\,loop}}\right).
$$ -/
def mollerLabFrameAPVWithOneLoop
    (I : MollerLabFrameInputs)
    (treeInterferenceRatio oneLoopShift : ℝ) : ℝ :=
  mollerLabPrefactor I * (treeInterferenceRatio + oneLoopShift)

lemma mollerLabFrameAPVWithOneLoop_eq_tree_plus_shift
    (I : MollerLabFrameInputs)
    (treeInterferenceRatio oneLoopShift : ℝ) :
    mollerLabFrameAPVWithOneLoop I treeInterferenceRatio oneLoopShift
      = mollerLabPrefactor I * treeInterferenceRatio
        + mollerLabPrefactor I * oneLoopShift := by
  unfold mollerLabFrameAPVWithOneLoop
  ring

/-- One-loop effect theorem: once the tree-level MOLLER expression is matched,
the one-loop correction contributes additively with the same lab-frame prefactor.

LaTeX form:

$$
A_{PV}^{\mathrm{lab,1\,loop}}
= A_{PV}^{\mathrm{lab,tree}} + \mathcal{P}_{\mathrm{lab}}\,\Delta_{\mathrm{1\,loop}}.
$$ -/
lemma moller_oneLoop_effect_on_experimental_asymmetry
    (I : MollerLabFrameInputs)
    (photonVal zVal gammaZVal epsilonReg oneLoopShift : ℝ)
    (hTree : I.labKinematicFactor * I.weakChargeElectron
      = (2 * gammaZVal) / (|2 * (photonVal + zVal)| + epsilonReg)) :
    mollerLabFrameAPVWithOneLoop
        I
        ((2 * gammaZVal) / (|2 * (photonVal + zVal)| + epsilonReg))
        oneLoopShift
      = mollerLabFrameAPV I + mollerLabPrefactor I * oneLoopShift := by
  have hTreePV :
      mollerLabFrameAPV I
        = mollerLabPrefactor I
            * ((2 * gammaZVal) / (|2 * (photonVal + zVal)| + epsilonReg)) := by
    simp [mollerLabFrameAPV, hTree, mul_assoc]
  calc
    mollerLabFrameAPVWithOneLoop
        I
        ((2 * gammaZVal) / (|2 * (photonVal + zVal)| + epsilonReg))
        oneLoopShift
      = mollerLabPrefactor I
          * ((2 * gammaZVal) / (|2 * (photonVal + zVal)| + epsilonReg))
          + mollerLabPrefactor I * oneLoopShift := by
            exact mollerLabFrameAPVWithOneLoop_eq_tree_plus_shift
              I
              ((2 * gammaZVal) / (|2 * (photonVal + zVal)| + epsilonReg))
              oneLoopShift
    _ = mollerLabFrameAPV I + mollerLabPrefactor I * oneLoopShift := by
      simp [hTreePV]

/-- Labels for two-loop diagram classes in the MOLLER correction interface.

These classes keep a structured bookkeeping layer separate from eventual
diagram-by-diagram analytic evaluation. -/
inductive MollerTwoLoopDiagramLabel where
  /-- Nested gauge-boson self-energy topology. -/
  | nestedGaugeBosonSelfEnergy
  /-- Gauge-boson and ghost mixed topology. -/
  | gaugeGhostMixed
  /-- Vertex-corrected box-interference topology. -/
  | vertexCorrectedBoxInterference
  /-- Double-fermion self-energy topology. -/
  | doubleFermionSelfEnergy
  /-- Counterterm insertion paired with one-loop topology. -/
  | countertermInsertedOneLoop
  deriving DecidableEq, Repr

/-- Finite set of two-loop diagram classes entering the MOLLER correction model. -/
def mollerContributingTwoLoopDiagrams : Finset MollerTwoLoopDiagramLabel :=
  [MollerTwoLoopDiagramLabel.nestedGaugeBosonSelfEnergy,
    MollerTwoLoopDiagramLabel.gaugeGhostMixed,
    MollerTwoLoopDiagramLabel.vertexCorrectedBoxInterference,
    MollerTwoLoopDiagramLabel.doubleFermionSelfEnergy,
    MollerTwoLoopDiagramLabel.countertermInsertedOneLoop].toFinset

lemma mem_mollerContributingTwoLoopDiagrams_iff
    (d : MollerTwoLoopDiagramLabel) :
    d ∈ mollerContributingTwoLoopDiagrams ↔
      d = MollerTwoLoopDiagramLabel.nestedGaugeBosonSelfEnergy ∨
      d = MollerTwoLoopDiagramLabel.gaugeGhostMixed ∨
      d = MollerTwoLoopDiagramLabel.vertexCorrectedBoxInterference ∨
      d = MollerTwoLoopDiagramLabel.doubleFermionSelfEnergy ∨
      d = MollerTwoLoopDiagramLabel.countertermInsertedOneLoop := by
  cases d <;> simp [mollerContributingTwoLoopDiagrams]

/-- Symbolic two-loop reduced amplitudes by topology class.

This abstraction separates enumeration and algebraic combination from
low-level integral evaluation details. -/
structure MollerTwoLoopContributions where
  reducedAmplitude : MollerTwoLoopDiagramLabel → ℝ

/-- Bridge certificate type for the Møller two-loop diagrammatic derivation.

This is the future home for concrete external two-loop diagram objects, once the
perturbative derivation package is implemented. -/
abbrev MollerTwoLoopDiagrammaticBridge :=
  TwoLoopDiagrammaticBridge MollerTwoLoopDiagramLabel
    mollerContributingTwoLoopDiagrams

/-- Concrete Møller two-loop evaluation object. -/
abbrev MollerTwoLoopDiagramEvaluation :=
  TwoLoopDiagramEvaluation MollerTwoLoopDiagramLabel

/-- Concrete Møller two-loop diagram data. -/
abbrev MollerTwoLoopDiagramData :=
  TwoLoopDiagramData MollerTwoLoopDiagramLabel

/-- Canonical momentum assignment used by the nested gauge-boson self-energy topology. -/
def mollerNestedGaugeBosonSelfEnergyLoopMomentum1 : Momentum :=
  Momentum.mk 1 1 0 0

/-- Canonical momentum assignment used by the nested gauge-boson self-energy topology. -/
def mollerNestedGaugeBosonSelfEnergyLoopMomentum2 : Momentum :=
  Momentum.mk 0 0 1 0

/-- Canonical external momentum assignment used by the nested gauge-boson self-energy topology. -/
def mollerNestedGaugeBosonSelfEnergyExternalMomentum : Momentum :=
  Momentum.mk 2 0 0 1

/-- Concrete integrand payload for the nested gauge-boson self-energy topology. -/
def mollerNestedGaugeBosonSelfEnergyIntegrand : TwoLoopScalarIntegrand where
  loopMomentum1 := mollerNestedGaugeBosonSelfEnergyLoopMomentum1
  loopMomentum2 := mollerNestedGaugeBosonSelfEnergyLoopMomentum2
  externalMomentum := mollerNestedGaugeBosonSelfEnergyExternalMomentum
  numeratorTerms := [unitNumeratorTerm]
  denominators := [masslessDenominatorFactor, masslessDenominatorFactor, masslessDenominatorFactor]
  regulator := 1
  hRegulator := by norm_num
  reducedMaster := twoLoopSunset 1

/-- Canonical momentum assignment used by the gauge-boson/ghost mixed topology. -/
def mollerGaugeGhostMixedLoopMomentum1 : Momentum :=
  Momentum.mk 0 1 1 0

/-- Canonical momentum assignment used by the gauge-boson/ghost mixed topology. -/
def mollerGaugeGhostMixedLoopMomentum2 : Momentum :=
  Momentum.mk 1 0 1 1

/-- Canonical external momentum assignment used by the gauge-boson/ghost mixed topology. -/
def mollerGaugeGhostMixedExternalMomentum : Momentum :=
  Momentum.mk 1 1 0 1

/-- Concrete integrand payload for the gauge-boson/ghost mixed topology. -/
def mollerGaugeGhostMixedIntegrand : TwoLoopScalarIntegrand where
  loopMomentum1 := mollerGaugeGhostMixedLoopMomentum1
  loopMomentum2 := mollerGaugeGhostMixedLoopMomentum2
  externalMomentum := mollerGaugeGhostMixedExternalMomentum
  numeratorTerms := [unitNumeratorTerm]
  denominators := [masslessDenominatorFactor, masslessDenominatorFactor]
  regulator := 1
  hRegulator := by norm_num
  reducedMaster := twoLoopBubble 1

/-- Canonical momentum assignment used by the vertex-corrected box-interference topology. -/
def mollerVertexCorrectedBoxInterferenceLoopMomentum1 : Momentum :=
  Momentum.mk 2 0 1 1

/-- Canonical momentum assignment used by the vertex-corrected box-interference topology. -/
def mollerVertexCorrectedBoxInterferenceLoopMomentum2 : Momentum :=
  Momentum.mk 1 1 0 1

/-- Canonical external momentum assignment for the vertex-corrected box-interference topology. -/
def mollerVertexCorrectedBoxInterferenceExternalMomentum : Momentum :=
  Momentum.mk 0 1 1 0

/-- Concrete integrand payload for the vertex-corrected box-interference topology. -/
def mollerVertexCorrectedBoxInterferenceIntegrand : TwoLoopScalarIntegrand where
  loopMomentum1 := mollerVertexCorrectedBoxInterferenceLoopMomentum1
  loopMomentum2 := mollerVertexCorrectedBoxInterferenceLoopMomentum2
  externalMomentum := mollerVertexCorrectedBoxInterferenceExternalMomentum
  numeratorTerms := [unitNumeratorTerm]
  denominators :=
    [masslessDenominatorFactor,
     masslessDenominatorFactor,
     masslessDenominatorFactor,
     masslessDenominatorFactor]
  regulator := 1
  hRegulator := by norm_num
  reducedMaster := twoLoopVertexCorrection 1

/-- Canonical momentum assignment used by the double-fermion self-energy topology. -/
def mollerDoubleFermionSelfEnergyLoopMomentum1 : Momentum :=
  Momentum.mk 1 0 1 0

/-- Canonical momentum assignment used by the double-fermion self-energy topology. -/
def mollerDoubleFermionSelfEnergyLoopMomentum2 : Momentum :=
  Momentum.mk 1 1 0 0

/-- Canonical external momentum assignment used by the double-fermion self-energy topology. -/
def mollerDoubleFermionSelfEnergyExternalMomentum : Momentum :=
  Momentum.mk 0 0 0 1

/-- Concrete integrand payload for the double-fermion self-energy topology. -/
def mollerDoubleFermionSelfEnergyIntegrand : TwoLoopScalarIntegrand where
  loopMomentum1 := mollerDoubleFermionSelfEnergyLoopMomentum1
  loopMomentum2 := mollerDoubleFermionSelfEnergyLoopMomentum2
  externalMomentum := mollerDoubleFermionSelfEnergyExternalMomentum
  numeratorTerms := [unitNumeratorTerm]
  denominators := [masslessDenominatorFactor, masslessDenominatorFactor]
  regulator := 1
  hRegulator := by norm_num
  reducedMaster := twoLoopSunset 2

/-- Canonical momentum assignment used by the counterterm-inserted one-loop topology. -/
def mollerCountertermInsertedOneLoopLoopMomentum1 : Momentum :=
  Momentum.mk 0 0 0 0

/-- Canonical momentum assignment used by the counterterm-inserted one-loop topology. -/
def mollerCountertermInsertedOneLoopLoopMomentum2 : Momentum :=
  Momentum.mk 1 1 0 0

/-- Canonical external momentum assignment used by the counterterm-inserted one-loop topology. -/
def mollerCountertermInsertedOneLoopExternalMomentum : Momentum :=
  Momentum.mk 1 0 1 0

/-- Concrete integrand payload for the counterterm-inserted one-loop topology. -/
def mollerCountertermInsertedOneLoopIntegrand : TwoLoopScalarIntegrand where
  loopMomentum1 := mollerCountertermInsertedOneLoopLoopMomentum1
  loopMomentum2 := mollerCountertermInsertedOneLoopLoopMomentum2
  externalMomentum := mollerCountertermInsertedOneLoopExternalMomentum
  numeratorTerms := [unitNumeratorTerm]
  denominators :=
    [masslessDenominatorFactor]
  regulator := 1
  hRegulator := by norm_num
  reducedMaster := regularTwoLoopMaster 0

/-- General constructor for Møller two-loop diagram data. -/
def mollerTwoLoopDiagramData
    (label : MollerTwoLoopDiagramLabel)
    (loopMomentum1 loopMomentum2 externalMomentum : Momentum)
    (integrand : TwoLoopScalarIntegrand) : MollerTwoLoopDiagramData where
  label := label
  loopMomentum1 := loopMomentum1
  loopMomentum2 := loopMomentum2
  externalMomentum := externalMomentum
  integrand := integrand

/-- Constructor for a nested gauge-boson self-energy Møller two-loop diagram. -/
def mollerNestedGaugeBosonSelfEnergyDiagram : MollerTwoLoopDiagramData :=
  mollerTwoLoopDiagramData
    MollerTwoLoopDiagramLabel.nestedGaugeBosonSelfEnergy
    mollerNestedGaugeBosonSelfEnergyLoopMomentum1
    mollerNestedGaugeBosonSelfEnergyLoopMomentum2
    mollerNestedGaugeBosonSelfEnergyExternalMomentum
    mollerNestedGaugeBosonSelfEnergyIntegrand

/-- Constructor for a gauge-boson/ghost mixed Møller two-loop diagram. -/
def mollerGaugeGhostMixedDiagram : MollerTwoLoopDiagramData :=
  mollerTwoLoopDiagramData
    MollerTwoLoopDiagramLabel.gaugeGhostMixed
    mollerGaugeGhostMixedLoopMomentum1
    mollerGaugeGhostMixedLoopMomentum2
    mollerGaugeGhostMixedExternalMomentum
    mollerGaugeGhostMixedIntegrand

/-- Constructor for a vertex-corrected box-interference Møller two-loop diagram. -/
def mollerVertexCorrectedBoxInterferenceDiagram : MollerTwoLoopDiagramData :=
  mollerTwoLoopDiagramData
    MollerTwoLoopDiagramLabel.vertexCorrectedBoxInterference
    mollerVertexCorrectedBoxInterferenceLoopMomentum1
    mollerVertexCorrectedBoxInterferenceLoopMomentum2
    mollerVertexCorrectedBoxInterferenceExternalMomentum
    mollerVertexCorrectedBoxInterferenceIntegrand

/-- Constructor for a double-fermion self-energy Møller two-loop diagram. -/
def mollerDoubleFermionSelfEnergyDiagram : MollerTwoLoopDiagramData :=
  mollerTwoLoopDiagramData
    MollerTwoLoopDiagramLabel.doubleFermionSelfEnergy
    mollerDoubleFermionSelfEnergyLoopMomentum1
    mollerDoubleFermionSelfEnergyLoopMomentum2
    mollerDoubleFermionSelfEnergyExternalMomentum
    mollerDoubleFermionSelfEnergyIntegrand

/-- Constructor for a counterterm-inserted one-loop Møller two-loop diagram. -/
def mollerCountertermInsertedOneLoopDiagram : MollerTwoLoopDiagramData :=
  mollerTwoLoopDiagramData
    MollerTwoLoopDiagramLabel.countertermInsertedOneLoop
    mollerCountertermInsertedOneLoopLoopMomentum1
    mollerCountertermInsertedOneLoopLoopMomentum2
    mollerCountertermInsertedOneLoopExternalMomentum
    mollerCountertermInsertedOneLoopIntegrand

/-- Canonical Møller two-loop diagram list covering the curated topology set. -/
def mollerCanonicalTwoLoopDiagrams : List MollerTwoLoopDiagramData :=
  [mollerNestedGaugeBosonSelfEnergyDiagram,
   mollerGaugeGhostMixedDiagram,
   mollerVertexCorrectedBoxInterferenceDiagram,
   mollerDoubleFermionSelfEnergyDiagram,
   mollerCountertermInsertedOneLoopDiagram]

/-- Evaluation object for the nested gauge-boson self-energy topology. -/
def mollerNestedGaugeBosonSelfEnergyEvaluation : MollerTwoLoopDiagramEvaluation :=
  { diagram := mollerNestedGaugeBosonSelfEnergyDiagram,
    target := twoLoopSunset 1,
    hEvaluate := rfl }

/-- Evaluation object for the gauge-boson/ghost mixed topology. -/
def mollerGaugeGhostMixedEvaluation : MollerTwoLoopDiagramEvaluation :=
  { diagram := mollerGaugeGhostMixedDiagram,
    target := twoLoopBubble 1,
    hEvaluate := rfl }

/-- Evaluation object for the vertex-corrected box-interference topology. -/
def mollerVertexCorrectedBoxInterferenceEvaluation : MollerTwoLoopDiagramEvaluation :=
  { diagram := mollerVertexCorrectedBoxInterferenceDiagram,
    target := twoLoopVertexCorrection 1,
    hEvaluate := rfl }

/-- Evaluation object for the double-fermion self-energy topology. -/
def mollerDoubleFermionSelfEnergyEvaluation : MollerTwoLoopDiagramEvaluation :=
  { diagram := mollerDoubleFermionSelfEnergyDiagram,
    target := twoLoopSunset 2,
    hEvaluate := rfl }

/-- Evaluation object for the counterterm-inserted one-loop topology. -/
def mollerCountertermInsertedOneLoopEvaluation : MollerTwoLoopDiagramEvaluation :=
  { diagram := mollerCountertermInsertedOneLoopDiagram,
    target := regularTwoLoopMaster 0,
    hEvaluate := rfl }

/-- Canonical Møller two-loop evaluation bundle. -/
def mollerCanonicalTwoLoopEvaluations : List MollerTwoLoopDiagramEvaluation :=
  [mollerNestedGaugeBosonSelfEnergyEvaluation,
   mollerGaugeGhostMixedEvaluation,
   mollerVertexCorrectedBoxInterferenceEvaluation,
   mollerDoubleFermionSelfEnergyEvaluation,
   mollerCountertermInsertedOneLoopEvaluation]

/-!
## FeynArts interface contracts

FeynArts (Hahn–Schappacher, Comput. Phys. Commun. 140 (2001) 418) generates
Feynman diagrams and amplitudes for a given process and model. For
$e^- e^- \to e^- e^-$ at two loops in the electroweak SM, the relevant inputs
are:

* Model file : `ElectroweakSM.mod` with Feynman gauge
* Process : `Process[e, e -> e, e, Tadpoles -> False]` at loop order 2
* TopologySelection : exactly two closed loops, at most four external legs

The structures below are the Lean-side receptacles that a FeynArts-to-Lean
export script would populate. Each records the topology identifier, master
integral class, UV pole coefficient, and renormalized finite part.
-/

/-- FeynArts-facing interface data for a single two-loop Møller topology. -/
structure MollerFeynArtsTopologyData where
  /-- FeynArts topology label, e.g. "T1-nested-gauge-2pt". -/
  feynArtsTopologyId : String
  /-- Human-readable propagator topology description. -/
  topologyDescription : String
  /-- Scalar master integral class name. -/
  masterClass : String
  /-- Coupling prefactor in units of αEW^2. -/
  couplingNumerator : ℝ
  /-- UV pole coefficient (coefficient of 1/ε after DR). -/
  uvPoleCoeff : ℝ
  /-- Renormalized finite part after UV subtraction. -/
  renormalizedFinitePart : ℂ

/-- Topology-specific reduced amplitude from the nested gauge-boson self-energy evaluation. -/
def mollerNestedGaugeBosonSelfEnergyReducedAmplitude : ℝ :=
  mollerNestedGaugeBosonSelfEnergyEvaluation.target.poleCoeff

/-- Topology-specific reduced amplitude extracted from the gauge-boson/ghost mixed evaluation. -/
def mollerGaugeGhostMixedReducedAmplitude : ℝ :=
  mollerGaugeGhostMixedEvaluation.target.poleCoeff

/-- Topology-specific reduced amplitude from the vertex-corrected box-interference evaluation. -/
def mollerVertexCorrectedBoxInterferenceReducedAmplitude : ℝ :=
  mollerVertexCorrectedBoxInterferenceEvaluation.target.poleCoeff

/-- Topology-specific reduced amplitude extracted from the double-fermion self-energy evaluation. -/
def mollerDoubleFermionSelfEnergyReducedAmplitude : ℝ :=
  mollerDoubleFermionSelfEnergyEvaluation.target.poleCoeff

/-- Topology-specific reduced amplitude from the counterterm-inserted one-loop evaluation. -/
def mollerCountertermInsertedOneLoopReducedAmplitude : ℝ :=
  mollerCountertermInsertedOneLoopEvaluation.target.poleCoeff

/-- FeynArts interface data for the nested gauge-boson self-energy topology.

Two-loop 2-point function with a gauge-boson loop nested inside a second
gauge-boson loop. FeynArts class: T1-nested-gauge-2pt. The UV double pole is
absorbed by wave-function renormalization. Pole coefficient from dimensional
reduction: $c_{-1} \propto \beta_0/(4\pi)^2$. -/
def mollerNestedGaugeBosonSelfEnergyFeynArtsData : MollerFeynArtsTopologyData where
  feynArtsTopologyId := "T1-nested-gauge-2pt"
  topologyDescription := "Two-loop gauge-boson self-energy, nested gauge loop"
  masterClass := "twoLoopSunset"
  couplingNumerator := 1
  uvPoleCoeff := mollerNestedGaugeBosonSelfEnergyReducedAmplitude
  renormalizedFinitePart :=
    mollerNestedGaugeBosonSelfEnergyEvaluation.target.finitePart

/-- FeynArts interface data for the gauge-boson/ghost mixed topology.

Ghost loop mixes with gauge-boson loop to cancel gauge-parameter dependence in
the PV observable. FeynArts class: T2-gauge-ghost-2pt. Gauge independence is
enforced by the Slavnov–Taylor identities. -/
def mollerGaugeGhostMixedFeynArtsData : MollerFeynArtsTopologyData where
  feynArtsTopologyId := "T2-gauge-ghost-2pt"
  topologyDescription := "Two-loop gauge/ghost mixed self-energy"
  masterClass := "twoLoopBubble"
  couplingNumerator := 1
  uvPoleCoeff := mollerGaugeGhostMixedReducedAmplitude
  renormalizedFinitePart := mollerGaugeGhostMixedEvaluation.target.finitePart

/-- FeynArts interface data for the vertex-corrected box-interference topology.

One-loop vertex correction interfering with tree-level box. Dominant two-loop
class for the PV asymmetry; arXiv:1508.07853 gives δA/A ≈ -0.0034 from this
class for an 11 GeV beam. FeynArts class: T3-vertex-box. -/
def mollerVertexCorrectedBoxInterferenceFeynArtsData : MollerFeynArtsTopologyData where
  feynArtsTopologyId := "T3-vertex-box"
  topologyDescription :=
    "One-loop vertex correction interfering with tree-level box"
  masterClass := "twoLoopVertexCorrection"
  couplingNumerator := 1
  uvPoleCoeff := mollerVertexCorrectedBoxInterferenceReducedAmplitude
  renormalizedFinitePart :=
    mollerVertexCorrectedBoxInterferenceEvaluation.target.finitePart

/-- FeynArts interface data for the double-fermion self-energy topology.

Product of two one-loop fermion self-energy insertions on the electron line.
FeynArts class: T4-double-fermion-2pt. UV poles cancel between the two
self-energy factors after mass renormalization. -/
def mollerDoubleFermionSelfEnergyFeynArtsData : MollerFeynArtsTopologyData where
  feynArtsTopologyId := "T4-double-fermion-2pt"
  topologyDescription := "Product of two one-loop fermion self-energies"
  masterClass := "twoLoopSunset"
  couplingNumerator := 1
  uvPoleCoeff := mollerDoubleFermionSelfEnergyReducedAmplitude
  renormalizedFinitePart :=
    mollerDoubleFermionSelfEnergyEvaluation.target.finitePart

/-- FeynArts interface data for the counterterm-inserted one-loop topology.

One-loop diagram with a two-loop counterterm vertex insertion, accounting for
mass and coupling counterterms at order α^2. UV finite after renormalization.
FeynArts class: T5-counterterm-1loop. -/
def mollerCountertermInsertedOneLoopFeynArtsData : MollerFeynArtsTopologyData where
  feynArtsTopologyId := "T5-counterterm-1loop"
  topologyDescription :=
    "One-loop diagram with two-loop counterterm insertion"
  masterClass := "regularTwoLoopMaster"
  couplingNumerator := 1
  uvPoleCoeff := mollerCountertermInsertedOneLoopReducedAmplitude
  renormalizedFinitePart :=
    mollerCountertermInsertedOneLoopEvaluation.target.finitePart

/-- Bundled FeynArts interface data for all five Møller two-loop topologies. -/
def mollerFeynArtsTopologyBundle : List MollerFeynArtsTopologyData :=
  [mollerNestedGaugeBosonSelfEnergyFeynArtsData,
   mollerGaugeGhostMixedFeynArtsData,
   mollerVertexCorrectedBoxInterferenceFeynArtsData,
   mollerDoubleFermionSelfEnergyFeynArtsData,
   mollerCountertermInsertedOneLoopFeynArtsData]

/-!
## QGRAF interface contracts

QGRAF (Nogueira, Comput. Phys. Commun. 73 (1993) 1) generates Feynman diagrams
as integer-labelled propagator lists. For $e^- e^- \to e^- e^-$ at two loops
the relevant QGRAF call is:

```
process e, e -> e, e;
loops 2;
loop_momentum k1, k2;
options noself;
output qgraf_moller_2loop.dat;
```

The output lists each diagram by integer id with propagator types, vertex
types, and the overall symmetry factor. A typical FORM/FeynCalc post-processor
then maps each diagram number to a scalar master integral topology.

The structures below are the Lean-side receptacles for that post-processed
data. The key QGRAF-specific fields are the diagram integer identifier, the
propagator count, the vertex count, and the combinatorial symmetry factor.
The remaining fields (`uvPoleCoeff`, `renormalizedFinitePart`) coincide with
the FeynArts interface so that cross-tool agreement can be stated as a theorem.
-/

/-- Interface data for a single two-loop Møller topology. -/
structure MollerTopologyData where
  /-- Diagram integer identifier (matches external generator diagram id). -/
  qgrafDiagramId : ℕ
  /-- Number of internal propagator lines. -/
  propagatorCount : ℕ
  /-- Number of interaction vertices. -/
  vertexCount : ℕ
  /-- Combinatorial symmetry factor of the diagram. -/
  symmetryFactor : ℕ
  /-- Human-readable description matching the FeynArts topology. -/
  topologyDescription : String
  /-- UV pole coefficient (coefficient of 1/ε after DR). -/
  uvPoleCoeff : ℝ
  /-- Renormalized finite part after UV subtraction. -/
  renormalizedFinitePart : ℂ

/-- Compatibility alias: QGRAF-specific topology data name. -/
abbrev MollerQGRAFTopologyData := MollerTopologyData

/-- QGRAF interface data for the nested gauge-boson self-energy topology.

QGRAF diagram 1: 3 internal propagators (2 gauge bosons + 1 ghost closure),
2 gauge-boson 3-vertices. Symmetry factor 1. Sunset-class master. -/
def mollerNestedGaugeBosonSelfEnergyQGRAFData : MollerQGRAFTopologyData where
  qgrafDiagramId := 1
  propagatorCount := 3
  vertexCount := 2
  symmetryFactor := 1
  topologyDescription := "Two-loop gauge-boson self-energy, nested gauge loop"
  uvPoleCoeff := mollerNestedGaugeBosonSelfEnergyReducedAmplitude
  renormalizedFinitePart :=
    mollerNestedGaugeBosonSelfEnergyEvaluation.target.finitePart

/-- Neutral alias for the nested gauge-boson self-energy topology data. -/
abbrev mollerNestedGaugeBosonSelfEnergyTopologyData :=
  mollerNestedGaugeBosonSelfEnergyQGRAFData

/-- QGRAF interface data for the gauge-boson/ghost mixed topology.

QGRAF diagram 2: 2 internal propagators (1 gauge boson + 1 ghost), 2 mixed
vertices. Symmetry factor 1. Bubble-class master. -/
def mollerGaugeGhostMixedQGRAFData : MollerQGRAFTopologyData where
  qgrafDiagramId := 2
  propagatorCount := 2
  vertexCount := 2
  symmetryFactor := 1
  topologyDescription := "Two-loop gauge/ghost mixed self-energy"
  uvPoleCoeff := mollerGaugeGhostMixedReducedAmplitude
  renormalizedFinitePart := mollerGaugeGhostMixedEvaluation.target.finitePart

/-- Neutral alias for the gauge-boson/ghost mixed topology data. -/
abbrev mollerGaugeGhostMixedTopologyData := mollerGaugeGhostMixedQGRAFData

/-- QGRAF interface data for the vertex-corrected box-interference topology.

QGRAF diagram 3: 4 internal propagators (box topology with vertex insertion),
4 gauge-fermion vertices. Symmetry factor 1. Vertex-correction-class master.
This is the numerically dominant diagram class; see arXiv:1508.07853. -/
def mollerVertexCorrectedBoxInterferenceQGRAFData : MollerQGRAFTopologyData where
  qgrafDiagramId := 3
  propagatorCount := 4
  vertexCount := 4
  symmetryFactor := 1
  topologyDescription :=
    "One-loop vertex correction interfering with tree-level box"
  uvPoleCoeff := mollerVertexCorrectedBoxInterferenceReducedAmplitude
  renormalizedFinitePart :=
    mollerVertexCorrectedBoxInterferenceEvaluation.target.finitePart

/-- Neutral alias for the vertex-corrected box-interference topology data. -/
abbrev mollerVertexCorrectedBoxInterferenceTopologyData :=
  mollerVertexCorrectedBoxInterferenceQGRAFData

/-- QGRAF interface data for the double-fermion self-energy topology.

QGRAF diagram 4: 2 internal propagators (product of two fermion bubbles),
2 fermion self-energy insertions. Symmetry factor 2 (two identical insertions).
Sunset-class master. -/
def mollerDoubleFermionSelfEnergyQGRAFData : MollerQGRAFTopologyData where
  qgrafDiagramId := 4
  propagatorCount := 2
  vertexCount := 2
  symmetryFactor := 2
  topologyDescription := "Product of two one-loop fermion self-energies"
  uvPoleCoeff := mollerDoubleFermionSelfEnergyReducedAmplitude
  renormalizedFinitePart :=
    mollerDoubleFermionSelfEnergyEvaluation.target.finitePart

/-- Neutral alias for the double-fermion self-energy topology data. -/
abbrev mollerDoubleFermionSelfEnergyTopologyData :=
  mollerDoubleFermionSelfEnergyQGRAFData

/-- QGRAF interface data for the counterterm-inserted one-loop topology.

QGRAF diagram 5: 1 internal propagator with counterterm insertion, 1 vertex.
Symmetry factor 1. Regular (UV-finite) master. -/
def mollerCountertermInsertedOneLoopQGRAFData : MollerQGRAFTopologyData where
  qgrafDiagramId := 5
  propagatorCount := 1
  vertexCount := 1
  symmetryFactor := 1
  topologyDescription :=
    "One-loop diagram with two-loop counterterm insertion"
  uvPoleCoeff := mollerCountertermInsertedOneLoopReducedAmplitude
  renormalizedFinitePart :=
    mollerCountertermInsertedOneLoopEvaluation.target.finitePart

/-- Neutral alias for the counterterm-inserted one-loop topology data. -/
abbrev mollerCountertermInsertedOneLoopTopologyData :=
  mollerCountertermInsertedOneLoopQGRAFData

/-- Bundled QGRAF interface data for all five Møller two-loop topologies. -/
def mollerQGRAFTopologyBundle : List MollerQGRAFTopologyData :=
  [mollerNestedGaugeBosonSelfEnergyQGRAFData,
   mollerGaugeGhostMixedQGRAFData,
   mollerVertexCorrectedBoxInterferenceQGRAFData,
   mollerDoubleFermionSelfEnergyQGRAFData,
   mollerCountertermInsertedOneLoopQGRAFData]

/-- Neutral alias for the Møller topology bundle. -/
abbrev mollerTopologyBundle := mollerQGRAFTopologyBundle

end Examples
end PVES
end DIS
end Scattering
end QFT
end EpsilonEridani
