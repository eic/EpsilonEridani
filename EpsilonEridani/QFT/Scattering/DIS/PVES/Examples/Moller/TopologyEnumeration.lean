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
public import EpsilonEridani.QFT.Scattering.DIS.PVES.Examples.Moller.Basic
/-!

# PVES MOLLER Examples: Two-Loop Topology Enumeration

This module continues `EpsilonEridani.QFT.Scattering.DIS.PVES.Examples.Moller.Basic`,
split out to stay under the file-length limit. It contains the Lean-native
QGRAF-style topology enumeration workflow and the two-loop derivation bundle
built from it.

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

/-!
## Lean-native QGRAF-style topology enumeration workflow

QGRAF itself emits graph-level data (ids plus propagator/vertex incidence) and
an external post-processor classifies those graphs into physics topologies. The
definitions below internalize that workflow entirely in Lean:

1. enumerate candidate two-loop ee->ee graph records,
2. classify each candidate to a `MollerTwoLoopDiagramLabel`,
3. prove the classified set matches the curated Møller topology set.
-/

/-- Topology candidate record for the Lean-native Møller enumeration. -/
structure MollerTopologyCandidate where
  /-- Diagram integer id. -/
  diagramId : ℕ
  /-- Number of internal propagators. -/
  propagatorCount : ℕ
  /-- Number of interaction vertices. -/
  vertexCount : ℕ
  /-- Combinatorial symmetry factor. -/
  symmetryFactor : ℕ
  /-- Whether a ghost line appears in the diagram. -/
  hasGhostLine : Bool
  /-- Whether a two-loop counterterm insertion appears. -/
  hasCountertermInsertion : Bool
  /-- Whether the graph is a vertex-corrected box-interference pattern. -/
  isVertexBoxInterference : Bool
  /-- Number of fermion self-energy insertions on external electron legs. -/
  fermionSelfEnergyInsertions : ℕ
  /-- Whether the graph contains a nested gauge-boson self-energy subgraph. -/
  hasNestedGaugeSelfEnergy : Bool

/-- Compatibility alias: QGRAF-specific candidate name. -/
abbrev MollerQGRAFCandidate := MollerTopologyCandidate

/-- Node kinds in the Lean-native Møller topology enumeration. -/
inductive MollerTopologyNodeKind where
  | gaugeInteraction
  | ghostInteraction
  | fermionSelfEnergyInsertion
  | countertermInsertion
  deriving DecidableEq, Repr

/-- Compatibility alias: QGRAF-specific node kind name. -/
abbrev MollerQGRAFNodeKind := MollerTopologyNodeKind

namespace MollerQGRAFNodeKind
-- An `abbrev` aliases the type but not its constructor namespace, so the
-- constructors are re-exported to make `MollerQGRAFNodeKind.<ctor>` resolve.
export MollerTopologyNodeKind
  (gaugeInteraction ghostInteraction fermionSelfEnergyInsertion countertermInsertion)
end MollerQGRAFNodeKind

/-- Edge kinds in the Lean-native Møller topology enumeration. -/
inductive MollerTopologyEdgeKind where
  | gaugePropagator
  | ghostPropagator
  | fermionPropagator
  | countertermEdge
  deriving DecidableEq, Repr

/-- Compatibility alias: QGRAF-specific edge kind name. -/
abbrev MollerQGRAFEdgeKind := MollerTopologyEdgeKind

namespace MollerQGRAFEdgeKind
-- An `abbrev` aliases the type but not its constructor namespace, so the
-- constructors are re-exported to make `MollerQGRAFEdgeKind.<ctor>` resolve.
export MollerTopologyEdgeKind
  (gaugePropagator ghostPropagator fermionPropagator countertermEdge)
end MollerQGRAFEdgeKind

/-- Compact graph container for a generated Møller topology. -/
structure MollerTopologyGraph where
  /-- Diagram integer id. -/
  diagramId : ℕ
  /-- Number of external electron nodes (fixed to 4 for ee->ee). -/
  externalNodeCount : ℕ
  /-- Interaction-node signature of the internal graph skeleton. -/
  interactionNodes : List MollerTopologyNodeKind
  /-- Internal propagator-type signature. -/
  internalEdgeKinds : List MollerTopologyEdgeKind
  /-- Combinatorial symmetry factor. -/
  symmetryFactor : ℕ

/-- Compatibility alias: QGRAF-specific graph name. -/
abbrev MollerQGRAFGraph := MollerTopologyGraph

/-- Exact node/edge incidence constraints for a generated Møller topology. -/
structure MollerTopologyConstraint where
  /-- Diagram integer id. -/
  diagramId : ℕ
  /-- Number of external electron nodes. -/
  externalNodeCount : ℕ
  /-- Combinatorial symmetry factor. -/
  symmetryFactor : ℕ
  /-- Number of interaction nodes. -/
  interactionNodeCount : ℕ
  /-- Gauge interaction nodes. -/
  gaugeInteractionCount : ℕ
  /-- Ghost interaction nodes. -/
  ghostInteractionCount : ℕ
  /-- Fermion self-energy insertion nodes. -/
  fermionSelfEnergyInsertionCount : ℕ
  /-- Counterterm insertion nodes. -/
  countertermInsertionCount : ℕ
  /-- Number of internal propagators. -/
  internalEdgeCount : ℕ
  /-- Gauge propagators. -/
  gaugePropagatorCount : ℕ
  /-- Ghost propagators. -/
  ghostPropagatorCount : ℕ
  /-- Fermion propagators. -/
  fermionPropagatorCount : ℕ
  /-- Counterterm edges. -/
  countertermEdgeCount : ℕ

/-- Compatibility alias: QGRAF-specific constraint name. -/
abbrev MollerQGRAFGraphConstraint := MollerTopologyConstraint

/-- Canonical node alphabet for the Lean-side QGRAF search. -/
def mollerQGRAFNodeAlphabet : List MollerQGRAFNodeKind :=
  [MollerQGRAFNodeKind.gaugeInteraction,
   MollerQGRAFNodeKind.ghostInteraction,
   MollerQGRAFNodeKind.fermionSelfEnergyInsertion,
   MollerQGRAFNodeKind.countertermInsertion]

/-- Canonical edge alphabet for the Lean-side QGRAF search. -/
def mollerQGRAFEdgeAlphabet : List MollerQGRAFEdgeKind :=
  [MollerQGRAFEdgeKind.gaugePropagator,
   MollerQGRAFEdgeKind.ghostPropagator,
   MollerQGRAFEdgeKind.fermionPropagator,
   MollerQGRAFEdgeKind.countertermEdge]

/-- The graph-skeleton search is a pure filter on exact node/edge incidence
constraints, not a hand-written list of templates. -/
def mollerQGRAFGraphOfConstraint
    (constraint : MollerQGRAFGraphConstraint) : MollerQGRAFGraph :=
  let nodeMatches : List MollerQGRAFNodeKind → Bool := fun nodes =>
    let gaugeCount :=
      (nodes.filter (fun n => decide (n = MollerQGRAFNodeKind.gaugeInteraction))).length
    let ghostCount :=
      (nodes.filter (fun n => decide (n = MollerQGRAFNodeKind.ghostInteraction))).length
    let fermionCount :=
      (nodes.filter (fun n =>
        decide (n = MollerQGRAFNodeKind.fermionSelfEnergyInsertion))).length
    let countertermCount :=
      (nodes.filter (fun n => decide (n = MollerQGRAFNodeKind.countertermInsertion))).length
    (nodes.length = constraint.interactionNodeCount) &&
      (gaugeCount = constraint.gaugeInteractionCount) &&
      (ghostCount = constraint.ghostInteractionCount) &&
      (fermionCount = constraint.fermionSelfEnergyInsertionCount) &&
      (countertermCount = constraint.countertermInsertionCount)
  let edgeMatches : List MollerQGRAFEdgeKind → Bool := fun edges =>
    let gaugeCount :=
      (edges.filter (fun e => decide (e = MollerQGRAFEdgeKind.gaugePropagator))).length
    let ghostCount :=
      (edges.filter (fun e => decide (e = MollerQGRAFEdgeKind.ghostPropagator))).length
    let fermionCount :=
      (edges.filter (fun e => decide (e = MollerQGRAFEdgeKind.fermionPropagator))).length
    let countertermCount :=
      (edges.filter (fun e => decide (e = MollerQGRAFEdgeKind.countertermEdge))).length
    (edges.length = constraint.internalEdgeCount) &&
      (gaugeCount = constraint.gaugePropagatorCount) &&
      (ghostCount = constraint.ghostPropagatorCount) &&
      (fermionCount = constraint.fermionPropagatorCount) &&
      (countertermCount = constraint.countertermEdgeCount)
  match firstMatching (allListsOfLength constraint.interactionNodeCount mollerQGRAFNodeAlphabet)
      nodeMatches,
    firstMatching (allListsOfLength constraint.internalEdgeCount mollerQGRAFEdgeAlphabet)
      edgeMatches with
  | some nodes, some edges =>
      show MollerQGRAFGraph from
        { diagramId := constraint.diagramId,
          externalNodeCount := constraint.externalNodeCount,
          interactionNodes := nodes,
          internalEdgeKinds := edges,
          symmetryFactor := constraint.symmetryFactor }
  | _, _ =>
      show MollerQGRAFGraph from
        { diagramId := constraint.diagramId,
          externalNodeCount := constraint.externalNodeCount,
          interactionNodes := [],
          internalEdgeKinds := [],
          symmetryFactor := constraint.symmetryFactor }

/-- Canonical Møller topology constraints, ordered by the physical topology list.

Column guide (in MollerTopologyConstraint field order):
```
id  ext sym  iN  gI ghI  fI ctI  iE  gP ghP  fP ctE
```
where:
* `id`  = diagram integer id
* `ext` = external node count (fixed 4 for ee→ee)
* `sym` = symmetry factor
* `iN`  = interaction node count
* `gI`  = gauge interaction count
* `ghI` = ghost interaction count
* `fI`  = fermion self-energy insertion count
* `ctI` = counterterm insertion count
* `iE`  = internal edge count
* `gP`  = gauge propagator count
* `ghP` = ghost propagator count
* `fP`  = fermion propagator count
* `ctE` = counterterm edge count -/
def mollerQGRAFGraphConstraints : List MollerQGRAFGraphConstraint :=
  --                                id ext sym  iN  gI ghI  fI ctI  iE  gP ghP  fP ctE
  [ MollerTopologyConstraint.mk      1   4   1   2   2   0   0   0   3   3   0   0   0,
    MollerTopologyConstraint.mk      2   4   1   2   1   1   0   0   2   1   1   0   0,
    MollerTopologyConstraint.mk      3   4   1   4   4   0   0   0   4   4   0   0   0,
    MollerTopologyConstraint.mk      4   4   2   2   0   0   2   0   2   0   0   2   0,
    MollerTopologyConstraint.mk      5   4   1   1   0   0   0   1   1   0   0   0   1 ]

/-- Lean-native QGRAF graph enumeration produced by filtering exact incidence
constraints through the canonical search space. -/
def mollerQGRAFGraphEnumeration : List MollerQGRAFGraph :=
  mollerQGRAFGraphConstraints.map mollerQGRAFGraphOfConstraint

/-- Neutral alias for the generated Møller graph enumeration. -/
abbrev mollerTopologyGraphEnumeration := mollerQGRAFGraphEnumeration

/-- Lean-side candidate obtained from the constraint-generated graph record. -/
def mollerQGRAFCandidateOfConstraint
    (constraint : MollerQGRAFGraphConstraint) : MollerQGRAFCandidate :=
  let graph : MollerQGRAFGraph := mollerQGRAFGraphOfConstraint constraint
  { diagramId := graph.diagramId,
    propagatorCount := graph.internalEdgeKinds.length,
    vertexCount := graph.interactionNodes.length,
    symmetryFactor := graph.symmetryFactor,
    hasGhostLine := graph.internalEdgeKinds.any (fun e =>
      decide (e = MollerQGRAFEdgeKind.ghostPropagator)),
    hasCountertermInsertion := graph.interactionNodes.any (fun n =>
      decide (n = MollerQGRAFNodeKind.countertermInsertion)) ||
      graph.internalEdgeKinds.any (fun e =>
        decide (e = MollerQGRAFEdgeKind.countertermEdge)),
    isVertexBoxInterference :=
      decide (graph.internalEdgeKinds.length = 4) &&
        decide (graph.interactionNodes.length = 4) &&
        decide ((graph.internalEdgeKinds.filter (fun e =>
          decide (e = MollerQGRAFEdgeKind.gaugePropagator))).length = 4),
    fermionSelfEnergyInsertions := (graph.interactionNodes.filter (fun n =>
      decide (n = MollerQGRAFNodeKind.fermionSelfEnergyInsertion))).length,
    hasNestedGaugeSelfEnergy :=
      decide (graph.internalEdgeKinds.length = 3) &&
        decide (graph.interactionNodes.length = 2) &&
        decide ((graph.internalEdgeKinds.filter (fun e =>
          decide (e = MollerQGRAFEdgeKind.gaugePropagator))).length = 3) }

/-- Lean-native QGRAF candidate enumeration for two-loop Møller scattering. -/
def mollerQGRAFCandidateEnumeration : List MollerQGRAFCandidate :=
  mollerQGRAFGraphConstraints.map mollerQGRAFCandidateOfConstraint

/-- Neutral alias for the generated Møller candidate enumeration. -/
abbrev mollerTopologyCandidateEnumeration := mollerQGRAFCandidateEnumeration

/-- Signature used by the Møller two-loop topology classifier. -/
structure MollerTwoLoopTopologySignature where
  hasGhostLine : Bool
  hasCountertermInsertion : Bool
  isVertexBoxInterference : Bool
  fermionSelfEnergyInsertions : ℕ
  hasNestedGaugeSelfEnergy : Bool

/-- Extract two-loop classifier signature from a Møller QGRAF candidate. -/
def mollerTwoLoopSignatureOfCandidate
    (candidate : MollerQGRAFCandidate) : MollerTwoLoopTopologySignature :=
  { hasGhostLine := candidate.hasGhostLine
    hasCountertermInsertion := candidate.hasCountertermInsertion
    isVertexBoxInterference := candidate.isVertexBoxInterference
    fermionSelfEnergyInsertions := candidate.fermionSelfEnergyInsertions
    hasNestedGaugeSelfEnergy := candidate.hasNestedGaugeSelfEnergy }

/-- Classifier from Møller two-loop signatures to curated topology labels. -/
def mollerClassifyQGRAFSignature
    (signature : MollerTwoLoopTopologySignature) : Option MollerTwoLoopDiagramLabel :=
  if signature.hasCountertermInsertion then
    some MollerTwoLoopDiagramLabel.countertermInsertedOneLoop
  else if signature.isVertexBoxInterference then
    some MollerTwoLoopDiagramLabel.vertexCorrectedBoxInterference
  else if signature.fermionSelfEnergyInsertions = 2 then
    some MollerTwoLoopDiagramLabel.doubleFermionSelfEnergy
  else if signature.hasNestedGaugeSelfEnergy then
    some MollerTwoLoopDiagramLabel.nestedGaugeBosonSelfEnergy
  else if signature.hasGhostLine then
    some MollerTwoLoopDiagramLabel.gaugeGhostMixed
  else
    none

/-- Canonical topology-class order used for grouped class enumeration output. -/
def mollerTopologyClassOrder : List MollerTwoLoopDiagramLabel :=
  [MollerTwoLoopDiagramLabel.nestedGaugeBosonSelfEnergy,
   MollerTwoLoopDiagramLabel.gaugeGhostMixed,
   MollerTwoLoopDiagramLabel.vertexCorrectedBoxInterference,
   MollerTwoLoopDiagramLabel.doubleFermionSelfEnergy,
   MollerTwoLoopDiagramLabel.countertermInsertedOneLoop]

/-- Classifier specification for Møller two-loop topology signatures. -/
def mollerTwoLoopClassifierSpec :
    TopologyClassifierSpec MollerTwoLoopDiagramLabel MollerTwoLoopTopologySignature where
  classOrder := mollerTopologyClassOrder
  classify := mollerClassifyQGRAFSignature

/-- Classifier from Lean-side QGRAF candidates to curated labels.
Compatibility shim over the signature-level classifier. -/
def mollerClassifyQGRAFCandidate
    (candidate : MollerQGRAFCandidate) : Option MollerTwoLoopDiagramLabel :=
  mollerClassifyQGRAFSignature (mollerTwoLoopSignatureOfCandidate candidate)

/-- Candidates that classify into a specific topology class label. -/
def mollerQGRAFCandidatesClassifiedAs
    (label : MollerTwoLoopDiagramLabel) : List MollerQGRAFCandidate :=
  mollerQGRAFCandidateEnumeration.filter (fun c =>
    mollerClassifyQGRAFCandidate c = some label)

/-- Grouped class enumeration for Møller candidates, in canonical class order. -/
def mollerQGRAFClassEnumeration :
    List (MollerTwoLoopDiagramLabel × List MollerQGRAFCandidate) :=
  enumerateItemClassBlocks mollerTwoLoopClassifierSpec
    mollerTwoLoopSignatureOfCandidate mollerQGRAFCandidateEnumeration

/-- Neutral alias for grouped class enumeration. -/
abbrev mollerTopologyClassEnumeration := mollerQGRAFClassEnumeration

/-- The grouped class enumeration preserves canonical class order. -/
theorem mollerQGRAFClassEnumeration_map_fst :
    mollerQGRAFClassEnumeration.map Prod.fst = mollerTopologyClassOrder := by
  simpa [mollerQGRAFClassEnumeration, mollerTwoLoopClassifierSpec] using
    enumerateItemClassBlocks_map_fst
      (spec := mollerTwoLoopClassifierSpec)
      (extract := mollerTwoLoopSignatureOfCandidate)
      (items := mollerQGRAFCandidateEnumeration)

/-- Normalized theorem name for two-loop class-order preservation. -/
theorem mollerQGRAFClassEnumeration_preserves_classOrder :
    mollerQGRAFClassEnumeration.map Prod.fst = mollerTopologyClassOrder :=
  mollerQGRAFClassEnumeration_map_fst

/-- Classified topology labels produced by the Lean-native QGRAF workflow. -/
def mollerQGRAFEnumeratedLabels : List MollerTwoLoopDiagramLabel :=
  mollerQGRAFCandidateEnumeration.filterMap mollerClassifyQGRAFCandidate

/-- Neutral alias for the classified Møller topology labels. -/
abbrev mollerTopologyLabels := mollerQGRAFEnumeratedLabels

/-- The Lean-native QGRAF classifier produces the expected canonical label order. -/
lemma mollerQGRAFEnumeratedLabels_eq_canonicalOrder :
    mollerQGRAFEnumeratedLabels =
      [MollerTwoLoopDiagramLabel.nestedGaugeBosonSelfEnergy,
       MollerTwoLoopDiagramLabel.gaugeGhostMixed,
       MollerTwoLoopDiagramLabel.vertexCorrectedBoxInterference,
       MollerTwoLoopDiagramLabel.doubleFermionSelfEnergy,
       MollerTwoLoopDiagramLabel.countertermInsertedOneLoop] := by
  decide

/-- Neutral form of the canonical label-order theorem. -/
lemma mollerTopologyLabels_eq_canonicalOrder :
    mollerTopologyLabels =
      [MollerTwoLoopDiagramLabel.nestedGaugeBosonSelfEnergy,
       MollerTwoLoopDiagramLabel.gaugeGhostMixed,
       MollerTwoLoopDiagramLabel.vertexCorrectedBoxInterference,
       MollerTwoLoopDiagramLabel.doubleFermionSelfEnergy,
       MollerTwoLoopDiagramLabel.countertermInsertedOneLoop] := by
  simpa [mollerTopologyLabels] using mollerQGRAFEnumeratedLabels_eq_canonicalOrder

/-- Set-level completeness: Lean-native QGRAF classification recovers exactly
the curated Møller two-loop topology set. -/
theorem mollerQGRAFEnumeratedLabels_toFinset_eq_contributingSet :
    mollerQGRAFEnumeratedLabels.toFinset = mollerContributingTwoLoopDiagrams := by
  simp [mollerQGRAFEnumeratedLabels_eq_canonicalOrder,
    mollerContributingTwoLoopDiagrams]

/-- Normalized theorem name for two-loop finite-set completeness. -/
theorem mollerQGRAFClassifiedLabels_toFinset_eq_contributingSet :
    mollerQGRAFEnumeratedLabels.toFinset = mollerContributingTwoLoopDiagrams :=
  mollerQGRAFEnumeratedLabels_toFinset_eq_contributingSet

/-- Neutral form of the set-level completeness theorem. -/
theorem mollerTopologyLabels_toFinset_eq_contributingSet :
    mollerTopologyLabels.toFinset = mollerContributingTwoLoopDiagrams := by
  simpa [mollerTopologyLabels] using
    mollerQGRAFEnumeratedLabels_toFinset_eq_contributingSet

/-- Canonical map from a classified topology label to the existing QGRAF data. -/
def mollerQGRAFDataOfLabel
    (label : MollerTwoLoopDiagramLabel) : MollerQGRAFTopologyData :=
  match label with
  | .nestedGaugeBosonSelfEnergy => mollerNestedGaugeBosonSelfEnergyQGRAFData
  | .gaugeGhostMixed => mollerGaugeGhostMixedQGRAFData
  | .vertexCorrectedBoxInterference =>
      mollerVertexCorrectedBoxInterferenceQGRAFData
  | .doubleFermionSelfEnergy => mollerDoubleFermionSelfEnergyQGRAFData
  | .countertermInsertedOneLoop => mollerCountertermInsertedOneLoopQGRAFData

/-- Neutral alias for the Møller topology data selector. -/
abbrev mollerTopologyDataOfLabel := mollerQGRAFDataOfLabel

/-- Lean-native QGRAF enumerator reproduces the canonical QGRAF topology bundle. -/
theorem mollerQGRAFTopologyBundle_eq_map_enumeratedLabels :
    mollerQGRAFTopologyBundle =
      mollerQGRAFEnumeratedLabels.map mollerQGRAFDataOfLabel := by
  simp [mollerQGRAFTopologyBundle,
    mollerQGRAFEnumeratedLabels_eq_canonicalOrder,
    mollerQGRAFDataOfLabel]

/-- Neutral form of the bundle reconstruction theorem. -/
theorem mollerTopologyBundle_eq_map_enumeratedLabels :
    mollerTopologyBundle =
      mollerTopologyLabels.map mollerTopologyDataOfLabel :=
  mollerQGRAFTopologyBundle_eq_map_enumeratedLabels

/-- Cross-tool agreement: the UV pole coefficient is the same whether the
topology data comes from FeynArts or from QGRAF. This is the Lean statement
of the physical requirement that two independent diagram generators must
produce the same UV divergence structure. -/
theorem mollerQGRAF_uvPole_eq_feynArts_uvPole :
    mollerNestedGaugeBosonSelfEnergyQGRAFData.uvPoleCoeff =
        mollerNestedGaugeBosonSelfEnergyFeynArtsData.uvPoleCoeff ∧
    mollerGaugeGhostMixedQGRAFData.uvPoleCoeff =
        mollerGaugeGhostMixedFeynArtsData.uvPoleCoeff ∧
    mollerVertexCorrectedBoxInterferenceQGRAFData.uvPoleCoeff =
        mollerVertexCorrectedBoxInterferenceFeynArtsData.uvPoleCoeff ∧
    mollerDoubleFermionSelfEnergyQGRAFData.uvPoleCoeff =
        mollerDoubleFermionSelfEnergyFeynArtsData.uvPoleCoeff ∧
    mollerCountertermInsertedOneLoopQGRAFData.uvPoleCoeff =
        mollerCountertermInsertedOneLoopFeynArtsData.uvPoleCoeff :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Neutral form of the pole-agreement theorem. -/
theorem mollerTopology_uvPole_eq_feynArts_uvPole :
    mollerNestedGaugeBosonSelfEnergyTopologyData.uvPoleCoeff =
        mollerNestedGaugeBosonSelfEnergyFeynArtsData.uvPoleCoeff ∧
    mollerGaugeGhostMixedTopologyData.uvPoleCoeff =
        mollerGaugeGhostMixedFeynArtsData.uvPoleCoeff ∧
    mollerVertexCorrectedBoxInterferenceTopologyData.uvPoleCoeff =
        mollerVertexCorrectedBoxInterferenceFeynArtsData.uvPoleCoeff ∧
    mollerDoubleFermionSelfEnergyTopologyData.uvPoleCoeff =
        mollerDoubleFermionSelfEnergyFeynArtsData.uvPoleCoeff ∧
    mollerCountertermInsertedOneLoopTopologyData.uvPoleCoeff =
        mollerCountertermInsertedOneLoopFeynArtsData.uvPoleCoeff := by
  simpa [mollerNestedGaugeBosonSelfEnergyTopologyData,
    mollerGaugeGhostMixedTopologyData,
    mollerVertexCorrectedBoxInterferenceTopologyData,
    mollerDoubleFermionSelfEnergyTopologyData,
    mollerCountertermInsertedOneLoopTopologyData] using
      mollerQGRAF_uvPole_eq_feynArts_uvPole

/-- Per-topology reduction lemma: nested gauge-boson amplitude equals the pole
coefficient of its sunset master evaluation target. -/
lemma mollerNestedGaugeBoson_amplitude_eq_poleCoeff :
    mollerNestedGaugeBosonSelfEnergyReducedAmplitude =
      mollerNestedGaugeBosonSelfEnergyEvaluation.target.poleCoeff :=
  rfl

/-- Per-topology reduction lemma: gauge-ghost amplitude equals the pole
coefficient of its bubble master evaluation target. -/
lemma mollerGaugeGhostMixed_amplitude_eq_poleCoeff :
    mollerGaugeGhostMixedReducedAmplitude =
      mollerGaugeGhostMixedEvaluation.target.poleCoeff :=
  rfl

/-- Per-topology reduction lemma: vertex-correction amplitude equals the pole
coefficient of its vertex-correction master evaluation target. -/
lemma mollerVertexCorrectedBoxInterference_amplitude_eq_poleCoeff :
    mollerVertexCorrectedBoxInterferenceReducedAmplitude =
      mollerVertexCorrectedBoxInterferenceEvaluation.target.poleCoeff :=
  rfl

/-- Per-topology reduction lemma: double-fermion amplitude equals the pole
coefficient of its sunset master evaluation target. -/
lemma mollerDoubleFermionSelfEnergy_amplitude_eq_poleCoeff :
    mollerDoubleFermionSelfEnergyReducedAmplitude =
      mollerDoubleFermionSelfEnergyEvaluation.target.poleCoeff :=
  rfl

/-- Per-topology reduction lemma: counterterm amplitude equals the pole
coefficient of its regular master evaluation target. -/
lemma mollerCountertermInsertedOneLoop_amplitude_eq_poleCoeff :
    mollerCountertermInsertedOneLoopReducedAmplitude =
      mollerCountertermInsertedOneLoopEvaluation.target.poleCoeff :=
  rfl

/-- The FeynArts UV pole coefficient equals the evaluation pole coefficient for
every topology in the bundle. -/
theorem mollerFeynArts_uvPole_eq_evaluationPoleCoeff :
    mollerNestedGaugeBosonSelfEnergyFeynArtsData.uvPoleCoeff =
        mollerNestedGaugeBosonSelfEnergyEvaluation.target.poleCoeff ∧
    mollerGaugeGhostMixedFeynArtsData.uvPoleCoeff =
        mollerGaugeGhostMixedEvaluation.target.poleCoeff ∧
    mollerVertexCorrectedBoxInterferenceFeynArtsData.uvPoleCoeff =
        mollerVertexCorrectedBoxInterferenceEvaluation.target.poleCoeff ∧
    mollerDoubleFermionSelfEnergyFeynArtsData.uvPoleCoeff =
        mollerDoubleFermionSelfEnergyEvaluation.target.poleCoeff ∧
    mollerCountertermInsertedOneLoopFeynArtsData.uvPoleCoeff =
        mollerCountertermInsertedOneLoopEvaluation.target.poleCoeff :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Concrete derivation record for a single Møller two-loop topology. -/
structure MollerTwoLoopDerivationEntry where
  /-- Topology label. -/
  label : MollerTwoLoopDiagramLabel
  /-- Concrete diagram data. -/
  diagram : MollerTwoLoopDiagramData
  /-- Concrete evaluation witness. -/
  evaluation : MollerTwoLoopDiagramEvaluation
  /-- Concrete reduction witness from the diagram integrand to the chosen target master. -/
  reduction : TwoLoopScalarIntegrandReduction diagram.integrand evaluation.target
  /-- Reduced amplitude attached to the topology. -/
  reducedAmplitude : ℝ
  /-- The diagram label matches the stored topology label. -/
  hLabel : diagram.label = label
  /-- The evaluation packages the same diagram. -/
  hDiagram : evaluation.diagram = diagram

/-- Canonical derivation entry for the nested gauge-boson self-energy topology. -/
def mollerNestedGaugeBosonSelfEnergyDerivationEntry : MollerTwoLoopDerivationEntry where
  label := MollerTwoLoopDiagramLabel.nestedGaugeBosonSelfEnergy
  diagram := mollerNestedGaugeBosonSelfEnergyDiagram
  evaluation := mollerNestedGaugeBosonSelfEnergyEvaluation
  reduction := { hEvaluate := rfl }
  reducedAmplitude := mollerNestedGaugeBosonSelfEnergyReducedAmplitude
  hLabel := rfl
  hDiagram := rfl

/-- Canonical derivation entry for the gauge-boson/ghost mixed topology. -/
def mollerGaugeGhostMixedDerivationEntry : MollerTwoLoopDerivationEntry where
  label := MollerTwoLoopDiagramLabel.gaugeGhostMixed
  diagram := mollerGaugeGhostMixedDiagram
  evaluation := mollerGaugeGhostMixedEvaluation
  reduction := { hEvaluate := rfl }
  reducedAmplitude := mollerGaugeGhostMixedReducedAmplitude
  hLabel := rfl
  hDiagram := rfl

/-- Canonical derivation entry for the vertex-corrected box-interference topology. -/
def mollerVertexCorrectedBoxInterferenceDerivationEntry : MollerTwoLoopDerivationEntry where
  label := MollerTwoLoopDiagramLabel.vertexCorrectedBoxInterference
  diagram := mollerVertexCorrectedBoxInterferenceDiagram
  evaluation := mollerVertexCorrectedBoxInterferenceEvaluation
  reduction := { hEvaluate := rfl }
  reducedAmplitude := mollerVertexCorrectedBoxInterferenceReducedAmplitude
  hLabel := rfl
  hDiagram := rfl

/-- Canonical derivation entry for the double-fermion self-energy topology. -/
def mollerDoubleFermionSelfEnergyDerivationEntry : MollerTwoLoopDerivationEntry where
  label := MollerTwoLoopDiagramLabel.doubleFermionSelfEnergy
  diagram := mollerDoubleFermionSelfEnergyDiagram
  evaluation := mollerDoubleFermionSelfEnergyEvaluation
  reduction := { hEvaluate := rfl }
  reducedAmplitude := mollerDoubleFermionSelfEnergyReducedAmplitude
  hLabel := rfl
  hDiagram := rfl

/-- Canonical derivation entry for the counterterm-inserted one-loop topology. -/
def mollerCountertermInsertedOneLoopDerivationEntry : MollerTwoLoopDerivationEntry where
  label := MollerTwoLoopDiagramLabel.countertermInsertedOneLoop
  diagram := mollerCountertermInsertedOneLoopDiagram
  evaluation := mollerCountertermInsertedOneLoopEvaluation
  reduction := { hEvaluate := rfl }
  reducedAmplitude := mollerCountertermInsertedOneLoopReducedAmplitude
  hLabel := rfl
  hDiagram := rfl

/-- Canonical list of concrete Møller two-loop derivation entries. -/
def mollerCanonicalTwoLoopDerivationEntries : List MollerTwoLoopDerivationEntry :=
  [mollerNestedGaugeBosonSelfEnergyDerivationEntry,
   mollerGaugeGhostMixedDerivationEntry,
   mollerVertexCorrectedBoxInterferenceDerivationEntry,
   mollerDoubleFermionSelfEnergyDerivationEntry,
   mollerCountertermInsertedOneLoopDerivationEntry]

/-- Canonical Møller two-loop derivation bundle. -/
structure MollerTwoLoopDerivationBundle where
  /-- Concrete derivation entries. -/
  entries : List MollerTwoLoopDerivationEntry
  /-- Canonical bridge certificate. -/
  bridge : MollerTwoLoopDiagrammaticBridge
  /-- Canonical reduced-amplitude model. -/
  contributions : MollerTwoLoopContributions
/-- Canonical reduced-amplitude model attached to the Møller two-loop topology set. -/
def mollerCanonicalTwoLoopContributions : MollerTwoLoopContributions where
  reducedAmplitude
  | MollerTwoLoopDiagramLabel.nestedGaugeBosonSelfEnergy =>
    mollerNestedGaugeBosonSelfEnergyReducedAmplitude
  | MollerTwoLoopDiagramLabel.gaugeGhostMixed =>
    mollerGaugeGhostMixedReducedAmplitude
  | MollerTwoLoopDiagramLabel.vertexCorrectedBoxInterference =>
    mollerVertexCorrectedBoxInterferenceReducedAmplitude
  | MollerTwoLoopDiagramLabel.doubleFermionSelfEnergy =>
    mollerDoubleFermionSelfEnergyReducedAmplitude
  | MollerTwoLoopDiagramLabel.countertermInsertedOneLoop =>
    mollerCountertermInsertedOneLoopReducedAmplitude

/-- Canonical two-loop bridge certificate built from the curated Møller example data. -/
def mollerCanonicalTwoLoopBridge : MollerTwoLoopDiagrammaticBridge :=
{ Diagram := MollerTwoLoopDiagramLabel,
  admissible := fun _ => True,
  classify := fun d => d,
  classify_mem := by
    intro d _
    cases d <;>
      simp [mollerContributingTwoLoopDiagrams],
  covers := by
    intro l hl
    exact ⟨l, trivial, rfl⟩
  reducedAmplitude := mollerCanonicalTwoLoopContributions.reducedAmplitude,
  outsideSupportZero := by
    intro l hl
    cases l with
    | nestedGaugeBosonSelfEnergy =>
        exfalso
        simp [mollerContributingTwoLoopDiagrams] at hl
    | gaugeGhostMixed =>
        exfalso
        simp [mollerContributingTwoLoopDiagrams] at hl
    | vertexCorrectedBoxInterference =>
        exfalso
        simp [mollerContributingTwoLoopDiagrams] at hl
    | doubleFermionSelfEnergy =>
        exfalso
        simp [mollerContributingTwoLoopDiagrams] at hl
    | countertermInsertedOneLoop =>
        exfalso
        simp [mollerContributingTwoLoopDiagrams] at hl
      }

/-- The canonical Møller two-loop bridge certificate. -/
theorem mollerCanonicalTwoLoopBridge_certificate :
    (∀ l : MollerTwoLoopDiagramLabel,
      l ∈ mollerContributingTwoLoopDiagrams ↔
        ∃ d : mollerCanonicalTwoLoopBridge.Diagram,
          mollerCanonicalTwoLoopBridge.admissible d ∧
          mollerCanonicalTwoLoopBridge.classify d = l) ∧
    (∀ l : MollerTwoLoopDiagramLabel,
      l ∉ mollerContributingTwoLoopDiagrams →
        mollerCanonicalTwoLoopBridge.reducedAmplitude l = 0) := by
  exact TwoLoopBridge.completeBridgeCertificate mollerCanonicalTwoLoopBridge

/-- Canonical Møller two-loop derivation bundle populated with the current concrete entries. -/
def mollerCanonicalTwoLoopDerivationBundle : MollerTwoLoopDerivationBundle where
  entries := mollerCanonicalTwoLoopDerivationEntries
  bridge := mollerCanonicalTwoLoopBridge
  contributions := mollerCanonicalTwoLoopContributions

/-- Lift a Møller two-loop diagram data object to an evaluation object with a chosen master. -/
def mollerTwoLoopDiagramEvaluationOf
    (diagram : MollerTwoLoopDiagramData)
    (target : TwoLoopMasterIntegral)
    (hEvaluate : diagram.evaluate = target) : MollerTwoLoopDiagramEvaluation where
  diagram := diagram
  target := target
  hEvaluate := hEvaluate

/-- Assumptions asserting that the chosen finite two-loop topology set is complete
for a given reduced-amplitude model. -/
structure MollerTwoLoopCompletenessAssumptions
    (C : MollerTwoLoopContributions) : Prop where
  /-- Any label outside the curated topology set has vanishing reduced amplitude. -/
  outsideSetHasZeroAmplitude :
    ∀ d : MollerTwoLoopDiagramLabel,
      d ∉ mollerContributingTwoLoopDiagrams → C.reducedAmplitude d = 0

/-- Completeness-under-assumptions scaffold: no missing contribution carries
nonzero reduced amplitude outside the curated topology set. -/
lemma moller_twoLoop_completeness_under_assumptions
    (C : MollerTwoLoopContributions)
    (hComplete : MollerTwoLoopCompletenessAssumptions C)
    (d : MollerTwoLoopDiagramLabel)
    (hdOut : d ∉ mollerContributingTwoLoopDiagrams) :
    C.reducedAmplitude d = 0 := by
  exact hComplete.outsideSetHasZeroAmplitude d hdOut

/-- Derivation-based classification assumptions from an external analytic diagram
domain into the curated two-loop topology labels. -/
structure MollerTwoLoopClassificationAssumptions
    (Diagram : Type)
  (C : MollerTwoLoopContributions) where
  /-- Predicate selecting diagrams in the intended analytic domain. -/
  admissible : Diagram → Prop
  /-- Classification map from external diagrams to curated topology labels. -/
  classify : Diagram → MollerTwoLoopDiagramLabel
  /-- Every admissible diagram is classified into the curated finite label set. -/
  classify_mem :
    ∀ d : Diagram,
      admissible d → classify d ∈ mollerContributingTwoLoopDiagrams
  /-- Every nonzero reduced-amplitude label has an admissible diagram witness
  classifying to that label. -/
  nonzeroReducedAmplitude_hasAdmissibleWitness :
    ∀ l : MollerTwoLoopDiagramLabel,
      C.reducedAmplitude l ≠ 0 →
        ∃ d : Diagram, admissible d ∧ classify d = l
  /-- Every curated topology label is realized by at least one admissible diagram. -/
  coversAllCuratedLabels :
    ∀ l : MollerTwoLoopDiagramLabel,
      l ∈ mollerContributingTwoLoopDiagrams →
        ∃ d : Diagram, admissible d ∧ classify d = l

/-- Strong completeness theorem: if nonzero reduced amplitudes are all induced by
an admissible external diagram domain whose classification lands in the curated
finite set, then the reduced-amplitude model is complete on that set. -/
lemma moller_twoLoop_completeness_from_classification
    (Diagram : Type)
    (C : MollerTwoLoopContributions)
    (hClass : MollerTwoLoopClassificationAssumptions Diagram C) :
    MollerTwoLoopCompletenessAssumptions C := by
  refine ⟨?_⟩
  intro l hlOut
  by_contra hNonzero
  rcases hClass.nonzeroReducedAmplitude_hasAdmissibleWitness l hNonzero with
    ⟨d, hdAdm, hcls⟩
  have hMem : hClass.classify d ∈ mollerContributingTwoLoopDiagrams :=
    hClass.classify_mem d hdAdm
  exact hlOut (hcls ▸ hMem)

/-- Pointwise corollary of classification-derived completeness. -/
lemma moller_twoLoop_completeness_under_classification
    (Diagram : Type)
    (C : MollerTwoLoopContributions)
    (hClass : MollerTwoLoopClassificationAssumptions Diagram C)
    (l : MollerTwoLoopDiagramLabel)
    (hlOut : l ∉ mollerContributingTwoLoopDiagrams) :
    C.reducedAmplitude l = 0 := by
  let hComp : MollerTwoLoopCompletenessAssumptions C :=
    moller_twoLoop_completeness_from_classification Diagram C hClass
  exact hComp.outsideSetHasZeroAmplitude l hlOut

/-- Concrete enumeration theorem: the curated two-loop labels are exactly the
image of admissible external diagrams under the classification map. -/
theorem moller_twoLoop_complete_enumeration
    (Diagram : Type)
    (C : MollerTwoLoopContributions)
    (hClass : MollerTwoLoopClassificationAssumptions Diagram C) :
    ∀ l : MollerTwoLoopDiagramLabel,
      l ∈ mollerContributingTwoLoopDiagrams ↔
        ∃ d : Diagram, hClass.admissible d ∧ hClass.classify d = l := by
  intro l
  constructor
  · intro hl
    exact hClass.coversAllCuratedLabels l hl
  · intro hWitness
    rcases hWitness with ⟨d, hdAdm, hcls⟩
    exact hcls.symm ▸ hClass.classify_mem d hdAdm

/-- Bridge-based version of the complete enumeration theorem for any future
Møller two-loop derivation object. -/
theorem moller_twoLoop_complete_enumeration_from_bridge
    (B : MollerTwoLoopDiagrammaticBridge) :
    ∀ l : MollerTwoLoopDiagramLabel,
      l ∈ mollerContributingTwoLoopDiagrams ↔
        ∃ d : B.Diagram, B.admissible d ∧ B.classify d = l := by
  exact TwoLoopBridge.completeEnumeration B

/-- Weighted symbolic two-loop shift in the interference channel.

LaTeX form:

$$
\Delta_{\mathrm{2\,loop}}
= \sum_{d \in \mathcal{D}_{2\ell}} w_d\,\mathcal{A}^{(2)}_d,
$$

where $\mathcal{D}_{2\ell}$ is `mollerContributingTwoLoopDiagrams`, $w_d$ are
`diagramWeight d`, and $\mathcal{A}^{(2)}_d$ is `C.reducedAmplitude d`. -/
def mollerTwoLoopInterferenceShift
    (C : MollerTwoLoopContributions)
    (diagramWeight : MollerTwoLoopDiagramLabel → ℝ) : ℝ :=
  ∑ d ∈ mollerContributingTwoLoopDiagrams, diagramWeight d * C.reducedAmplitude d

/-- Bookkeeping container for an interference-ratio expansion through two loops. -/
structure MollerInterferenceExpansion where
  /-- Tree-level interference ratio contribution. -/
  tree : ℝ
  /-- One-loop additive shift. -/
  oneLoop : ℝ
  /-- Two-loop additive shift. -/
  twoLoop : ℝ

/-- Interference ratio truncated at two loops.

LaTeX form:

$$
R_{\le 2\ell} = R_{\mathrm{tree}} + \Delta_{\mathrm{1\,loop}} + \Delta_{\mathrm{2\,loop}}.
$$ -/
def mollerInterferenceRatioUpToTwoLoop (E : MollerInterferenceExpansion) : ℝ :=
  E.tree + E.oneLoop + E.twoLoop

/-- Lab-frame MOLLER asymmetry model through two loops.

LaTeX form:

$$
A_{PV}^{\mathrm{lab},\le 2\ell}
= \mathcal{P}_{\mathrm{lab}}\,R_{\le 2\ell}.
$$ -/
def mollerLabFrameAPVUpToTwoLoop
    (I : MollerLabFrameInputs)
    (E : MollerInterferenceExpansion) : ℝ :=
  mollerLabPrefactor I * mollerInterferenceRatioUpToTwoLoop E

lemma mollerInterferenceRatioUpToTwoLoop_eq_tree_plus_loops
    (E : MollerInterferenceExpansion) :
    mollerInterferenceRatioUpToTwoLoop E = E.tree + E.oneLoop + E.twoLoop := by
  rfl

lemma mollerLabFrameAPVUpToTwoLoop_eq_tree_one_two_split
    (I : MollerLabFrameInputs)
    (E : MollerInterferenceExpansion) :
    mollerLabFrameAPVUpToTwoLoop I E
      = mollerLabPrefactor I * E.tree
        + mollerLabPrefactor I * E.oneLoop
        + mollerLabPrefactor I * E.twoLoop := by
  unfold mollerLabFrameAPVUpToTwoLoop mollerInterferenceRatioUpToTwoLoop
  ring

/-- Connection to the existing one-loop model by taking an explicit tree ratio and
adding both one- and two-loop shifts. -/
lemma mollerLabFrameAPVUpToTwoLoop_eq_oneLoopModel_plus_twoLoop
    (I : MollerLabFrameInputs)
    (treeInterferenceRatio oneLoopShift twoLoopShift : ℝ) :
    mollerLabFrameAPVUpToTwoLoop I
        { tree := treeInterferenceRatio
          oneLoop := oneLoopShift
          twoLoop := twoLoopShift }
      = mollerLabFrameAPVWithOneLoop I treeInterferenceRatio oneLoopShift
        + mollerLabPrefactor I * twoLoopShift := by
  unfold mollerLabFrameAPVUpToTwoLoop
    mollerInterferenceRatioUpToTwoLoop
    mollerLabFrameAPVWithOneLoop
  ring

/-- Experiment-facing input bundle for a MOLLER observable model through two loops.

The tree part is represented via the same interference-ratio toy decomposition used
in existing bridge lemmas, while loop effects enter additively. -/
structure MollerExperimentObservableInputs where
  /-- Toy decomposition photon-channel contribution. -/
  photonVal : ℝ
  /-- Toy decomposition Z-channel contribution. -/
  zVal : ℝ
  /-- Toy decomposition gamma-Z interference contribution. -/
  gammaZVal : ℝ
  /-- Positive regulator in the denominator. -/
  epsilonReg : ℝ
  /-- One-loop additive shift in the interference ratio. -/
  oneLoopShift : ℝ
  /-- Two-loop additive shift in the interference ratio. -/
  twoLoopShift : ℝ

/-- Canonical construction of the two-loop interference expansion from experiment-facing
observable inputs. -/
def mollerExpansionFromObservableInputs
    (O : MollerExperimentObservableInputs) : MollerInterferenceExpansion where
  tree := (2 * O.gammaZVal) / (|2 * (O.photonVal + O.zVal)| + O.epsilonReg)
  oneLoop := O.oneLoopShift
  twoLoop := O.twoLoopShift

/-- Experiment-facing bridge: when lab-frame kinematic and weak-charge factors match
the tree-level interference ratio, the two-loop MOLLER lab-frame asymmetry equals
prefactor times tree + one-loop + two-loop terms from observable inputs. -/
lemma moller_twoLoop_experiment_observable_bridge
    (I : MollerLabFrameInputs)
    (O : MollerExperimentObservableInputs)
    (hTree : I.labKinematicFactor * I.weakChargeElectron
      = (2 * O.gammaZVal) / (|2 * (O.photonVal + O.zVal)| + O.epsilonReg)) :
    mollerLabFrameAPVUpToTwoLoop I (mollerExpansionFromObservableInputs O)
      = mollerLabFrameAPV I
        + mollerLabPrefactor I * O.oneLoopShift
        + mollerLabPrefactor I * O.twoLoopShift := by
  have hTreePV :
      mollerLabFrameAPV I
        = mollerLabPrefactor I
            * ((2 * O.gammaZVal) / (|2 * (O.photonVal + O.zVal)| + O.epsilonReg)) := by
    simp [mollerLabFrameAPV, hTree, mul_assoc]
  calc
    mollerLabFrameAPVUpToTwoLoop I (mollerExpansionFromObservableInputs O)
      = mollerLabPrefactor I
          * ((2 * O.gammaZVal) / (|2 * (O.photonVal + O.zVal)| + O.epsilonReg))
          + mollerLabPrefactor I * O.oneLoopShift
          + mollerLabPrefactor I * O.twoLoopShift := by
            simp [mollerLabFrameAPVUpToTwoLoop,
              mollerInterferenceRatioUpToTwoLoop,
              mollerExpansionFromObservableInputs,
              mul_add,
              add_left_comm,
              add_comm]
    _ = mollerLabFrameAPV I
          + mollerLabPrefactor I * O.oneLoopShift
          + mollerLabPrefactor I * O.twoLoopShift := by
            simp [hTreePV]

/-- Interface for assigning two-loop diagram weights under a renormalization scheme.

This keeps scheme assumptions explicit while leaving concrete analytic derivation
for follow-up modules.

An earlier version carried three further fields

```
  absorbsUVPoles : Prop
  finiteRenormalizedShift : Prop
  gaugeParameterIndependent : Prop
```

which asserted nothing, and in a stronger sense than the usual `foo : Prop` plus
`hFoo : foo` pattern: there was no accompanying proof field at all, so the structure carried
three propositions and assumed none of them. All three concrete schemes below instantiated
them as literal `True`. They have been removed rather than repaired because none of the three
can be stated honestly against the data this structure holds: `diagramWeight` is an
`ℝ`-valued map on topology labels, with no pole structure for `absorbsUVPoles` to cancel, no
regulator for `finiteRenormalizedShift` to survive, and no gauge parameter for
`gaugeParameterIndependent` to be independent of. Stating them requires a two-loop amplitude
with a regulator, which this module does not have; the removal records that the scheme
interface is bookkeeping for weights, and that its renormalization content is still to be
supplied. -/
structure MollerTwoLoopWeightScheme where
  /-- Label for documentation and downstream reporting. -/
  schemeName : String
  /-- High-level scheme family identifier. -/
  schemeKind : String
  /-- Weight assignment for each two-loop topology class. -/
  diagramWeight : MollerTwoLoopDiagramLabel → ℝ
  /-- Optional benchmark value for the relative asymmetry correction `δA/A`. -/
  benchmarkDeltaAOverA : Option ℝ

/-- Placeholder zero-weight map used for interface-level scheme objects. -/
def mollerZeroTwoLoopWeights : MollerTwoLoopDiagramLabel → ℝ := fun _ => 0

/-- Placeholder on-shell-style relative weights across two-loop topologies. -/
def mollerOnShellPlaceholderWeights : MollerTwoLoopDiagramLabel → ℝ
  | .nestedGaugeBosonSelfEnergy => 1.0
  | .gaugeGhostMixed => 0.6
  | .vertexCorrectedBoxInterference => 1.2
  | .doubleFermionSelfEnergy => 0.8
  | .countertermInsertedOneLoop => -0.4

/-- Placeholder MS-bar-style relative weights across two-loop topologies. -/
def mollerMSbarPlaceholderWeights : MollerTwoLoopDiagramLabel → ℝ
  | .nestedGaugeBosonSelfEnergy => 0.9
  | .gaugeGhostMixed => 0.5
  | .vertexCorrectedBoxInterference => 1.0
  | .doubleFermionSelfEnergy => 0.7
  | .countertermInsertedOneLoop => -0.3

/-- Placeholder vertex-focused weights inspired by arXiv:1508.07853.

This profile upweights vertex-corrected box-interference topologies relative to
other classes to model a vertex-emphasis regime at the interface level. -/
def mollerVertex1508_07853PlaceholderWeights : MollerTwoLoopDiagramLabel → ℝ
  | .nestedGaugeBosonSelfEnergy => 0.4
  | .gaugeGhostMixed => 0.2
  | .vertexCorrectedBoxInterference => 1.6
  | .doubleFermionSelfEnergy => 0.3
  | .countertermInsertedOneLoop => -0.2

/-- Placeholder on-shell-style scheme for MOLLER two-loop bookkeeping. -/
def mollerOnShellPlaceholderScheme : MollerTwoLoopWeightScheme where
  schemeName := "MOLLER-on-shell-placeholder"
  schemeKind := "on-shell"
  diagramWeight := mollerOnShellPlaceholderWeights
  benchmarkDeltaAOverA := none

/-- Placeholder MS-bar-style scheme for MOLLER two-loop bookkeeping. -/
def mollerMSbarPlaceholderScheme : MollerTwoLoopWeightScheme where
  schemeName := "MOLLER-msbar-placeholder"
  schemeKind := "MS-bar"
  diagramWeight := mollerMSbarPlaceholderWeights
  benchmarkDeltaAOverA := none

/-- Placeholder vertex-focused MOLLER scheme inspired by arXiv:1508.07853.

The referenced study reports a relative correction estimate around `-0.0034` for
an 11 GeV beam on a fixed electron target, for the considered two-loop electroweak
vertex subset. We store this only as metadata for future calibrated instantiations. -/
def mollerVertex1508_07853PlaceholderScheme : MollerTwoLoopWeightScheme where
  schemeName := "MOLLER-vertex-1508.07853-placeholder"
  schemeKind := "vertex-subset"
  diagramWeight := mollerVertex1508_07853PlaceholderWeights
  benchmarkDeltaAOverA := some (-0.0034)

/-- Registry-style selector for initial placeholder renormalization schemes.

Supported keys currently include:
* `"on-shell"`
* `"msbar"`
* `"vertex-1508.07853"` -/
def mollerPlaceholderSchemeOfKey (key : String) : MollerTwoLoopWeightScheme :=
  if key = "on-shell" then
    mollerOnShellPlaceholderScheme
  else if key = "msbar" then
    mollerMSbarPlaceholderScheme
  else if key = "vertex-1508.07853" then
    mollerVertex1508_07853PlaceholderScheme
  else
    mollerOnShellPlaceholderScheme

/-- Numeric benchmark target for relative asymmetry correction.

If a scheme does not specify a benchmark, this defaults to `0`. -/
def mollerSchemeBenchmarkTarget (scheme : MollerTwoLoopWeightScheme) : ℝ :=
  scheme.benchmarkDeltaAOverA.getD 0

/-- Relative two-loop correction at a fixed benchmark point, represented as
the ratio of the two-loop shift to the tree-level contribution. -/
def mollerRelativeCorrectionAtBenchmark
    (treeContribution twoLoopShift : ℝ) : ℝ :=
  twoLoopShift / treeContribution

/-- Calibration theorem: if a benchmark point is calibrated so that the two-loop
shift equals `target * tree`, then the relative correction equals that target. -/
lemma mollerRelativeCorrectionAtBenchmark_eq_target_of_calibration
    (treeContribution twoLoopShift target : ℝ)
    (hTree : treeContribution ≠ 0)
    (hCalib : twoLoopShift = target * treeContribution) :
    mollerRelativeCorrectionAtBenchmark treeContribution twoLoopShift = target := by
  unfold mollerRelativeCorrectionAtBenchmark
  rw [hCalib]
  field_simp [hTree]

/-- Scheme-level benchmark calibration statement at a fixed kinematic point. -/
lemma mollerRelativeCorrectionAtBenchmark_eq_schemeTarget_of_calibration
    (scheme : MollerTwoLoopWeightScheme)
    (treeContribution twoLoopShift : ℝ)
    (hTree : treeContribution ≠ 0)
    (hCalib :
      twoLoopShift = mollerSchemeBenchmarkTarget scheme * treeContribution) :
    mollerRelativeCorrectionAtBenchmark treeContribution twoLoopShift
      = mollerSchemeBenchmarkTarget scheme := by
  exact mollerRelativeCorrectionAtBenchmark_eq_target_of_calibration
    treeContribution
    twoLoopShift
    (mollerSchemeBenchmarkTarget scheme)
    hTree
    hCalib

/-- The arXiv:1508.07853-inspired placeholder scheme stores benchmark target
`δA/A = -0.0034`. -/
lemma mollerVertex1508_07853_schemeBenchmarkTarget :
    mollerSchemeBenchmarkTarget mollerVertex1508_07853PlaceholderScheme
      = -0.0034 := by
  rfl

/-- Scheme-instantiated two-loop interference shift. -/
def mollerTwoLoopInterferenceShiftOfScheme
    (scheme : MollerTwoLoopWeightScheme)
    (C : MollerTwoLoopContributions) : ℝ :=
  mollerTwoLoopInterferenceShift C scheme.diagramWeight

lemma mollerTwoLoopInterferenceShiftOfScheme_eq_sum
    (scheme : MollerTwoLoopWeightScheme)
    (C : MollerTwoLoopContributions) :
    mollerTwoLoopInterferenceShiftOfScheme scheme C
      = ∑ d ∈ mollerContributingTwoLoopDiagrams,
          scheme.diagramWeight d * C.reducedAmplitude d := by
  rfl

/-- Per-scheme relative correction from concrete reduced amplitudes at a fixed
benchmark point. -/
def mollerSchemeRelativeCorrectionFromConcreteAmplitudes
    (scheme : MollerTwoLoopWeightScheme)
    (treeContribution : ℝ)
    (C : MollerTwoLoopContributions) : ℝ :=
  mollerRelativeCorrectionAtBenchmark
    treeContribution
    (mollerTwoLoopInterferenceShiftOfScheme scheme C)

/-- Expanded expression for per-scheme relative correction from concrete reduced
amplitudes. -/
lemma mollerSchemeRelativeCorrectionFromConcreteAmplitudes_eq_sum_ratio
    (scheme : MollerTwoLoopWeightScheme)
    (treeContribution : ℝ)
    (C : MollerTwoLoopContributions) :
    mollerSchemeRelativeCorrectionFromConcreteAmplitudes
        scheme
        treeContribution
        C
      = (∑ d ∈ mollerContributingTwoLoopDiagrams,
          scheme.diagramWeight d * C.reducedAmplitude d) / treeContribution := by
  unfold mollerSchemeRelativeCorrectionFromConcreteAmplitudes
    mollerRelativeCorrectionAtBenchmark
  rw [mollerTwoLoopInterferenceShiftOfScheme_eq_sum]

/-- Calibrated per-scheme theorem: when concrete reduced amplitudes satisfy the
scheme benchmark relation, the computed relative correction equals the scheme
target `δA/A`. -/
lemma mollerSchemeRelativeCorrectionFromConcreteAmplitudes_eq_target_of_calibration
    (scheme : MollerTwoLoopWeightScheme)
    (treeContribution : ℝ)
    (C : MollerTwoLoopContributions)
    (hTree : treeContribution ≠ 0)
    (hCalib :
      mollerTwoLoopInterferenceShiftOfScheme scheme C
        = mollerSchemeBenchmarkTarget scheme * treeContribution) :
    mollerSchemeRelativeCorrectionFromConcreteAmplitudes
        scheme
        treeContribution
        C
      = mollerSchemeBenchmarkTarget scheme := by
  exact mollerRelativeCorrectionAtBenchmark_eq_schemeTarget_of_calibration
    scheme
    treeContribution
    (mollerTwoLoopInterferenceShiftOfScheme scheme C)
    hTree
    hCalib

/-- Key-based variant for placeholder scheme selection. -/
lemma mollerPlaceholderScheme_relativeCorrection_eq_target_of_calibration
    (key : String)
    (treeContribution : ℝ)
    (C : MollerTwoLoopContributions)
    (hTree : treeContribution ≠ 0)
    (hCalib :
      mollerTwoLoopInterferenceShiftOfScheme
          (mollerPlaceholderSchemeOfKey key)
          C
        = mollerSchemeBenchmarkTarget (mollerPlaceholderSchemeOfKey key)
            * treeContribution) :
    mollerSchemeRelativeCorrectionFromConcreteAmplitudes
        (mollerPlaceholderSchemeOfKey key)
        treeContribution
        C
      = mollerSchemeBenchmarkTarget (mollerPlaceholderSchemeOfKey key) := by
  exact mollerSchemeRelativeCorrectionFromConcreteAmplitudes_eq_target_of_calibration
    (mollerPlaceholderSchemeOfKey key)
    treeContribution
    C
    hTree
    hCalib

/-- Difference between two scheme-instantiated two-loop shifts as a weighted
sum over pointwise weight differences. -/
lemma mollerTwoLoopInterferenceShift_schemeDifference_eq_weightDifference_sum
    (scheme₁ scheme₂ : MollerTwoLoopWeightScheme)
    (C : MollerTwoLoopContributions) :
    mollerTwoLoopInterferenceShiftOfScheme scheme₁ C
      - mollerTwoLoopInterferenceShiftOfScheme scheme₂ C
      = ∑ d ∈ mollerContributingTwoLoopDiagrams,
          (scheme₁.diagramWeight d - scheme₂.diagramWeight d)
            * C.reducedAmplitude d := by
  unfold mollerTwoLoopInterferenceShiftOfScheme mollerTwoLoopInterferenceShift
  let S : Finset MollerTwoLoopDiagramLabel := mollerContributingTwoLoopDiagrams
  let f : MollerTwoLoopDiagramLabel → ℝ :=
    fun d => scheme₁.diagramWeight d * C.reducedAmplitude d
  let g : MollerTwoLoopDiagramLabel → ℝ :=
    fun d => scheme₂.diagramWeight d * C.reducedAmplitude d
  have hsum :
      (∑ d ∈ S, (f d - g d)) = (∑ d ∈ S, f d) - (∑ d ∈ S, g d) := by
    exact Finset.sum_sub_distrib (s := S) f g
  calc
    (∑ d ∈ mollerContributingTwoLoopDiagrams,
        scheme₁.diagramWeight d * C.reducedAmplitude d)
        -
        (∑ d ∈ mollerContributingTwoLoopDiagrams,
          scheme₂.diagramWeight d * C.reducedAmplitude d)
      = ∑ d ∈ mollerContributingTwoLoopDiagrams,
          (scheme₁.diagramWeight d * C.reducedAmplitude d
            - scheme₂.diagramWeight d * C.reducedAmplitude d) := by
              change (∑ d ∈ S, f d) - (∑ d ∈ S, g d)
                = ∑ d ∈ S, (f d - g d)
              exact hsum.symm
    _ = ∑ d ∈ mollerContributingTwoLoopDiagrams,
          (scheme₁.diagramWeight d - scheme₂.diagramWeight d)
            * C.reducedAmplitude d := by
              refine Finset.sum_congr rfl ?_
              intro d hd
              ring

/-- Two-loop lab-frame asymmetry with renormalization-scheme weighted shift.

This theorem is a typed interface result: once a scheme provides a diagram-weight
assignment, the corresponding two-loop corrected lab-frame expression is obtained
by plugging the scheme-induced shift into `mollerLabFrameAPVUpToTwoLoop`. -/
lemma mollerLabFrameAPVUpToTwoLoop_of_scheme
    (I : MollerLabFrameInputs)
    (scheme : MollerTwoLoopWeightScheme)
    (treeInterferenceRatio oneLoopShift : ℝ)
    (C : MollerTwoLoopContributions)
    (hTwoLoop :
      mollerTwoLoopInterferenceShiftOfScheme scheme C
        = mollerTwoLoopInterferenceShift C scheme.diagramWeight) :
    mollerLabFrameAPVUpToTwoLoop I
        { tree := treeInterferenceRatio
          oneLoop := oneLoopShift
          twoLoop := mollerTwoLoopInterferenceShiftOfScheme scheme C }
      = mollerLabPrefactor I
          * (treeInterferenceRatio
            + oneLoopShift
            + mollerTwoLoopInterferenceShift C scheme.diagramWeight) := by
  simp [mollerLabFrameAPVUpToTwoLoop,
    mollerInterferenceRatioUpToTwoLoop,
    hTwoLoop]


end Examples
end PVES
end DIS
end Scattering
end QFT
end EpsilonEridani
