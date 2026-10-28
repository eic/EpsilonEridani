/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Reversing the coordinates of a tuple

The coordinate reversal `p ↦ p ∘ Fin.rev` on `Fin n → α` is the measurable equivalence that
the permutation `Fin.revPerm` induces through `MeasurableEquiv.piCongrLeft`
(`coe_piCongrLeft_revPerm`).  Hence it is a measurable embedding
(`measurableEmbedding_comp_rev`) and preserves the product volume
(`volume_preserving_comp_rev`), which is what a change of variables along the reversal
needs.  The descending ordered region of `EpsilonEridani.Mathematics.OrderedSimplexIntegral`
is reduced to the ascending one this way.
-/

@[expose] public section

namespace EpsilonEridani

open MeasureTheory

variable {α : Type*}

/-- Reversing the coordinates of a tuple twice gives the tuple back. -/
lemma comp_rev_comp_rev {n : ℕ} (p : Fin n → α) : (p ∘ Fin.rev) ∘ Fin.rev = p := by
  rw [Function.comp_assoc, Fin.rev_involutive.comp_self, Function.comp_id]

/-- The measurable equivalence that `Fin.revPerm` induces on `Fin n → α` is the coordinate
reversal `p ↦ p ∘ Fin.rev`. -/
lemma coe_piCongrLeft_revPerm [MeasurableSpace α] (n : ℕ) :
    ⇑(MeasurableEquiv.piCongrLeft (fun _ : Fin n => α) Fin.revPerm) =
      fun p : Fin n → α => p ∘ Fin.rev := by
  funext p i
  obtain ⟨j, rfl⟩ := Fin.revPerm.surjective i
  rw [MeasurableEquiv.piCongrLeft_apply_apply, Function.comp_apply, Fin.revPerm_apply,
    Fin.rev_rev]

/-- Coordinate reversal is a measurable embedding of `Fin n → α` into itself. -/
lemma measurableEmbedding_comp_rev [MeasurableSpace α] (n : ℕ) :
    MeasurableEmbedding fun p : Fin n → α => p ∘ Fin.rev := by
  rw [← coe_piCongrLeft_revPerm]
  exact (MeasurableEquiv.piCongrLeft _ _).measurableEmbedding

/-- Coordinate reversal preserves the product volume on `Fin n → α`. -/
lemma volume_preserving_comp_rev [MeasureSpace α] [SigmaFinite (volume : Measure α)] (n : ℕ) :
    MeasurePreserving (fun p : Fin n → α => p ∘ Fin.rev) volume volume := by
  rw [← coe_piCongrLeft_revPerm]
  exact volume_measurePreserving_piCongrLeft _ _

end EpsilonEridani
