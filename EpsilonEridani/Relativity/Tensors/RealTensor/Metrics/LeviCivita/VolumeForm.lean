/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.Relativity.Tensors.RealTensor.Metrics.LeviCivita.Basic
public import EpsilonEridani.Relativity.Tensors.RealTensor.Vector.VolumeForm

/-!
# The volume form and the integer Levi-Civita symbols

Relates the volume form `EpsilonEridani.minkowskiVolumeForm` of four-dimensional Minkowski space
(`EpsilonEridani.Relativity.Tensors.RealTensor.Vector.VolumeForm`, with `ε^{0123} = +1`) to the
integer Levi-Civita symbols of
`EpsilonEridani.Relativity.Tensors.RealTensor.Metrics.LeviCivita.Basic`.

The two use opposite sign conventions. There, `realLorentzTensor.leviCivita4Int`, documented as
the covariant symbol, is `leviCivitaSymbol` (`ε_{0123} = +1`), and
`realLorentzTensor.leviCivita4UpInt`, documented as the contravariant symbol, is its negative.
The covariant components `ε_{μνρσ} = -leviCivitaSymbol (μ, ν, ρ, σ)` of `minkowskiVolumeForm` are
therefore `-leviCivita4Int`.

This bridge is a module of its own so that the volume form does not import `LeviCivita.Basic`,
and `LeviCivita.Basic`, which is in Physlib's `realLorentzTensor` namespace, imports nothing
from EpsilonEridani.

## Main statements

* `EpsilonEridani.minkowskiVolumeForm_minkowskiBasisFin4_eq_neg_leviCivita4Int`: the covariant
  components of the volume form are `-leviCivita4Int`.
-/

public section

namespace EpsilonEridani

/-- The covariant components of the volume form are minus the integer covariant symbol
`leviCivita4Int`: `ε_{μνρσ} = -leviCivita4Int μ ν ρ σ = -leviCivitaSymbol (μ, ν, ρ, σ)`. -/
theorem minkowskiVolumeForm_minkowskiBasisFin4_eq_neg_leviCivita4Int (μ ν ρ σ : Fin 4) :
    minkowskiVolumeForm ![minkowskiBasisFin4 μ, minkowskiBasisFin4 ν, minkowskiBasisFin4 ρ,
        minkowskiBasisFin4 σ] = -(realLorentzTensor.leviCivita4Int μ ν ρ σ : ℝ) := by
  have h : ![minkowskiBasisFin4 μ, minkowskiBasisFin4 ν, minkowskiBasisFin4 ρ,
      minkowskiBasisFin4 σ] = minkowskiBasisFin4 ∘ ![μ, ν, ρ, σ] := by
    simp only [Matrix.vecCons, Fin.comp_cons, Matrix.empty_eq (minkowskiBasisFin4 ∘ ![])]
  rw [h, Function.comp_def, minkowskiVolumeForm_minkowskiBasisFin4_comp ![μ, ν, ρ, σ],
    realLorentzTensor.leviCivita4Int_eq_leviCivitaSymbol]

end EpsilonEridani
