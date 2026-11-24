/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.Relativity.Tensors.RealTensor.Metrics.LeviCivita
public import EpsilonEridani.Relativity.Tensors.RealTensor.Vector.VolumeForm

/-!
# The volume form and the integer Levi-Civita symbols

Relates the volume form `EpsilonEridani.minkowskiVolumeForm` of four-dimensional Minkowski space
(`EpsilonEridani.Relativity.Tensors.RealTensor.Vector.VolumeForm`, with `ε^{0123} = +1`) to the
integer Levi-Civita symbols of `EpsilonEridani.Relativity.Tensors.RealTensor.Metrics.LeviCivita`.

The two use opposite sign conventions. There, `realLorentzTensor.leviCivita4Int` is
`leviCivitaSymbol`, and `realLorentzTensor.leviCivita4UpInt`, documented as the contravariant
symbol, is its negative, i.e. `ε^{0123} = -1`. Numerically, the covariant components
`ε_{μνρσ} = -leviCivitaSymbol (μ, ν, ρ, σ)` of `minkowskiVolumeForm` are therefore the values of
`leviCivita4UpInt`.

This bridge is a module of its own so that `LeviCivita`, which imports all of Mathlib, is not
imported by the volume form, and the volume form is not imported by `LeviCivita`.

## Main statements

* `EpsilonEridani.minkowskiVolumeForm_minkowskiBasisFin4_eq_leviCivita4UpInt`: the components of
  the volume form are the values of `leviCivita4UpInt`.
-/

public section

namespace EpsilonEridani

/-- The covariant components of the volume form are the values of the integer symbol
`leviCivita4UpInt`: `ε_{μνρσ} = leviCivita4UpInt μ ν ρ σ = -leviCivitaSymbol (μ, ν, ρ, σ)`. -/
theorem minkowskiVolumeForm_minkowskiBasisFin4_eq_leviCivita4UpInt (μ ν ρ σ : Fin 4) :
    minkowskiVolumeForm ![minkowskiBasisFin4 μ, minkowskiBasisFin4 ν, minkowskiBasisFin4 ρ,
        minkowskiBasisFin4 σ] = (realLorentzTensor.leviCivita4UpInt μ ν ρ σ : ℝ) := by
  have h : ![minkowskiBasisFin4 μ, minkowskiBasisFin4 ν, minkowskiBasisFin4 ρ,
      minkowskiBasisFin4 σ] = minkowskiBasisFin4 ∘ ![μ, ν, ρ, σ] := by
    simp only [Matrix.vecCons, Fin.comp_cons, Matrix.empty_eq (minkowskiBasisFin4 ∘ ![])]
  rw [h, Function.comp_def, minkowskiVolumeForm_minkowskiBasisFin4_comp ![μ, ν, ρ, σ],
    realLorentzTensor.leviCivita4UpInt_eq_neg, Int.cast_neg,
    realLorentzTensor.leviCivita4Int_eq_leviCivitaSymbol]

end EpsilonEridani
