/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import EpsilonEridani.Particles.Parton.GTMD.Transverse
/-!

# GTMD Object Model

A `TMD.Tmd` is a function of the transverse-momentum *magnitude* `kT`, so it cannot express
any dependence on the direction of the transverse-momentum vector. This module introduces the
object that can: a `VectorTmd`, a transverse-momentum dependent distribution whose
transverse-momentum argument is a genuine vector in the transverse plane, together with its
structural assumptions. The azimuthal average that maps a `VectorTmd` into `TMD.Tmd` is
defined in `EpsilonEridani.Particles.Parton.GTMD.Average`.

The assumption bundle separates what it *means* to be a vector-argument density from
the analytic regularity the analysis needs; `VectorTmd.assumptions_iff` records that the
split is exact. Both bundles are namespaced to `VectorTmd` because the unqualified
`GTMD.Regularity` and `GTMD.Assumptions` are reserved for correlator-level bundles.

## Main definitions

* `VectorTmd`: a transverse-momentum dependent distribution whose transverse-momentum
  argument is a vector in `Transverse`.
* `IsVectorTmdDensity`: the vector-argument analogue of `TMD.IsTmdDensity`.
* `VectorTmd.Regularity`: the vector-argument analogue of `TMD.Regularity`, the analytic
  half of the assumption bundle: continuity of every transverse-momentum slice.
* `VectorTmd.Assumptions`: the full vector-argument assumption bundle, extending the physical
  conditions of `IsVectorTmdDensity` with the analytic condition of `VectorTmd.Regularity`.

## Main results

* `VectorTmd.assumptions_iff`: the split of the vector-argument assumption bundle into its
  physical and analytic halves is exact.
-/

@[expose] public section

noncomputable section

namespace EpsilonEridani
namespace Particles
namespace Parton
namespace GTMD

variable {Flavor : Type}

/-- A transverse-momentum dependent distribution `f i x kT Q2 ζ` whose transverse-momentum
    argument `kT` is a vector in the transverse plane rather than a magnitude. -/
abbrev VectorTmd (Flavor : Type) : Type := Flavor → ℝ → Transverse → ℝ → ℝ → ℝ

/-- The vector-argument analogue of `TMD.IsTmdDensity`: support in `x ∈ [0, 1]` and
    nonnegativity there. -/
structure IsVectorTmdDensity (f : VectorTmd Flavor) : Prop where
  /-- The density vanishes outside the physical range `[0, 1]` of the momentum fraction. -/
  supportX : ∀ i x kT Q2 ζ, x < 0 ∨ 1 < x → f i x kT Q2 ζ = 0
  /-- The density is nonnegative on the physical range of the momentum fraction. -/
  nonneg : ∀ i x kT Q2 ζ, 0 ≤ x → x ≤ 1 → 0 ≤ f i x kT Q2 ζ

/-! ### The analytic/physical split of `VectorTmd.Assumptions`

As in the transverse-magnitude case (`EpsilonEridani.Particles.Parton.TMD.Assumptions`) the
bundle mixes a definition with an obligation. `IsVectorTmdDensity` is the physical half —
support in `x` and nonnegativity on the physical region — and is what "vector-argument
transverse-momentum-dependent parton density" means. `VectorTmd.Regularity` is the analytic
half, continuity of the transverse-momentum slices; it is what transports to measurability of
the azimuthal average in the transverse-momentum magnitude
(`regularity_azimuthalAverage` in `EpsilonEridani.Particles.Parton.GTMD.Average`).
`VectorTmd.assumptions_iff` records that the split is exact.
-/

/-- **The analytic half of the vector-argument assumption bundle**: continuity of every
    transverse-momentum slice. -/
structure VectorTmd.Regularity (f : VectorTmd Flavor) : Prop where
  /-- `f i x · Q2 ζ` is continuous as a function of the transverse-momentum vector. -/
  continuousKT : ∀ i x Q2 ζ, Continuous (fun w : Transverse => f i x w Q2 ζ)

/-- Structural assumptions for vector-argument TMD objects: the physical conditions of
    `IsVectorTmdDensity` together with the analytic condition of `VectorTmd.Regularity`,
    declared by extension, so the two halves are the projections
    `VectorTmd.Assumptions.toIsVectorTmdDensity` and `VectorTmd.Assumptions.toRegularity`. -/
structure VectorTmd.Assumptions (f : VectorTmd Flavor) : Prop extends
    IsVectorTmdDensity f, VectorTmd.Regularity f

/-- The split is exact: `VectorTmd.Assumptions` is the conjunction of the physical and the
    analytic half, with no residue. -/
lemma VectorTmd.assumptions_iff {f : VectorTmd Flavor} :
    VectorTmd.Assumptions f ↔ IsVectorTmdDensity f ∧ VectorTmd.Regularity f :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

end GTMD
end Parton
end Particles
end EpsilonEridani
