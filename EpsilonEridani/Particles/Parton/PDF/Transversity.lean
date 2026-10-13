/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import EpsilonEridani.Particles.Parton.PDF.Positivity
/-!

# Absence of gluon transversity for a spin-half target

This module proves that a spin-half target admits no gluon transversity. The argument
is angular-momentum counting: a gluon transversity density would be the matrix element of
an operator changing the total helicity by two units, which a two-state system cannot
execute.  The spin-one case is provided for contrast.

The claim enters SpinStructure Layer 1.5 ("Gluon transversity and evolution")
as the key structural fact needed before stating the consequence for the evolution
equation; that consequence must be phrased against the collinear-evolution kernels,
which are not yet in the library, and is left to a follow-up.  The claim proved here is
purely combinatorial: it concerns which helicity changes can occur in a forward matrix
element, and it does not depend on the dynamics of the parton distributions.

Reference: P. Hoodbhoy, R. L. Jaffe and A. Manohar, *Novel effects in deep inelastic
scattering from spin-one hadrons*, Nucl. Phys. B **312** (1989) 571, §3.
-/

@[expose] public section

namespace EpsilonEridani
namespace Particles
namespace Parton
namespace PDF

/-!
## Allowed helicity changes in a forward matrix element

For a hadronic target of spin `J` (represented as `twoJ : ℕ`, so that `J = twoJ / 2`),
the magnetic quantum numbers `m` and `m'` are encoded doubled, as integers: they satisfy
`|m| ≤ twoJ` and `|m'| ≤ twoJ` together with the parity conditions `m ≡ twoJ (mod 2)`
and `m' ≡ twoJ (mod 2)`.  A forward matrix element `⟨m'| O |m⟩` of an operator `O`
carrying angular momentum `J` can only connect states whose helicity change
`d = (m - m') / 2`, measured in ordinary units, is recorded in `helicityChanges twoJ`.

A parton operator that flips the parton helicity by ±2 contributes `±2` to the total
helicity change.  Hence a gluon transversity operator — which flips a gluon's helicity
by two units — can contribute to a forward matrix element only if
`±2 ∈ helicityChanges twoJ`.

The definition below mirrors the roadmap specification
`EpsilonEridaniRoadmaps.SpinStructure.Suggested.lean`.
-/

/-- The set of helicity changes `d : ℤ`, measured in ordinary units, that can occur in
a forward matrix element between two states of a target with spin `J` (represented as
`twoJ : ℕ`, so that `J = twoJ / 2`).

The conditions are: `m` and `m'` are doubled magnetic quantum numbers with
`|m| ≤ twoJ`, `|m'| ≤ twoJ`, and the parity conditions `m ≡ twoJ (mod 2)` and
`m' ≡ twoJ (mod 2)`.  The helicity change is `d = (m - m') / 2` in ordinary units,
which is why the defining equation is `2 * d = m - m'`. -/
def helicityChanges (twoJ : ℕ) : Set ℤ :=
  {d | ∃ (m m' : ℤ),
    m.natAbs ≤ twoJ ∧ m'.natAbs ≤ twoJ ∧
    (m - (twoJ : ℤ)) % 2 = 0 ∧ (m' - (twoJ : ℤ)) % 2 = 0 ∧
    2 * d = m - m'}

/-- A gluon transversity operator changes the gluon helicity by ±2, which in a
forward matrix element produces a total helicity change of ±2. -/
abbrev gluonTransversityHelicityChange : ℤ := 2

/-! ### Spin-half: no gluon transversity -/

/-- For a spin-half target (`J = ½`, `twoJ = 1`), a helicity change of `2` is
impossible.

The target Hilbert space has two magnetic sublevels (`m = ±½`).  In the doubled
integer convention used throughout this module, these correspond to
`m = 1` and `m = -1`.  The maximum doubled difference is `m - m' = 2` (when
`m = 1` and `m' = -1`), so the doubled difference `m - m' = 4` required for the
matrix element of a gluon-transversity operator — whose helicity change is
`d = 2` — exceeds the available range.  Geometrically: a spin-½ target has
`helicityChanges 1 = {-1, 0, 1}`; `2` is not in this set.

This is the core angular-momentum counting argument for the absence of gluon
transversity in a spin-half hadron. -/
theorem not_gluonTransversityHelicityChange_in_helicityChanges_one
    : gluonTransversityHelicityChange ∉ helicityChanges 1 := by
  rintro ⟨m, m', hm_le, hm'_le, -, -, h_eq⟩
  -- From the defining equation `2 * 2 = m - m'` we get `m - m' = 4`, but `|m| ≤ 1` and
  -- `|m'| ≤ 1` bound the difference by `2`.
  simp only [gluonTransversityHelicityChange] at h_eq
  omega

/-! ### Spin-one: gluon transversity is allowed -/

/-- For a spin-one target (`J = 1`, `twoJ = 2`), a helicity change of `2` is
possible.

The three doubled magnetic sublevels are `m = -2, 0, 2`.  The pair
`(m, m') = (2, -2)` satisfies all conditions with `d = (2 - (-2)) / 2 = 2`:
`|2| ≤ 2` and `|-2| ≤ 2`, both `2` and `-2` are even as the parity condition with
`twoJ = 2` requires, and `2 * d = m - m' = 4`.  This provides the contrast with the
spin-half case: a spin-one target has enough helicity span to accommodate a
parton-gluon helicity flip of ±2 and remain in the allowed magnetic sublevels.

Reference: Hoodbhoy–Jaffe–Manohar, Nucl. Phys. B **312** (1989) 571, §3. -/
theorem gluonTransversityHelicityChange_in_helicityChanges_two
    : gluonTransversityHelicityChange ∈ helicityChanges 2 := by
  -- Exhibit m = 2, m' = -2.
  --   * |2| ≤ 2 and |-2| ≤ 2
  --   * (2 - 2) % 2 = 0 and (-2 - 2) % 2 = 0
  --   * 2 * 2 = 2 - (-2) = 4
  refine ⟨2, -2, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num

end EpsilonEridani.Particles.Parton.PDF
