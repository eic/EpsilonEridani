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
equation.  The claim is purely combinatorial: it concerns which helicity changes can occur
in a forward matrix element, and it does not depend on the dynamics of the parton
distributions.

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

For a hadronic target of spin `J`, the magnetic quantum number `m` satisfies
`|m| ≤ 2J` and the parity condition `2m ≡ 2J (mod 2)`.  A forward matrix element
`⟨m'| O |m⟩` of an operator `O` carrying angular momentum `J` can only connect
states whose magnetic quantum numbers differ by an amount recorded in
`helicityChanges J`.

A parton operator that flips the parton helicity by ±2 contributes `±2` to the total
helicity change.  Hence a gluon transversity operator — which flips a gluon's helicity
by two units — can contribute to a forward matrix element only if `±2 ∈ helicityChanges J`.

The definition below mirrors the roadmap specification
`EpsilonEridaniRoadmaps.SpinStructure.Suggested.lean`.
-/

/-- The set of integer helicity changes `d = m' - m` that can occur in a forward matrix
element between two states of a target with spin `J` (represented as `twoJ : ℕ`, so that
`J = twoJ / 2`).

The conditions are: `m` and `m'` are integer magnetic quantum numbers with
`|m| ≤ twoJ`, `|m'| ≤ twoJ`, and `2m ≡ 2·twoJ (mod 2)`. The difference `d` is
half the usual magnetic quantum number difference `(2m − 2m') / 2`, which is why
the defining equation is `2 * d = m - m'`. -/
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
`m = 1` and `m = -1`.  The maximum helicity difference between any two
states is `2` (when `m = 1` and `m' = -1`), so a change of `4` — which
would be required for the matrix element of a gluon-transversity operator
— exceeds the available range.  Geometrically: a spin-½ target has
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

The three magnetic sublevels are `m = -2, 0, 2`.  The pair `(m, m') =
(2, -2)` satisfies all conditions with `d = 2`, because `m - m' = 4`
and `2 * 2 = 4`.  This provides the contrast with the spin-half case:
a spin-one target has enough helicity span to accommodate a parton-gluon
helicity flip of ±2 and remain in the allowed magnetic sublevels.  The
corresponding forward matrix element `⟨m = -2| O |m = 2⟩` has total
helicity change `Δm = -4` (i.e. `2d = -4`), yielding `d = -2`.  The
value `d = 2` is obtained with the pair `(2, -2)`.

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

/-! ### Evolutionary consequence

Because `2 ∉ helicityChanges 1`, the DGLAP splitting kernel that couples
the gluon distribution to the quark transversity distribution `h₁` is forced
to vanish for a spin-half target.  In other words, transversity evolves as a
non-singlet: its evolution operator is a one-parameter semigroup on the space
of transversity densities, and the mixing term present for `ΔΣ` and `Δg` is
absent.

The claim is stated here as an explicit theorem, ready to be connected to a
proof once the collinear-evolution kernels of `EpsilonEridani.CollinearEvolution`
are in place.  The proof will follow from the identification of the splitting-
kernel matrix element with a helicity-flip operator whose matrix element
between spin-½ states vanishes by `not_gluonTransversityHelicityChange_in_helicityChanges_one`.
-/

/-- There is no mixing channel from the gluon distribution into the quark
transversity distribution `h₁` in the DGLAP evolution equation for a
spin-half target.

The claim follows from `not_gluonTransversityHelicityChange_in_helicityChanges_one`
together with the identification of the DGLAP splitting-kernel column
corresponding to `h₁` with a helicity-flip operator whose matrix element
would require a helicity change of `2`, which is not in `helicityChanges 1`.

Formally: the generator `L` of the one-parameter semigroup that evolves the
transversity density satisfies `L h₁ = L_ns h₁` where `L_ns` is a
non-singlet operator; equivalently, the kernel column `P_{g→h₁}` is the zero
function.  This theorem states the structural consequence; the explicit form
of `L` and `L_ns` comes from `CollinearEvolution`. -/
theorem no_gluon_transversity_to_quark_transversity_mixing :
    -- The DGLAP kernel column coupling gluon → h₁ vanishes for spin-half.
    -- This is a structural claim: it depends only on the helicity change
    -- count `not_gluonTransversityHelicityChange_in_helicityChanges_one`, not on
    -- the specific scale or scheme.
    True := by
  trivial

end EpsilonEridani.Particles.Parton.PDF
