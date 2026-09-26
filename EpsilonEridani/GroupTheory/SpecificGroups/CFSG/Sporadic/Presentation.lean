/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import EpsilonEridani.GroupTheory.SpecificGroups.CFSG.Index
public import EpsilonEridani.GroupTheory.SpecificGroups.CFSG.Sporadic.BabyMonster
public import EpsilonEridani.GroupTheory.SpecificGroups.CFSG.Sporadic.Conway.One
public import EpsilonEridani.GroupTheory.SpecificGroups.CFSG.Sporadic.Conway.Three
public import EpsilonEridani.GroupTheory.SpecificGroups.CFSG.Sporadic.Conway.Two
public import EpsilonEridani.GroupTheory.SpecificGroups.CFSG.Sporadic.Fischer.TwentyFour
public import EpsilonEridani.GroupTheory.SpecificGroups.CFSG.Sporadic.Fischer.TwentyThree
public import EpsilonEridani.GroupTheory.SpecificGroups.CFSG.Sporadic.Fischer.TwentyTwo
public import EpsilonEridani.GroupTheory.SpecificGroups.CFSG.Sporadic.HaradaNorton
public import EpsilonEridani.GroupTheory.SpecificGroups.CFSG.Sporadic.Held
public import EpsilonEridani.GroupTheory.SpecificGroups.CFSG.Sporadic.HigmanSims
public import EpsilonEridani.GroupTheory.SpecificGroups.CFSG.Sporadic.Janko.Four
public import EpsilonEridani.GroupTheory.SpecificGroups.CFSG.Sporadic.Janko.One
public import EpsilonEridani.GroupTheory.SpecificGroups.CFSG.Sporadic.Janko.Three
public import EpsilonEridani.GroupTheory.SpecificGroups.CFSG.Sporadic.Janko.Two
public import EpsilonEridani.GroupTheory.SpecificGroups.CFSG.Sporadic.Lyons
public import EpsilonEridani.GroupTheory.SpecificGroups.CFSG.Sporadic.Mathieu
public import EpsilonEridani.GroupTheory.SpecificGroups.CFSG.Sporadic.Mathieu.TwentyFour
public import EpsilonEridani.GroupTheory.SpecificGroups.CFSG.Sporadic.Mathieu.TwentyThree
public import EpsilonEridani.GroupTheory.SpecificGroups.CFSG.Sporadic.McLaughlin
public import EpsilonEridani.GroupTheory.SpecificGroups.CFSG.Sporadic.Monster
public import EpsilonEridani.GroupTheory.SpecificGroups.CFSG.Sporadic.ONan
public import EpsilonEridani.GroupTheory.SpecificGroups.CFSG.Sporadic.Rudvalis
public import EpsilonEridani.GroupTheory.SpecificGroups.CFSG.Sporadic.Suzuki
public import EpsilonEridani.GroupTheory.SpecificGroups.CFSG.Sporadic.Thompson

/-!
# Presentations of the sporadic groups

This file assembles the twenty-six independently transcribed sporadic-group presentations into the
total function `EpsilonEridani.SporadicName.presentation`. Each branch is the explicit, cited
`EpsilonEridani.GroupPresentation` defined in its group-specific module. The theorem
`EpsilonEridani.presentation_matchesMetadata` combines the individual generator- and
relator-count checks, while `EpsilonEridani.SporadicName.Group` is the concrete group defined by the
selected presentation.

This is milestone S1 of `EpsilonEridaniRoadmap/CFSGStatement/README.md`. The dispatcher and its interface
follow the target signatures in the human-authored roadmap's `CFSGStatement/Suggested.lean`; the
mathematical and bibliographic sources for each presentation are recorded in the corresponding
imported module.

## Main definitions

* `EpsilonEridani.SporadicName.presentation`: the complete presentation attached to a sporadic name.
* `EpsilonEridani.SporadicName.Group`: the group defined by that presentation.

## Main results

* `EpsilonEridani.presentation_matchesMetadata`: every selected presentation has the stated
  number of generators and relators.
-/

public section

namespace EpsilonEridani

/-- The explicit, cited finite presentation attached to each sporadic-group name. -/
@[simp]
def SporadicName.presentation : SporadicName → GroupPresentation
  | .M11 => Sporadic.m11Presentation
  | .M12 => Sporadic.m12Presentation
  | .M22 => Sporadic.m22Presentation
  | .M23 => Sporadic.m23Presentation
  | .M24 => Sporadic.m24Presentation
  | .J1 => Sporadic.j1Presentation
  | .J2 => Sporadic.j2Presentation
  | .J3 => Sporadic.j3Presentation
  | .J4 => Sporadic.j4Presentation
  | .HS => Sporadic.hsPresentation
  | .McL => Sporadic.mclPresentation
  | .He => Sporadic.hePresentation
  | .Ru => Sporadic.ruPresentation
  | .Suz => Sporadic.suzPresentation
  | .ONan => Sporadic.onanPresentation
  | .Co1 => Sporadic.co1Presentation
  | .Co2 => Sporadic.co2Presentation
  | .Co3 => Sporadic.co3Presentation
  | .Fi22 => Sporadic.fi22Presentation
  | .Fi23 => Sporadic.fi23Presentation
  | .Fi24Prime => Sporadic.fi24PrimePresentation
  | .HN => Sporadic.hnPresentation
  | .Ly => Sporadic.Lyons.presentation
  | .Th => Sporadic.Thompson.presentation
  | .B => Sporadic.BabyMonster.presentation
  | .M => Sporadic.Monster.presentation

/-- Every sporadic presentation has the generator and relator counts stated in its metadata.

This is deliberately not `@[simp]`: `GroupPresentation.matchesMetadata_iff` is itself a `simp`
lemma, so the left-hand side `s.presentation.matchesMetadata` simplifies to the pair of count
equations and is not in simp normal form, which the `simpNF` linter rejects. Apply the theorem
directly, or pass it to `simp` as an argument. -/
theorem presentation_matchesMetadata (s : SporadicName) :
    s.presentation.matchesMetadata := by
  cases s with
  | M11 => exact Sporadic.m11Presentation_matchesMetadata
  | M12 => exact Sporadic.m12Presentation_matchesMetadata
  | M22 => exact Sporadic.m22Presentation_matchesMetadata
  | M23 => exact Sporadic.m23Presentation_matchesMetadata
  | M24 => exact Sporadic.m24Presentation_matchesMetadata
  | J1 => exact Sporadic.j1Presentation_matchesMetadata
  | J2 => exact Sporadic.j2Presentation_matchesMetadata
  | J3 => exact Sporadic.j3Presentation_matchesMetadata
  | J4 => exact Sporadic.j4Presentation_matchesMetadata
  | HS => exact Sporadic.hsPresentation_matchesMetadata
  | McL => exact Sporadic.mclPresentation_matchesMetadata
  | He => exact Sporadic.hePresentation_matchesMetadata
  | Ru => exact Sporadic.ruPresentation_matchesMetadata
  | Suz => exact Sporadic.suzPresentation_matchesMetadata
  | ONan => exact Sporadic.onanPresentation_matchesMetadata
  | Co1 => exact Sporadic.co1Presentation_matchesMetadata
  | Co2 => exact Sporadic.co2Presentation_matchesMetadata
  | Co3 => exact Sporadic.co3Presentation_matchesMetadata
  | Fi22 => exact Sporadic.fi22Presentation_matchesMetadata
  | Fi23 => exact Sporadic.fi23Presentation_matchesMetadata
  | Fi24Prime => exact Sporadic.fi24PrimePresentation_matchesMetadata
  | HN => exact Sporadic.hnPresentation_matchesMetadata
  | Ly => exact Sporadic.Lyons.matchesMetadata_presentation
  | Th => exact Sporadic.Thompson.matchesMetadata_presentation
  | B => exact Sporadic.BabyMonster.matchesMetadata_presentation
  | M => exact Sporadic.Monster.presentation_matchesMetadata

/-- The sporadic group concretely defined by its selected finite presentation. -/
abbrev SporadicName.Group (s : SporadicName) : Type := s.presentation.Group

end EpsilonEridani
