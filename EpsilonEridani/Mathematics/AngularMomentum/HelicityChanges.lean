/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Set.Defs

/-!
# Helicity changes of a target of spin `J`

This module records, as the set `helicityChanges twoJ`, the helicity changes that a forward
matrix element can effect on a target of spin `J` (represented as `twoJ : ℕ`, so that
`J = twoJ / 2`), and proves the counting input to the absence of gluon transversity for a
spin-half target: `2 ∉ helicityChanges 1`, while `2 ∈ helicityChanges 2`.  A gluon
transversity density would be the matrix element of an operator changing the helicity of
the target by two units, which a spin-half state cannot accommodate but a spin-one state
can.

The claim proved here is purely combinatorial: it concerns which helicity changes can occur
in a forward matrix element, and it does not depend on the dynamics of the parton
distributions.

Reference: P. Hoodbhoy, R. L. Jaffe and A. Manohar, *Novel effects in deep inelastic
scattering from spin-one hadrons*, Nucl. Phys. B **312** (1989) 571, §3.
-/

@[expose] public section

namespace EpsilonEridani
namespace AngularMomentum

/-!
## Allowed helicity changes in a forward matrix element

For a target of spin `J` (represented as `twoJ : ℕ`, so that `J = twoJ / 2`), the magnetic
quantum numbers `m` and `m'` are encoded doubled, as integers: they satisfy `|m| ≤ twoJ` and
`|m'| ≤ twoJ` together with the parity conditions `m ≡ twoJ (mod 2)` and `m' ≡ twoJ (mod 2)`.
The set `helicityChanges twoJ` records the helicity changes `d = (m - m') / 2`, measured in
ordinary units, between two states of the target; this bounds the helicity change that any
operator can contribute to a forward matrix element `⟨m'| O |m⟩`, independently of the
operator.

A parton operator that flips the parton helicity by two units contributes `2` to the total
helicity change.  Hence a gluon transversity operator — which flips a gluon's helicity by
two units — can contribute to a forward matrix element only if `2 ∈ helicityChanges twoJ`.
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

/-- A helicity change `d` can occur in a forward matrix element on a target of spin
`J = twoJ / 2` exactly when its magnitude does not exceed the spin of the target. -/
@[simp] theorem mem_helicityChanges_iff {twoJ : ℕ} {d : ℤ} :
    d ∈ helicityChanges twoJ ↔ d.natAbs ≤ twoJ := by
  constructor
  · -- The magnitude of the difference is at most the sum of the magnitudes:
    -- `|2 * d| = |m - m'| ≤ 2 * twoJ`.
    rintro ⟨m, m', hm, hm', -, -, hd⟩
    omega
  · -- Realize `d` as the change from the extreme sublevel `m = twoJ` down to
    -- `m' = twoJ - 2 * d` (for `0 ≤ d`), or the mirror image; the second sublevel stays
    -- in range because `|d| ≤ twoJ`, and both carry the parity of `twoJ`.
    intro hd
    by_cases hd0 : 0 ≤ d
    · refine ⟨(twoJ : ℤ), (twoJ : ℤ) - 2 * d, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
    · refine ⟨(twoJ : ℤ) + 2 * d, (twoJ : ℤ), ?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-- The helicity changes available to a target of spin `J = twoJ / 2` form the closed
integer interval from `-twoJ` to `twoJ`. -/
theorem helicityChanges_eq_Icc (twoJ : ℕ) :
    helicityChanges twoJ = Set.Icc (-(twoJ : ℤ)) (twoJ : ℤ) := by
  ext d
  simp only [mem_helicityChanges_iff, Set.mem_Icc]
  omega

/-- A target of spin `J = twoJ / 2` accommodates a helicity change of `2` exactly when its
spin is at least `1`. -/
theorem two_mem_helicityChanges_iff {twoJ : ℕ} :
    (2 : ℤ) ∈ helicityChanges twoJ ↔ 2 ≤ twoJ := by
  simp only [mem_helicityChanges_iff]
  omega

/-! ### Spin-half: no gluon transversity -/

/-- For a spin-half target (`J = ½`, `twoJ = 1`), a helicity change of `2` is impossible.
The only available doubled magnetic sublevels are `m = 1` and `m = -1`, so the attainable
helicity changes are `-1`, `0` and `1`, and a change of `2` cannot occur.

This is the counting input to the absence of gluon transversity for a spin-half target: a
gluon transversity operator changes the gluon helicity by two units, and a two-state target
cannot accommodate that change. -/
theorem two_notMem_helicityChanges_one : (2 : ℤ) ∉ helicityChanges 1 := by
  simp only [two_mem_helicityChanges_iff]
  omega

/-! ### Spin-one: gluon transversity is allowed -/

/-- For a spin-one target (`J = 1`, `twoJ = 2`), a helicity change of `2` is possible: the
doubled magnetic sublevels span enough range to accommodate the helicity change of a gluon
transversity operator, in contrast with the spin-half case `two_notMem_helicityChanges_one`.

Reference: Hoodbhoy–Jaffe–Manohar, Nucl. Phys. B **312** (1989) 571, §3. -/
theorem two_mem_helicityChanges_two : (2 : ℤ) ∈ helicityChanges 2 := by
  simp only [two_mem_helicityChanges_iff]
  omega

end AngularMomentum
end EpsilonEridani
