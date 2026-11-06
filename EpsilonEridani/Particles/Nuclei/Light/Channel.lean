/-
Copyright (c) 2026 The EpsilonEridani contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The EpsilonEridani contributors
-/
module

public import Mathlib.Algebra.Ring.Int.Units
public import Mathlib.Algebra.Ring.Parity

/-!
# Two-nucleon partial-wave channels and the deuteron channels

The relative motion of two spin-`1/2` particles is decomposed into partial-wave channels. A channel
is labelled by the total spin `S` of the pair, the orbital angular momentum `L` of the relative
motion, and the total angular momentum `J` to which they couple, subject to the triangle condition
`|L - S| ≤ J ≤ L + S`. The label is `ChannelLabel`; the spectroscopic name `²ˢ⁺¹L_J` (for example
`³S₁` or `³D₁`) appears only in docstrings, so that no channel is identified by a string. For two
spin-`1/2` particles `S ∈ {0, 1}`; the general label does not impose this, and the theorems that
need it take `S ≤ 1` as a hypothesis. Likewise the isospin of two nucleons is `0` or `1`; the
definitions take an arbitrary isospin `T`, and the theorems that need the restriction take
`T ≤ 1` as a hypothesis.

The parity of a channel is the orbital factor `(-1)^L` (`ChannelLabel.parity`): the intrinsic
parities of two nucleons are equal and cancel.

Two nucleons are identical fermions once isospin is included, so a two-nucleon state is
antisymmetric under the exchange of the two nucleons. In a channel of isospin `T`, the exchange acts
on the three factors of the state separately: by `(-1)^L` on the orbital factor (the relative
position changes sign), and by `(-1)^(S + 1)` on the spin factor and by `(-1)^(T + 1)` on the
isospin factor (two spin-`1/2` objects coupled to `1` are symmetric and coupled to `0` are
antisymmetric). These three eigenvalues are the definition of `ChannelLabel.exchangeSign`; their
derivation from the coupled states is not part of this module. The generalised Pauli principle,
`ChannelLabel.PauliAllowed`, demands that the exchange sign be `-1`; it holds exactly when
`L + S + T` is odd (`ChannelLabel.pauliAllowed_iff_odd`).

The deuteron has total angular momentum `1`, positive parity and isospin `0`. These quantum numbers
alone, with no input from the nucleon-nucleon interaction, admit exactly the two channels `³S₁`
and `³D₁` (`ChannelLabel.eq_tripletS1_or_eq_tripletD1_iff`), so a deuteron wave function consists
of the two radial amplitudes of these channels; the spin-singlet channel with `J = 1` is `¹P₁`, of
negative parity. No two-nucleon channel at all has total angular momentum `1`, positive parity and
isospin `1` (`ChannelLabel.not_pauliAllowed_isospin_one_of_J_eq_one_of_parity_eq_one`): there is
no isospin-one two-nucleon state, and so no proton-proton or neutron-neutron state, with the
deuteron's spin and parity.

More generally, two Pauli-allowed channels with the same total angular momentum, parity and isospin
coincide unless they are the spin-triplet pair `³(J-1)_J` and `³(J+1)_J`
(`ChannelLabel.eq_or_S_eq_one_and_L_add_two`). An interaction that conserves total angular
momentum, parity and isospin, but not orbital angular momentum, therefore couples channels only
in such pairs; the tensor force is the standard example, and the deuteron's `³S₁`-`³D₁` mixing is
its case `J = 1`.

Finally, the spin-triplet channels of even orbital angular momentum, among them the deuteron
channels, are Pauli-allowed exactly in isospin `0`
(`ChannelLabel.pauliAllowed_iff_isospin_eq_zero`). A proton-proton or neutron-neutron pair has
isospin projection `±1`, hence isospin `1`, so these channels are available to a proton-neutron
pair and forbidden to a like-species pair.

## Main definitions

* `ChannelLabel`: total spin, orbital angular momentum and total angular momentum of a two-body
  channel, subject to the triangle condition.
* `ChannelLabel.parity`: the parity `(-1)^L` of a channel.
* `ChannelLabel.exchangeSign`: the eigenvalue of nucleon exchange in a channel of given isospin.
* `ChannelLabel.PauliAllowed`: the generalised Pauli principle, exchange sign `-1`.
* `ChannelLabel.tripletS1`, `ChannelLabel.tripletD1`: the deuteron channels `³S₁` and `³D₁`.

## Main results

* `ChannelLabel.pauliAllowed_iff_odd`: a channel of isospin `T` is Pauli-allowed exactly when
  `L + S + T` is odd.
* `ChannelLabel.eq_tripletS1_or_eq_tripletD1_iff`: the two-nucleon channels with `J = 1`, positive
  parity and isospin `0` allowed by the Pauli principle are exactly `³S₁` and `³D₁`.
* `ChannelLabel.not_pauliAllowed_isospin_one_of_J_eq_one_of_parity_eq_one`: no allowed
  two-nucleon channel has `J = 1`, positive parity and isospin `1`.
* `ChannelLabel.eq_or_S_eq_one_and_L_add_two`: allowed two-nucleon channels sharing `J`, parity
  and isospin are equal or form the pair `³(J-1)_J`, `³(J+1)_J`; conversely, channels of equal
  spin whose orbital angular momenta differ by two share parity
  (`ChannelLabel.parity_eq_of_L_add_two`) and Pauli status
  (`ChannelLabel.pauliAllowed_iff_of_L_add_two`).
* `ChannelLabel.pauliAllowed_iff_isospin_eq_zero`: a spin-triplet channel of even orbital angular
  momentum is allowed exactly in isospin `0`; the hypothesis `T ≤ 1` restricts the isospin to
  the two-nucleon range.

## References

* J. M. Blatt and V. F. Weisskopf, *Theoretical Nuclear Physics*, Wiley 1952: the two-nucleon
  states, the exclusion principle and the tensor force.
* K. S. Krane, *Introductory Nuclear Physics*, Wiley 1988, Chapter 4 (the deuteron and the force
  between nucleons).
-/

public section

namespace EpsilonEridani.Particles.Nuclei

/-- A two-body partial-wave channel: the total spin `S`, the orbital angular momentum `L` of the
relative motion, and the total angular momentum `J` to which they couple, subject to the triangle
condition `|L - S| ≤ J ≤ L + S`. Its spectroscopic name is `²ˢ⁺¹L_J`. -/
@[ext]
structure ChannelLabel where
  /-- The total spin of the pair. -/
  S : ℕ
  /-- The orbital angular momentum of the relative motion. -/
  L : ℕ
  /-- The total angular momentum. -/
  J : ℕ
  /-- The triangle condition `|L - S| ≤ J ≤ L + S`. -/
  triangle : J ≤ L + S ∧ L ≤ J + S ∧ S ≤ J + L

-- The derived decision procedure is exposed because `deriving instance` generates a private
-- `.decEq` auxiliary that is not exported without `@[expose]`; with the expose, `decide` compares
-- concrete channels in importing modules. The hand-written `Decidable (PauliAllowed)` instance
-- below needs no `@[expose]`: its body is exported without it, and `decide` reduces on
-- `PauliAllowed` in importing modules as it is.
@[expose] section

deriving instance DecidableEq for ChannelLabel

end

namespace ChannelLabel

variable (c : ChannelLabel) (T : ℕ)

theorem J_le_L_add_S : c.J ≤ c.L + c.S := c.triangle.1

theorem L_le_J_add_S : c.L ≤ c.J + c.S := c.triangle.2.1

theorem S_le_J_add_L : c.S ≤ c.J + c.L := c.triangle.2.2

/-- A spin-singlet channel has `L = J`. -/
theorem L_eq_J_of_S_eq_zero {c : ChannelLabel} (h : c.S = 0) : c.L = c.J := by
  have := c.J_le_L_add_S
  have := c.L_le_J_add_S
  omega

/-! ### Parity -/

/-- The parity of a two-nucleon channel, `(-1)^L`. The intrinsic parities of the two nucleons are
equal, so only the orbital factor remains. -/
def parity : ℤˣ := (-1) ^ c.L

theorem parity_def : c.parity = (-1) ^ c.L := (rfl)

@[simp] theorem parity_eq_one_iff : c.parity = 1 ↔ Even c.L :=
  neg_one_pow_eq_one_iff_even (by decide)

@[simp] theorem parity_eq_neg_one_iff : c.parity = -1 ↔ Odd c.L :=
  neg_one_pow_eq_neg_one_iff_odd (by decide)

/-! ### The generalised Pauli principle -/

/-- The eigenvalue of the exchange of the two nucleons on a state in the channel `c` with isospin
`T`: the product of `(-1)^L` on the orbital factor, `(-1)^(S + 1)` on the spin factor and
`(-1)^(T + 1)` on the isospin factor. -/
def exchangeSign : ℤˣ := (-1) ^ c.L * (-1) ^ (c.S + 1) * (-1) ^ (T + 1)

theorem exchangeSign_def :
    c.exchangeSign T = (-1) ^ c.L * (-1) ^ (c.S + 1) * (-1) ^ (T + 1) := (rfl)

/-- The exchange sign depends on `L + S + T` only: it is `(-1)^(L + S + T)`. -/
theorem exchangeSign_eq_neg_one_pow : c.exchangeSign T = (-1) ^ (c.L + c.S + T) := by
  rw [exchangeSign_def, ← pow_add, ← pow_add,
    show c.L + (c.S + 1) + (T + 1) = c.L + c.S + T + 2 by omega, pow_add]
  simp

/-- The generalised Pauli principle for a two-nucleon channel `c` of isospin `T`: a state of two
nucleons is antisymmetric under their exchange, so the exchange sign is `-1`. -/
def PauliAllowed : Prop := c.exchangeSign T = -1

theorem pauliAllowed_def : c.PauliAllowed T ↔ c.exchangeSign T = -1 := Iff.rfl

/-- A two-nucleon channel of isospin `T` is allowed by the Pauli principle exactly when
`L + S + T` is odd. -/
@[simp] theorem pauliAllowed_iff_odd : c.PauliAllowed T ↔ Odd (c.L + c.S + T) := by
  rw [pauliAllowed_def, exchangeSign_eq_neg_one_pow]
  exact neg_one_pow_eq_neg_one_iff_odd (by decide)

/-- The Pauli principle is decided by the parity of `L + S + T`. -/
instance : Decidable (c.PauliAllowed T) := decidable_of_iff' _ (c.pauliAllowed_iff_odd T)

/-! ### The deuteron channels -/

/-- The channel `³S₁`: total spin one, orbital angular momentum zero, total angular momentum one.
It is the dominant channel of the deuteron. -/
def tripletS1 : ChannelLabel := ⟨1, 0, 1, by omega⟩

/-- The channel `³D₁`: total spin one, orbital angular momentum two, total angular momentum one.
It is the channel admixed into the deuteron by the tensor force. -/
def tripletD1 : ChannelLabel := ⟨1, 2, 1, by omega⟩

@[simp] theorem tripletS1_S : tripletS1.S = 1 := (rfl)
@[simp] theorem tripletS1_L : tripletS1.L = 0 := (rfl)
@[simp] theorem tripletS1_J : tripletS1.J = 1 := (rfl)
@[simp] theorem tripletD1_S : tripletD1.S = 1 := (rfl)
@[simp] theorem tripletD1_L : tripletD1.L = 2 := (rfl)
@[simp] theorem tripletD1_J : tripletD1.J = 1 := (rfl)

/-- The two-nucleon channels with total angular momentum `1`, positive parity and isospin `0` that
the Pauli principle allows are exactly `³S₁` and `³D₁`. These are the deuteron's quantum numbers,
so a deuteron wave function lives in these two channels; the derivation uses no property of the
nucleon-nucleon interaction. -/
theorem eq_tripletS1_or_eq_tripletD1_iff {c : ChannelLabel} (hS : c.S ≤ 1) :
    c = tripletS1 ∨ c = tripletD1 ↔ c.J = 1 ∧ c.parity = 1 ∧ c.PauliAllowed 0 := by
  rw [parity_eq_one_iff, pauliAllowed_iff_odd, Nat.even_iff, Nat.odd_iff, ChannelLabel.ext_iff,
    ChannelLabel.ext_iff, tripletS1_S, tripletS1_L, tripletS1_J, tripletD1_S, tripletD1_L,
    tripletD1_J]
  have := c.triangle
  omega

/-- No two-nucleon channel with total angular momentum `1` and positive parity is allowed by the
Pauli principle in isospin `1`: the spin triplets of even `L` are forbidden, and the spin singlet
with `J = 1` is `¹P₁`, of negative parity. -/
theorem not_pauliAllowed_isospin_one_of_J_eq_one_of_parity_eq_one {c : ChannelLabel} (hS : c.S ≤ 1)
    (hJ : c.J = 1) (hP : c.parity = 1) : ¬ c.PauliAllowed 1 := by
  rw [parity_eq_one_iff, Nat.even_iff] at hP
  rw [pauliAllowed_iff_odd, Nat.odd_iff]
  have := c.triangle
  omega

/-! ### Channels with the same conserved quantum numbers -/

/-- Two Pauli-allowed two-nucleon channels with the same total angular momentum, parity and isospin
are either equal or the spin-triplet pair `³(J-1)_J`, `³(J+1)_J`. An interaction conserving these
quantum numbers can therefore mix channels only in such pairs, as the tensor force mixes `³S₁` and
`³D₁` in the deuteron. -/
theorem eq_or_S_eq_one_and_L_add_two {c c' : ChannelLabel} {T : ℕ} (hS : c.S ≤ 1) (hS' : c'.S ≤ 1)
    (hJ : c.J = c'.J) (hP : c.parity = c'.parity) (h : c.PauliAllowed T)
    (h' : c'.PauliAllowed T) :
    c = c' ∨ c.S = 1 ∧ c'.S = 1 ∧ (c.L + 2 = c'.L ∨ c'.L + 2 = c.L) := by
  have hP' : Even c.L ↔ Even c'.L := by rw [← parity_eq_one_iff, ← parity_eq_one_iff, hP]
  rw [Nat.even_iff, Nat.even_iff] at hP'
  rw [pauliAllowed_iff_odd, Nat.odd_iff] at h h'
  have h₁ := c.J_le_L_add_S
  have h₂ := c.L_le_J_add_S
  have h₃ := c'.J_le_L_add_S
  have h₄ := c'.L_le_J_add_S
  rw [ChannelLabel.ext_iff]
  -- equal parity and equal Pauli status force equal total spin, and then `|L - J|, |L' - J| ≤ S`
  -- with `S ≤ 1` leave `L = L'` or `|L - L'| = 2`
  omega

/-- Two channels whose orbital angular momenta differ by two have the same parity. -/
theorem parity_eq_of_L_add_two {c c' : ChannelLabel} (hL : c.L + 2 = c'.L) :
    c.parity = c'.parity := by
  rw [parity_def, parity_def, ← hL, pow_add]
  simp

/-- Two channels with the same total spin whose orbital angular momenta differ by two have the
same Pauli status in every isospin. -/
theorem pauliAllowed_iff_of_L_add_two {c c' : ChannelLabel} (hS : c.S = c'.S)
    (hL : c.L + 2 = c'.L) : c.PauliAllowed T ↔ c'.PauliAllowed T := by
  rw [pauliAllowed_iff_odd, pauliAllowed_iff_odd, ← hS, ← hL, Nat.odd_iff, Nat.odd_iff]
  omega

/-! ### Availability of the spin-triplet channels by isospin -/

/-- A spin-triplet channel of even orbital angular momentum, such as `³S₁` or `³D₁`, is allowed by
the Pauli principle exactly in isospin `0`. The isospin of two nucleons is `0` or `1`, and the
hypothesis `T ≤ 1` restricts to this range; without it the statement fails, since `T = 2` makes
`L + S + T` odd. Since a proton-proton or neutron-neutron pair has isospin `1`, these channels
are available to a proton-neutron pair only. -/
theorem pauliAllowed_iff_isospin_eq_zero {c : ChannelLabel} {T : ℕ} (hS : c.S = 1)
    (hL : Even c.L) (hT : T ≤ 1) : c.PauliAllowed T ↔ T = 0 := by
  rw [pauliAllowed_iff_odd, hS, Nat.odd_iff]
  rw [Nat.even_iff] at hL
  constructor <;> intro <;> omega

end ChannelLabel

end EpsilonEridani.Particles.Nuclei
