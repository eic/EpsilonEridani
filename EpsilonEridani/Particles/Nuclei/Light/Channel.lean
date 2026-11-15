/-
Copyright (c) 2026 The EpsilonEridani contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The EpsilonEridani contributors
-/
module

public import Mathlib.Algebra.Ring.Parity
public import EpsilonEridani.QuantumMechanics.AngularMomentum.SelectionRulesExtensions

/-!
# Two-nucleon partial-wave channels and the deuteron channels

The relative motion of two spin-`1/2` particles is decomposed into partial-wave channels. A channel
is labelled by the total spin `S` of the pair, the orbital angular momentum `L` of the relative
motion, and the total angular momentum `J` to which they couple, subject to the triangle condition
`|L - S| ≤ J ≤ L + S`, stated as Physlib's angular-momentum triangle rule
`PhyslibAlpha.Sl2.TriangleRule` in doubled units: `J` occurs in the Clebsch–Gordan decomposition of
the coupling of `S` and `L` (`PhyslibAlpha.Sl2.exists_eq_iff_triangleRule`). For two spin-`1/2`
particles `S ∈ {0, 1}`, and the label carries `S ≤ 1` as a field. The label is `ChannelLabel`; the
spectroscopic name `²ˢ⁺¹L_J` (for example `³S₁` or `³D₁`) appears only in docstrings, so that no
channel is identified by a string. The isospin of two nucleons is `0` or `1`; the definitions take
an arbitrary isospin `T`, and the theorems that need the restriction take `T ≤ 1` as a hypothesis.

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

The deuteron has total angular momentum `1`, positive parity and isospin `0`. Total angular
momentum `1` and positive parity alone, with no input from the nucleon-nucleon interaction, admit
exactly the two channels `³S₁` and `³D₁` (`ChannelLabel.eq_tripletS1_or_eq_tripletD1_iff`), so a
deuteron wave function consists of the two radial amplitudes of these channels; the spin-singlet
channel with `J = 1` is `¹P₁`, of negative parity. Such a channel is allowed by the Pauli principle
exactly in isospin `0`
(`ChannelLabel.pauliAllowed_iff_isospin_eq_zero_of_J_eq_one_of_parity_eq_one`): there is no
isospin-one two-nucleon state, and so no proton-proton or neutron-neutron state, with the
deuteron's spin and parity.

More generally, two Pauli-allowed channels with the same total angular momentum, parity and isospin
coincide unless they are the spin-triplet pair `³(J-1)_J` and `³(J+1)_J`
(`ChannelLabel.eq_or_S_eq_one_and_L_add_one_eq_J_of_pauliAllowed`); without the Pauli principle
the same holds for channels of equal total spin (`ChannelLabel.eq_or_S_eq_one_and_L_add_one_eq_J`).
An interaction that conserves total angular momentum, parity and isospin, but not orbital angular
momentum, therefore couples channels only in such pairs; the tensor force is the standard example,
and the deuteron's `³S₁`-`³D₁` mixing is its case `J = 1`.

The isospin-zero statement is a case of a general one: a channel with `L + S` odd, such as a spin
triplet of even orbital angular momentum or a spin singlet of odd orbital angular momentum, is
Pauli-allowed exactly in isospin `0` (`ChannelLabel.pauliAllowed_iff_isospin_eq_zero`). A
proton-proton or neutron-neutron pair has isospin projection `±1`, hence isospin `1`, so these
channels are available to a proton-neutron pair and forbidden to a like-species pair.

## Main definitions

* `ChannelLabel`: total spin, orbital angular momentum and total angular momentum of a two-nucleon
  channel, subject to `S ≤ 1` and the triangle condition.
* `ChannelLabel.parity`: the parity `(-1)^L` of a channel.
* `ChannelLabel.exchangeSign`: the eigenvalue of nucleon exchange in a channel of given isospin.
* `ChannelLabel.PauliAllowed`: the generalised Pauli principle, exchange sign `-1`.
* `ChannelLabel.tripletS1`, `ChannelLabel.tripletD1`: the deuteron channels `³S₁` and `³D₁`.

## Main results

* `ChannelLabel.exchangeSign_eq_neg_one_pow`: the exchange sign is `(-1)^(L + S + T)`.
* `ChannelLabel.pauliAllowed_iff_odd`: a channel of isospin `T` is Pauli-allowed exactly when
  `L + S + T` is odd.
* `ChannelLabel.pauliAllowed_iff_isospin_eq_zero`: a channel with `L + S` odd is allowed exactly
  in isospin `0`; the hypothesis `T ≤ 1` restricts the isospin to the two-nucleon range.
* `ChannelLabel.S_eq_of_parity_eq_of_pauliAllowed`: two channels allowed in the same isospin and of
  equal parity have equal total spin.
* `ChannelLabel.eq_tripletS1_or_eq_tripletD1_iff`: the two-nucleon channels with `J = 1` and
  positive parity are exactly `³S₁` and `³D₁`.
* `ChannelLabel.pauliAllowed_iff_isospin_eq_zero_of_odd_J_of_parity_eq_one`: a two-nucleon channel
  of odd `J` and positive parity is allowed exactly in isospin `0`; its case `J = 1` is
  `ChannelLabel.pauliAllowed_iff_isospin_eq_zero_of_J_eq_one_of_parity_eq_one`.
* `ChannelLabel.eq_or_S_eq_one_and_L_add_one_eq_J_of_pauliAllowed`: allowed two-nucleon channels
  sharing `J`, parity and isospin are equal or form the pair `³(J-1)_J`, `³(J+1)_J`; conversely,
  such a pair has equal parity (`ChannelLabel.parity_eq_iff`).

## References

* J. M. Blatt and V. F. Weisskopf, *Theoretical Nuclear Physics*, Wiley 1952: the two-nucleon
  states, the exclusion principle and the tensor force.
* K. S. Krane, *Introductory Nuclear Physics*, Wiley 1988, Chapter 4 (the deuteron and the force
  between nucleons).
-/

public section

namespace EpsilonEridani.Particles.Nuclei

/-- A two-nucleon partial-wave channel: the total spin `S ≤ 1` of the two spin-`1/2` nucleons,
the orbital angular momentum `L` of the relative motion, and the total angular momentum `J` to
which they couple, subject to the triangle condition `|L - S| ≤ J ≤ L + S`. Its spectroscopic name
is `²ˢ⁺¹L_J`. -/
@[ext]
structure ChannelLabel where
  /-- The total spin of the pair. -/
  S : ℕ
  /-- The orbital angular momentum of the relative motion. -/
  L : ℕ
  /-- The total angular momentum. -/
  J : ℕ
  /-- The total spin of two spin-`1/2` particles is `0` or `1`. -/
  S_le_one : S ≤ 1
  /-- The triangle condition `|L - S| ≤ J ≤ L + S`, in the doubled units of the triangle rule: `J`
  occurs in the coupling of `S` and `L`. -/
  triangle : PhyslibAlpha.Sl2.TriangleRule (2 * S) (2 * L) (2 * J)

deriving instance DecidableEq for ChannelLabel

namespace ChannelLabel

variable (c : ChannelLabel) (T : ℕ)

theorem J_le_L_add_S : c.J ≤ c.L + c.S := by
  obtain ⟨hJ, -, -⟩ := PhyslibAlpha.Sl2.triangleRule_two_mul_iff.1 c.triangle
  omega

theorem L_le_J_add_S : c.L ≤ c.J + c.S := by
  obtain ⟨-, -, hL⟩ := PhyslibAlpha.Sl2.triangleRule_two_mul_iff.1 c.triangle
  omega

theorem S_le_J_add_L : c.S ≤ c.J + c.L := by
  obtain ⟨-, hS, -⟩ := PhyslibAlpha.Sl2.triangleRule_two_mul_iff.1 c.triangle
  omega

/-- The orbital angular momentum of a two-nucleon channel is `J` or, in a spin triplet, `J ∓ 1`. -/
theorem L_eq_J_or_S_eq_one : c.L = c.J ∨ c.S = 1 ∧ (c.L + 1 = c.J ∨ c.L = c.J + 1) := by
  have := c.S_le_one
  have := c.J_le_L_add_S
  have := c.L_le_J_add_S
  omega

/-- A spin-singlet channel has `L = J`. -/
theorem L_eq_J_of_S_eq_zero {c : ChannelLabel} (h : c.S = 0) : c.L = c.J :=
  c.L_eq_J_or_S_eq_one.resolve_right (by omega)

/-! ### Parity -/

/-- The parity of a two-nucleon channel, `(-1)^L`. The intrinsic parities of the two nucleons are
equal, so only the orbital factor remains. -/
def parity : ℤˣ := (-1) ^ c.L

theorem parity_def : c.parity = (-1) ^ c.L := (rfl)

@[simp] theorem parity_eq_one_iff : c.parity = 1 ↔ Even c.L :=
  neg_one_pow_eq_one_iff_even (by decide)

@[simp] theorem parity_eq_neg_one_iff : c.parity = -1 ↔ Odd c.L :=
  neg_one_pow_eq_neg_one_iff_odd (by decide)

/-- Two channels have the same parity exactly when their orbital angular momenta have the same
parity. -/
theorem parity_eq_iff {c c' : ChannelLabel} : c.parity = c'.parity ↔ (Even c.L ↔ Even c'.L) :=
  ⟨fun h => c.parity_eq_one_iff.symm.trans (by rw [h, parity_eq_one_iff]),
    fun h => by simpa only [parity_def] using neg_one_pow_congr (R := ℤˣ) h⟩

/-! ### The generalised Pauli principle -/

/-- The eigenvalue of the exchange of the two nucleons on a state in the channel `c` with isospin
`T`: the product of the channel's parity on the orbital factor, `(-1)^(S + 1)` on the spin factor
of the two spin-`1/2` nucleons and `(-1)^(T + 1)` on the isospin factor. -/
def exchangeSign : ℤˣ := c.parity * (-1) ^ (c.S + 1) * (-1) ^ (T + 1)

theorem exchangeSign_def :
    c.exchangeSign T = c.parity * (-1) ^ (c.S + 1) * (-1) ^ (T + 1) := (rfl)

/-- The exchange sign depends on `L + S + T` only: it is `(-1)^(L + S + T)`. -/
@[simp] theorem exchangeSign_eq_neg_one_pow : c.exchangeSign T = (-1) ^ (c.L + c.S + T) := by
  rw [exchangeSign_def, parity_def, ← pow_add, ← pow_add,
    show c.L + (c.S + 1) + (T + 1) = c.L + c.S + T + 2 by omega, pow_add]
  simp

/-- The generalised Pauli principle for a two-nucleon channel `c` of isospin `T`: a state of two
nucleons is antisymmetric under their exchange, so the exchange sign is `-1`. -/
def PauliAllowed : Prop := c.exchangeSign T = -1

theorem pauliAllowed_def : c.PauliAllowed T ↔ c.exchangeSign T = -1 := (Iff.rfl)

/-- A two-nucleon channel of isospin `T` is allowed by the Pauli principle exactly when
`L + S + T` is odd. -/
@[simp] theorem pauliAllowed_iff_odd : c.PauliAllowed T ↔ Odd (c.L + c.S + T) := by
  rw [pauliAllowed_def, exchangeSign_eq_neg_one_pow]
  exact neg_one_pow_eq_neg_one_iff_odd (by decide)

/-- The Pauli principle is decided by the parity of `L + S + T`. -/
instance : Decidable (c.PauliAllowed T) := decidable_of_iff' _ (c.pauliAllowed_iff_odd T)

/-- A channel with `L + S` odd, such as a spin triplet of even orbital angular momentum (`³S₁`,
`³D₁`) or a spin singlet of odd orbital angular momentum (`¹P₁`), is allowed by the Pauli principle
exactly in isospin `0`. The isospin of two nucleons is `0` or `1`, and the hypothesis `T ≤ 1`
restricts to this range; without it the statement fails, since `T = 2` makes `L + S + T` odd.
Since a proton-proton or neutron-neutron pair has isospin `1`, these channels are available to a
proton-neutron pair only. -/
theorem pauliAllowed_iff_isospin_eq_zero {c : ChannelLabel} {T : ℕ} (h : Odd (c.L + c.S))
    (hT : T ≤ 1) : c.PauliAllowed T ↔ T = 0 := by
  rw [pauliAllowed_iff_odd, Nat.odd_iff]
  rw [Nat.odd_iff] at h
  constructor <;> intro <;> omega

/-- Two channels of equal parity that are both allowed by the Pauli principle in the same isospin
have the same total spin: `L + S + T` and `L' + S' + T` are odd and `L ≡ L' (mod 2)`, so
`S ≡ S' (mod 2)`, and both spins are `0` or `1`. -/
theorem S_eq_of_parity_eq_of_pauliAllowed {c c' : ChannelLabel} {T : ℕ}
    (hP : c.parity = c'.parity) (h : c.PauliAllowed T) (h' : c'.PauliAllowed T) : c.S = c'.S := by
  have hL := parity_eq_iff.1 hP
  have := c.S_le_one
  have := c'.S_le_one
  simp only [pauliAllowed_iff_odd, Nat.odd_iff, Nat.even_iff] at h h' hL
  omega

/-! ### The deuteron channels -/

/-- The channel `³S₁`: total spin one, orbital angular momentum zero, total angular momentum one.
It is the dominant channel of the deuteron. -/
def tripletS1 : ChannelLabel := ⟨1, 0, 1, le_rfl, by decide⟩

/-- The channel `³D₁`: total spin one, orbital angular momentum two, total angular momentum one.
It is the channel admixed into the deuteron by the tensor force. -/
def tripletD1 : ChannelLabel := ⟨1, 2, 1, le_rfl, by decide⟩

@[simp] theorem tripletS1_S : tripletS1.S = 1 := (rfl)
@[simp] theorem tripletS1_L : tripletS1.L = 0 := (rfl)
@[simp] theorem tripletS1_J : tripletS1.J = 1 := (rfl)
@[simp] theorem tripletD1_S : tripletD1.S = 1 := (rfl)
@[simp] theorem tripletD1_L : tripletD1.L = 2 := (rfl)
@[simp] theorem tripletD1_J : tripletD1.J = 1 := (rfl)

/-- The two deuteron channels are distinct. -/
@[simp] theorem tripletS1_ne_tripletD1 : tripletS1 ≠ tripletD1 := by
  simp [ChannelLabel.ext_iff]

/-- The two-nucleon channels with total angular momentum `1` and positive parity are exactly `³S₁`
and `³D₁`; the spin singlet with `J = 1` is `¹P₁`, of negative parity. These are the deuteron's
spin and parity, so a deuteron wave function lives in these two channels; the derivation uses no
property of the nucleon-nucleon interaction. -/
theorem eq_tripletS1_or_eq_tripletD1_iff {c : ChannelLabel} :
    c = tripletS1 ∨ c = tripletD1 ↔ c.J = 1 ∧ c.parity = 1 := by
  simp only [parity_eq_one_iff, Nat.even_iff, ChannelLabel.ext_iff, tripletS1_S, tripletS1_L,
    tripletS1_J, tripletD1_S, tripletD1_L, tripletD1_J]
  have := c.L_eq_J_or_S_eq_one
  omega

/-- A two-nucleon channel of odd total angular momentum and positive parity is a spin triplet of
even orbital angular momentum `J ∓ 1`, so it is allowed by the Pauli principle exactly in isospin
`0`; the spin singlet of odd `J` has `L = J` odd, hence negative parity. -/
theorem pauliAllowed_iff_isospin_eq_zero_of_odd_J_of_parity_eq_one {c : ChannelLabel} {T : ℕ}
    (hJ : Odd c.J) (hP : c.parity = 1) (hT : T ≤ 1) :
    c.PauliAllowed T ↔ T = 0 := by
  refine pauliAllowed_iff_isospin_eq_zero ?_ hT
  have := c.L_eq_J_or_S_eq_one
  rw [parity_eq_one_iff, Nat.even_iff] at hP
  rw [Nat.odd_iff] at hJ ⊢
  omega

/-- A two-nucleon channel with total angular momentum `1` and positive parity is allowed by the
Pauli principle exactly in isospin `0`, the isospin of the deuteron; in isospin `1` the spin
triplets `³S₁` and `³D₁` are forbidden, and the spin singlet with `J = 1` is `¹P₁`, of negative
parity. -/
theorem pauliAllowed_iff_isospin_eq_zero_of_J_eq_one_of_parity_eq_one {c : ChannelLabel} {T : ℕ}
    (hJ : c.J = 1) (hP : c.parity = 1) (hT : T ≤ 1) :
    c.PauliAllowed T ↔ T = 0 :=
  pauliAllowed_iff_isospin_eq_zero_of_odd_J_of_parity_eq_one (hJ ▸ odd_one) hP hT

/-! ### Channels with the same conserved quantum numbers -/

/-- Two channels with the same total spin, total angular momentum and parity are either equal or the
spin-triplet pair `³(J-1)_J`, `³(J+1)_J`. -/
theorem eq_or_S_eq_one_and_L_add_one_eq_J {c c' : ChannelLabel}
    (hSS' : c.S = c'.S) (hJ : c.J = c'.J) (hP : c.parity = c'.parity) :
    c = c' ∨ c.S = 1 ∧ c'.S = 1 ∧
      (c.L + 1 = c.J ∧ c.J + 1 = c'.L ∨ c'.L + 1 = c.J ∧ c.J + 1 = c.L) := by
  have hP' := parity_eq_iff.1 hP
  have := c.L_eq_J_or_S_eq_one
  have := c'.L_eq_J_or_S_eq_one
  simp only [Nat.even_iff] at hP'
  rw [ChannelLabel.ext_iff]
  -- `L, L' ∈ {J - 1, J, J + 1}` with `J - 1` and `J + 1` only in a triplet, and `L ≡ L' (mod 2)`
  omega

/-- Two Pauli-allowed two-nucleon channels with the same total angular momentum, parity and isospin
are either equal or the spin-triplet pair `³(J-1)_J`, `³(J+1)_J`: equal parity and equal Pauli
status force equal total spin (`ChannelLabel.S_eq_of_parity_eq_of_pauliAllowed`). An interaction
conserving these quantum numbers can therefore mix channels only in such pairs, as the tensor force
mixes `³S₁` and `³D₁` in the deuteron. -/
theorem eq_or_S_eq_one_and_L_add_one_eq_J_of_pauliAllowed {c c' : ChannelLabel} {T : ℕ}
    (hJ : c.J = c'.J) (hP : c.parity = c'.parity) (h : c.PauliAllowed T)
    (h' : c'.PauliAllowed T) :
    c = c' ∨ c.S = 1 ∧ c'.S = 1 ∧
      (c.L + 1 = c.J ∧ c.J + 1 = c'.L ∨ c'.L + 1 = c.J ∧ c.J + 1 = c.L) :=
  eq_or_S_eq_one_and_L_add_one_eq_J (S_eq_of_parity_eq_of_pauliAllowed hP h h') hJ hP

end ChannelLabel

end EpsilonEridani.Particles.Nuclei
