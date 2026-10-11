/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Multiset
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Tactic.NormNum

/-!
# Collinear twist of light-cone operators

Fix light-like vectors `n`, `nbar` with `n·nbar = 1` and write `v^+ = n·v`, `v^- = nbar·v` for the
light-cone components of a vector (so `γ^+ = n·γ` and `γ^- = nbar·γ`), the remaining two components
being transverse. A boost along
the light-cone axis with rapidity `η` rescales `v^± ↦ e^{±η} v^±`. The quark field splits into its
good and bad projections `ψ_± = P_± ψ`, `P_± = ½ γ^∓ γ^±`, which rescale by `e^{±η/2}`; the
Dirac-conjugate quark field `ψbar_± = \overline{ψ_±}` rescales in the same way. The gluon field
strength `F^{μν}` splits into the components `F^{+i}`, `F^{+-}`, `F^{ij}` and `F^{-i}` (`i, j`
transverse), which rescale by `e^{η}`, `1`, `1` and `e^{-η}`. The exponent of `e^{η}` is the
*light-cone spin* `s` of the field component.

The *collinear twist* of a field component is `t = d - s`, its canonical mass dimension (`3/2`
for a quark field, `2` for the field strength) minus its light-cone spin. It is a positive integer:
the *good components* — the good quark fields and `F^{+i}` — have twist one, bad quark fields,
`F^{+-}` and `F^{ij}` have twist two, and `F^{-i}` has twist three. The twist of a light-cone
operator is computed from its field content, as its mass dimension minus its light-cone spin, both
of which are additive over the field insertions. The light-cone positions of the insertions and
the Dirac and colour structure contracting them do not enter the grading, so the field content is
recorded as a multiset of field components and nothing else. A Dirac structure selects which
projections appear: the scalar `ψbar ψ = ψbar_+ ψ_- + ψbar_- ψ_+` is a sum of two twist-three
monomials, while `ψbar γ^+ ψ` only involves `ψbar_+ γ^+ ψ_+` and has twist two.

Covariant-derivative insertions are not modelled. They do enter the grading: a derivative has
mass dimension `1`, so `D^+`, `D^i` and `D^-` would carry twist zero, one and two. The
classifications below are therefore classifications of derivative-free operator monomials only;
for instance the twist-three operator `ψbar_+ γ^+ D^i ψ_+` is not among them.

Twist is the grading by which forward nucleon matrix elements of light-cone operators are
organised: the twist-two operators give the leading-power parton densities, the twist-three
operators the two- and three-parton correlators behind `g_T`, `h_L`, `e` and the
Efremov-Teryaev-Qiu-Sterman function, and the twist-four operators the `1/Q²` power corrections
to the inclusive structure functions.

## Main definitions

* `LightConeField`: a quark, conjugate quark or gluon field-strength component on the light cone.
* `LightConeField.massDimension`, `LightConeField.lightConeSpin`, `LightConeField.twist`.
* `FieldContent`: the field content of a light-cone operator monomial.
* `FieldContent.twist`, with `FieldContent.massDimension`, `FieldContent.lightConeSpin` and the
  quark number `FieldContent.quarkNumber`.

## Main statements

* `LightConeField.twist_eq_massDimension_sub_lightConeSpin` and its operator version
  `FieldContent.twist_eq_massDimension_sub_lightConeSpin`: twist is dimension minus spin.
* `FieldContent.twist_add`: twist is additive under products of operators.
* `FieldContent.card_le_twist`: an operator has twist at least its number of fields, with
  equality exactly when every field is a good component (`FieldContent.twist_eq_card_iff`).
* `FieldContent.twist_eq_one_iff`: a derivative-free operator has twist one exactly when it is a
  single twist-one field.
* `FieldContent.twist_eq_two_iff`, `FieldContent.twist_eq_three_iff`: a derivative-free operator
  has twist two exactly when it is a single twist-two field or a bilinear in twist-one fields, and
  twist three exactly when it is a single twist-three field, a bilinear in a twist-one and a
  twist-two field, or a trilinear in twist-one fields.
* `FieldContent.twist_eq_two_iff_of_quarkNumber_eq_zero`: a derivative-free quark-number-neutral
  operator of twist two is a bilinear in good quark fields or in two `F^{+i}`, or a single `F^{+-}`
  or `F^{ij}`.
* `FieldContent.twist_eq_three_iff_of_quarkNumber_eq_zero`: a derivative-free quark-number-neutral
  operator of twist three is a bilinear with one twist-two field (a bad quark field, `F^{+-}` or
  `F^{ij}`), a trilinear in good quark fields and one `F^{+i}` or in three `F^{+i}`, or a single
  `F^{-i}`.

The single-field cases are colour octets and drop out of any gauge-invariant operator; they are
kept in the classifications because colour is not recorded in the field content.

## References

* R. L. Jaffe, *Spin, twist and hadron structure in deep inelastic processes*,
  arXiv:hep-ph/9602236.
* V. M. Braun, G. P. Korchemsky, D. Müller, *The uses of conformal symmetry in QCD*,
  Prog. Part. Nucl. Phys. 51 (2003) 311, arXiv:hep-ph/0306057.
-/

public section

namespace EpsilonEridani.Particles.Parton.HigherTwist

/-- The good and bad light-cone projections `ψ_± = P_± ψ`, `P_± = ½ γ^∓ γ^±`, of a quark field. -/
inductive QuarkProjection
  /-- The good projection `ψ_+`, of light-cone spin `+1/2`. -/
  | good
  /-- The bad projection `ψ_-`, of light-cone spin `-1/2`. -/
  | bad
  deriving DecidableEq

/-- The light-cone components of the gluon field strength `F^{μν}`, up to the transverse
indices. -/
inductive FieldStrengthComponent
  /-- The components `F^{+i}`, of light-cone spin `1`. -/
  | plusTransverse
  /-- The component `F^{+-}`, of light-cone spin `0`. -/
  | plusMinus
  /-- The purely transverse component `F^{ij}`, of light-cone spin `0`. -/
  | purelyTransverse
  /-- The components `F^{-i}`, of light-cone spin `-1`. -/
  | minusTransverse
  deriving DecidableEq

/-- A field insertion in a light-cone operator: a projection of the quark field `ψ` or of the
Dirac-conjugate quark field `ψbar`, or a light-cone component of the gluon field strength. -/
inductive LightConeField
  /-- A projection `ψ_±` of the quark field. -/
  | quark (p : QuarkProjection)
  /-- A projection `ψbar_±` of the Dirac-conjugate quark field. -/
  | quarkBar (p : QuarkProjection)
  /-- A light-cone component of the gluon field strength. -/
  | fieldStrength (c : FieldStrengthComponent)
  deriving DecidableEq

namespace LightConeField

/-- The canonical mass dimension of a field component in four dimensions: `3/2` for the quark
field and its Dirac conjugate and `2` for the gluon field strength. -/
def massDimension : LightConeField → ℚ
  | quark _ => 3 / 2
  | quarkBar _ => 3 / 2
  | fieldStrength _ => 2

/-- The light-cone spin of a field component: the exponent of `e^η` by which it rescales under a
boost of rapidity `η` along the light-cone axis. -/
def lightConeSpin : LightConeField → ℚ
  | quark .good | quarkBar .good => 1 / 2
  | quark .bad | quarkBar .bad => -1 / 2
  | fieldStrength .plusTransverse => 1
  | fieldStrength .plusMinus | fieldStrength .purelyTransverse => 0
  | fieldStrength .minusTransverse => -1

/-- The collinear twist of a field component, its mass dimension minus its light-cone spin
(`twist_eq_massDimension_sub_lightConeSpin`). -/
def twist : LightConeField → ℕ
  | quark .good | quarkBar .good => 1
  | quark .bad | quarkBar .bad => 2
  | fieldStrength .plusTransverse => 1
  | fieldStrength .plusMinus | fieldStrength .purelyTransverse => 2
  | fieldStrength .minusTransverse => 3

/-- The quark number of a field component: `1` for the quark field, `-1` for its Dirac conjugate
and `0` for the gluon field strength. -/
def quarkNumber : LightConeField → ℤ
  | quark _ => 1
  | quarkBar _ => -1
  | fieldStrength _ => 0

@[simp] theorem massDimension_quark (p : QuarkProjection) :
    (quark p).massDimension = 3 / 2 := (rfl)

@[simp] theorem massDimension_quarkBar (p : QuarkProjection) :
    (quarkBar p).massDimension = 3 / 2 := (rfl)

@[simp] theorem massDimension_fieldStrength (c : FieldStrengthComponent) :
    (fieldStrength c).massDimension = 2 := (rfl)

@[simp] theorem lightConeSpin_quark_good : (quark .good).lightConeSpin = 1 / 2 := (rfl)

@[simp] theorem lightConeSpin_quark_bad : (quark .bad).lightConeSpin = -1 / 2 := (rfl)

@[simp] theorem lightConeSpin_quarkBar_good : (quarkBar .good).lightConeSpin = 1 / 2 := (rfl)

@[simp] theorem lightConeSpin_quarkBar_bad : (quarkBar .bad).lightConeSpin = -1 / 2 := (rfl)

@[simp] theorem lightConeSpin_fieldStrength_plusTransverse :
    (fieldStrength .plusTransverse).lightConeSpin = 1 := (rfl)

@[simp] theorem lightConeSpin_fieldStrength_plusMinus :
    (fieldStrength .plusMinus).lightConeSpin = 0 := (rfl)

@[simp] theorem lightConeSpin_fieldStrength_purelyTransverse :
    (fieldStrength .purelyTransverse).lightConeSpin = 0 := (rfl)

@[simp] theorem lightConeSpin_fieldStrength_minusTransverse :
    (fieldStrength .minusTransverse).lightConeSpin = -1 := (rfl)

@[simp, grind =] theorem twist_quark_good : (quark .good).twist = 1 := (rfl)

@[simp, grind =] theorem twist_quark_bad : (quark .bad).twist = 2 := (rfl)

@[simp, grind =] theorem twist_quarkBar_good : (quarkBar .good).twist = 1 := (rfl)

@[simp, grind =] theorem twist_quarkBar_bad : (quarkBar .bad).twist = 2 := (rfl)

@[simp, grind =] theorem twist_fieldStrength_plusTransverse :
    (fieldStrength .plusTransverse).twist = 1 := (rfl)

@[simp, grind =] theorem twist_fieldStrength_plusMinus :
    (fieldStrength .plusMinus).twist = 2 := (rfl)

@[simp, grind =] theorem twist_fieldStrength_purelyTransverse :
    (fieldStrength .purelyTransverse).twist = 2 := (rfl)

@[simp, grind =] theorem twist_fieldStrength_minusTransverse :
    (fieldStrength .minusTransverse).twist = 3 := (rfl)

@[simp, grind =] theorem quarkNumber_quark (p : QuarkProjection) : (quark p).quarkNumber = 1 :=
  (rfl)

@[simp, grind =] theorem quarkNumber_quarkBar (p : QuarkProjection) :
    (quarkBar p).quarkNumber = -1 := (rfl)

@[simp, grind =] theorem quarkNumber_fieldStrength (c : FieldStrengthComponent) :
    (fieldStrength c).quarkNumber = 0 := (rfl)

/-- The twist of a field component is its mass dimension minus its light-cone spin. -/
theorem twist_eq_massDimension_sub_lightConeSpin (f : LightConeField) :
    (f.twist : ℚ) = f.massDimension - f.lightConeSpin := by
  rcases f with (_ | _) | (_ | _) | (_ | _ | _ | _) <;> norm_num

/-- Every field component has twist at least one. -/
@[simp, grind .] theorem one_le_twist (f : LightConeField) : 1 ≤ f.twist := by
  rcases f with (_ | _) | (_ | _) | (_ | _ | _ | _) <;> simp

/-- The field components of twist one are the good ones: `ψ_+`, `ψbar_+` and `F^{+i}`. -/
@[simp] theorem twist_eq_one_iff {f : LightConeField} :
    f.twist = 1 ↔ f = quark .good ∨ f = quarkBar .good ∨ f = fieldStrength .plusTransverse := by
  rcases f with (_ | _) | (_ | _) | (_ | _ | _ | _) <;> simp

/-- The field components of twist two: `ψ_-`, `ψbar_-`, `F^{+-}` and `F^{ij}`. -/
@[simp] theorem twist_eq_two_iff {f : LightConeField} :
    f.twist = 2 ↔ f = quark .bad ∨ f = quarkBar .bad ∨ f = fieldStrength .plusMinus ∨
      f = fieldStrength .purelyTransverse := by
  rcases f with (_ | _) | (_ | _) | (_ | _ | _ | _) <;> simp

/-- The field component of twist three: `F^{-i}`. -/
@[simp] theorem twist_eq_three_iff {f : LightConeField} :
    f.twist = 3 ↔ f = fieldStrength .minusTransverse := by
  rcases f with (_ | _) | (_ | _) | (_ | _ | _ | _) <;> simp

end LightConeField

open LightConeField

/-- The field content of a light-cone operator monomial: the multiset of its field insertions.
The product of two operators has the sum of their field contents. -/
abbrev FieldContent : Type := Multiset LightConeField

namespace FieldContent

/-- The mass dimension of an operator, the sum of the mass dimensions of its fields. -/
def massDimension (O : FieldContent) : ℚ := (O.map LightConeField.massDimension).sum

/-- The light-cone spin of an operator, the sum of the light-cone spins of its fields. -/
def lightConeSpin (O : FieldContent) : ℚ := (O.map LightConeField.lightConeSpin).sum

/-- The collinear twist of an operator, the sum of the twists of its fields; it equals the mass
dimension minus the light-cone spin (`twist_eq_massDimension_sub_lightConeSpin`). -/
def twist (O : FieldContent) : ℕ := (O.map LightConeField.twist).sum

/-- The quark number of an operator, the number of quark fields `ψ` minus the number of
conjugate quark fields `ψbar`. -/
def quarkNumber (O : FieldContent) : ℤ := (O.map LightConeField.quarkNumber).sum

theorem massDimension_def (O : FieldContent) :
    massDimension O = (O.map LightConeField.massDimension).sum := (rfl)

theorem lightConeSpin_def (O : FieldContent) :
    lightConeSpin O = (O.map LightConeField.lightConeSpin).sum := (rfl)

theorem twist_def (O : FieldContent) : twist O = (O.map LightConeField.twist).sum := (rfl)

theorem quarkNumber_def (O : FieldContent) :
    quarkNumber O = (O.map LightConeField.quarkNumber).sum := (rfl)

@[simp] theorem massDimension_zero : massDimension 0 = 0 := (rfl)

@[simp] theorem lightConeSpin_zero : lightConeSpin 0 = 0 := (rfl)

@[simp, grind =] theorem twist_zero : twist 0 = 0 := (rfl)

@[simp, grind =] theorem quarkNumber_zero : quarkNumber 0 = 0 := (rfl)

@[simp] theorem massDimension_cons (f : LightConeField) (O : FieldContent) :
    massDimension (f ::ₘ O) = f.massDimension + massDimension O := by
  simp [massDimension_def]

@[simp] theorem lightConeSpin_cons (f : LightConeField) (O : FieldContent) :
    lightConeSpin (f ::ₘ O) = f.lightConeSpin + lightConeSpin O := by
  simp [lightConeSpin_def]

-- `grind` matches patterns in its own rule set, in which the definitional unfolding of the
-- `insert` of the `{f, g}` multiset notation into `cons` is not available. Registering it lets the
-- `@[grind =]` lemmas below evaluate the twist and quark number of a concrete field content
-- written in that notation.
attribute [grind =] Multiset.insert_eq_cons

@[simp, grind =] theorem twist_cons (f : LightConeField) (O : FieldContent) :
    twist (f ::ₘ O) = f.twist + twist O := by
  simp [twist_def]

@[simp, grind =] theorem quarkNumber_cons (f : LightConeField) (O : FieldContent) :
    quarkNumber (f ::ₘ O) = f.quarkNumber + quarkNumber O := by
  simp [quarkNumber_def]

@[simp] theorem massDimension_singleton (f : LightConeField) :
    massDimension {f} = f.massDimension := by
  simp [massDimension_def]

@[simp] theorem lightConeSpin_singleton (f : LightConeField) :
    lightConeSpin {f} = f.lightConeSpin := by
  simp [lightConeSpin_def]

@[simp, grind =] theorem twist_singleton (f : LightConeField) : twist {f} = f.twist := by
  simp [twist_def]

@[simp, grind =] theorem quarkNumber_singleton (f : LightConeField) :
    quarkNumber {f} = f.quarkNumber := by
  simp [quarkNumber_def]

/-- The mass dimension is additive under products of operators. -/
@[simp] theorem massDimension_add (O O' : FieldContent) :
    massDimension (O + O') = massDimension O + massDimension O' := by
  simp [massDimension_def]

/-- The light-cone spin is additive under products of operators. -/
@[simp] theorem lightConeSpin_add (O O' : FieldContent) :
    lightConeSpin (O + O') = lightConeSpin O + lightConeSpin O' := by
  simp [lightConeSpin_def]

/-- Twist is additive under products of operators. -/
@[simp, grind =] theorem twist_add (O O' : FieldContent) : twist (O + O') = twist O + twist O' := by
  simp [twist_def]

/-- The quark number is additive under products of operators. -/
@[simp, grind =] theorem quarkNumber_add (O O' : FieldContent) :
    quarkNumber (O + O') = quarkNumber O + quarkNumber O' := by
  simp [quarkNumber_def]

/-- The twist of an operator is its mass dimension minus its light-cone spin. -/
theorem twist_eq_massDimension_sub_lightConeSpin (O : FieldContent) :
    (twist O : ℚ) = massDimension O - lightConeSpin O := by
  induction O using Multiset.induction_on with
  | empty => simp
  | cons f O ih =>
    simp only [twist_cons, massDimension_cons, lightConeSpin_cons, Nat.cast_add, ih,
      f.twist_eq_massDimension_sub_lightConeSpin, add_sub_add_comm]

/-- An operator has twist at least its number of fields. -/
@[grind .] theorem card_le_twist (O : FieldContent) : Multiset.card O ≤ twist O := by
  simpa [twist_def] using Multiset.card_nsmul_le_sum (a := 1) (s := O.map LightConeField.twist)
    (by simp)

/-- Each field of an operator has twist at most the twist of the operator. -/
theorem le_twist_of_mem {f : LightConeField} {O : FieldContent} (h : f ∈ O) :
    f.twist ≤ twist O :=
  twist_def O ▸ Multiset.le_sum_of_mem (Multiset.mem_map_of_mem _ h)

/-- Twist is monotone under inclusion of field content. -/
theorem twist_mono : Monotone twist := by
  intro O O' h
  obtain ⟨O'', rfl⟩ := exists_add_of_le h
  simp

/-- Only the empty field content, the identity operator, has twist zero. -/
@[simp] theorem twist_eq_zero_iff {O : FieldContent} : twist O = 0 ↔ O = 0 := by
  refine ⟨fun h ↦ ?_, by rintro rfl; rfl⟩
  have := card_le_twist O
  exact Multiset.card_eq_zero.1 (by omega)

/-- An operator has twist equal to its number of fields exactly when all its fields are good
components. -/
@[simp] theorem twist_eq_card_iff {O : FieldContent} :
    twist O = Multiset.card O ↔ ∀ f ∈ O, f.twist = 1 := by
  induction O using Multiset.induction_on with
  | empty => simp
  | cons f O ih =>
    have h₁ := one_le_twist f
    have h₂ := card_le_twist O
    simp only [twist_cons, Multiset.card_cons, Multiset.mem_cons, forall_eq_or_imp]
    constructor
    · intro h
      exact ⟨by omega, ih.1 (by omega)⟩
    · rintro ⟨hf, hO⟩
      rw [hf, ih.2 hO, add_comm]

/-- A derivative-free operator has twist one exactly when it is a single twist-one field. -/
theorem twist_eq_one_iff {O : FieldContent} :
    twist O = 1 ↔ ∃ f, f.twist = 1 ∧ O = {f} := by
  refine ⟨fun h ↦ ?_, by rintro ⟨f, hf, rfl⟩; simp [*]⟩
  have hcard := card_le_twist O
  obtain h0 | h1 : Multiset.card O = 0 ∨ Multiset.card O = 1 := by omega
  · simp_all
  · obtain ⟨a, rfl⟩ := Multiset.card_eq_one.1 h1
    exact ⟨a, by simpa using h, rfl⟩

/-- A derivative-free operator has twist two exactly when it is a single twist-two field or a
bilinear in twist-one fields. -/
theorem twist_eq_two_iff {O : FieldContent} :
    twist O = 2 ↔ (∃ f, f.twist = 2 ∧ O = {f}) ∨
      ∃ f g, f.twist = 1 ∧ g.twist = 1 ∧ O = {f, g} := by
  refine ⟨fun h ↦ ?_, by rintro (⟨f, hf, rfl⟩ | ⟨f, g, hf, hg, rfl⟩) <;> simp [*]⟩
  have hcard := card_le_twist O
  obtain h0 | h1 | h2 : Multiset.card O = 0 ∨ Multiset.card O = 1 ∨ Multiset.card O = 2 := by
    omega
  · simp_all
  · obtain ⟨a, rfl⟩ := Multiset.card_eq_one.1 h1
    exact .inl ⟨a, by simpa using h, rfl⟩
  · have hgood := twist_eq_card_iff.1 (h.trans h2.symm)
    obtain ⟨a, b, rfl⟩ := Multiset.card_eq_two.1 h2
    exact .inr ⟨a, b, hgood a (by simp), hgood b (by simp), rfl⟩

/-- A derivative-free operator has twist three exactly when it is a single twist-three field, a
bilinear in a twist-one and a twist-two field, or a trilinear in twist-one fields. -/
theorem twist_eq_three_iff {O : FieldContent} :
    twist O = 3 ↔ (∃ f, f.twist = 3 ∧ O = {f}) ∨
      (∃ f g, f.twist = 1 ∧ g.twist = 2 ∧ O = {f, g}) ∨
      ∃ f g k, f.twist = 1 ∧ g.twist = 1 ∧ k.twist = 1 ∧ O = {f, g, k} := by
  refine ⟨fun h ↦ ?_, by
    rintro (⟨f, hf, rfl⟩ | ⟨f, g, hf, hg, rfl⟩ | ⟨f, g, k, hf, hg, hk, rfl⟩) <;> simp [*]⟩
  have hcard := card_le_twist O
  obtain h0 | h1 | h2 | h3 : Multiset.card O = 0 ∨ Multiset.card O = 1 ∨
      Multiset.card O = 2 ∨ Multiset.card O = 3 := by
    omega
  · simp_all
  · obtain ⟨a, rfl⟩ := Multiset.card_eq_one.1 h1
    exact .inl ⟨a, by simpa using h, rfl⟩
  · -- Two fields of total twist three: one has twist one and the other twist two.
    obtain ⟨a, b, rfl⟩ := Multiset.card_eq_two.1 h2
    have ha := one_le_twist a
    have hb := one_le_twist b
    have hab : a.twist + b.twist = 3 := by simpa using h
    obtain ha' | ha' : a.twist = 1 ∨ a.twist = 2 := by omega
    · exact .inr <| .inl ⟨a, b, ha', by omega, rfl⟩
    · exact .inr <| .inl ⟨b, a, by omega, ha', Multiset.pair_comm a b⟩
  · have hgood := twist_eq_card_iff.1 (h.trans h3.symm)
    obtain ⟨a, b, c, rfl⟩ := Multiset.card_eq_three.1 h3
    exact .inr <| .inr ⟨a, b, c, hgood a (by simp), hgood b (by simp), hgood c (by simp), rfl⟩

/-- A derivative-free quark-number-neutral operator of twist two is a bilinear in good quark
fields (such as `ψbar_+ γ^+ ψ_+`) or in two `F^{+i}` (such as `F^{+i} F^{+j}`), or a single
`F^{+-}` or `F^{ij}`. -/
theorem twist_eq_two_iff_of_quarkNumber_eq_zero {O : FieldContent} (hO : quarkNumber O = 0) :
    twist O = 2 ↔ O = {quarkBar .good, quark .good} ∨
      O = {fieldStrength .plusTransverse, fieldStrength .plusTransverse} ∨
      O = {fieldStrength .plusMinus} ∨ O = {fieldStrength .purelyTransverse} := by
  refine ⟨fun h ↦ ?_, by rintro (rfl | rfl | rfl | rfl) <;> simp⟩
  obtain ⟨a, ha, rfl⟩ | ⟨a, b, ha, hb, rfl⟩ := twist_eq_two_iff.1 h
  · rcases a with (_ | _) | (_ | _) | (_ | _ | _ | _) <;> simp_all
  · simp only [LightConeField.twist_eq_one_iff] at ha hb
    obtain ha | ha | ha := ha <;> obtain hb | hb | hb := hb <;> subst ha hb
    -- The quark-number-violating field contents contradict `hO`; the others are listed.
    all_goals simp at hO
    all_goals decide

/-- A derivative-free quark-number-neutral operator of twist three is a bilinear with one
twist-one and one twist-two field (such as `ψbar_+ ψ_-` or `ψbar_- ψ_+` in quark fields, or
`F^{+i} F^{+-}` or `F^{+i} F^{jk}`), a trilinear in good quark fields and one `F^{+i}` (such as
`ψbar_+ γ^+ F^{+i} ψ_+`) or in three `F^{+i}` (such as `F^{+i} F^{+j} F^{+k}`), or a single
`F^{-i}`. -/
theorem twist_eq_three_iff_of_quarkNumber_eq_zero {O : FieldContent} (hO : quarkNumber O = 0) :
    twist O = 3 ↔ O = {quarkBar .good, quark .bad} ∨ O = {quarkBar .bad, quark .good} ∨
      O = {fieldStrength .plusTransverse, fieldStrength .plusMinus} ∨
      O = {fieldStrength .plusTransverse, fieldStrength .purelyTransverse} ∨
      O = {quarkBar .good, fieldStrength .plusTransverse, quark .good} ∨
      O = {fieldStrength .plusTransverse, fieldStrength .plusTransverse,
        fieldStrength .plusTransverse} ∨
      O = {fieldStrength .minusTransverse} := by
  refine ⟨fun h ↦ ?_, by rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> simp⟩
  obtain ⟨a, ha, rfl⟩ | ⟨a, b, ha, hb, rfl⟩ | ⟨a, b, c, ha, hb, hc, rfl⟩ :=
    twist_eq_three_iff.1 h
  · rcases a with (_ | _) | (_ | _) | (_ | _ | _ | _) <;> simp_all
  · simp only [LightConeField.twist_eq_one_iff, LightConeField.twist_eq_two_iff] at ha hb
    obtain ha | ha | ha := ha <;> obtain hb | hb | hb | hb := hb <;> subst ha hb
    -- The quark-number-violating field contents contradict `hO`; the others are listed.
    all_goals simp at hO
    all_goals decide
  · simp only [LightConeField.twist_eq_one_iff] at ha hb hc
    obtain ha | ha | ha := ha <;> obtain hb | hb | hb := hb <;> obtain hc | hc | hc := hc <;>
      subst ha hb hc
    -- The quark-number-violating field contents contradict `hO`; the others are listed.
    all_goals simp at hO
    all_goals decide

end FieldContent

end EpsilonEridani.Particles.Parton.HigherTwist
