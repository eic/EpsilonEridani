/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Collinear twist of light-cone operators

Fix light-like vectors `n`, `n̄` with `n·n̄ = 1` and write `v^+ = n·v`, `v^- = n̄·v` for the
light-cone components of a vector (so `γ^+ = n̸` and `γ^- = n̸̄`), the remaining two components
being transverse. A boost along
the light-cone axis with rapidity `η` rescales `v^± ↦ e^{±η} v^±`. The quark field splits into its
good and bad projections `ψ_± = P_± ψ`, `P_± = ½ γ^∓ γ^±`, which rescale by `e^{±η/2}`; the
antiquark field `ψ̄_± = \overline{ψ_±}` rescales in the same way. The gluon field strength `F^{μν}`
splits into the components `F^{+i}`, `F^{+-}`, `F^{ij}` and `F^{-i}` (`i, j` transverse), which
rescale by `e^{η}`, `1`, `1` and `e^{-η}`. The exponent of `e^{η}` is the *light-cone spin* `s` of
the field component.

The *collinear twist* of a field component is `t = d - s`, its canonical mass dimension (`3/2`
for a quark field, `2` for the field strength) minus its light-cone spin. It is a positive integer:
good quark fields and `F^{+i}` have twist one, bad quark fields, `F^{+-}` and `F^{ij}` have twist
two, and `F^{-i}` has twist three. The twist of a light-cone operator is computed from its field
content, as its mass dimension minus its light-cone spin, both of which are additive over the field
insertions. The light-cone positions of the insertions and the Dirac and colour structure
contracting them do not enter the grading, so the field content is recorded as a multiset of
field components and nothing else. A Dirac structure selects which projections appear: the
scalar `ψ̄ ψ = ψ̄_+ ψ_- + ψ̄_- ψ_+` is a sum of two twist-three monomials, while `ψ̄ γ^+ ψ` only
involves `ψ̄_+ ψ_+` and has twist two.

Twist is the grading by which forward nucleon matrix elements of light-cone operators are
organised: the twist-two operators give the leading-power parton densities, the twist-three
operators the two- and three-parton correlators behind `g_T`, `h_L`, `e` and the
Efremov-Teryaev-Qiu-Sterman function, and the twist-four operators the `1/Q²` power corrections
to the inclusive structure functions.

## Main definitions

* `LightConeField`: a quark, antiquark or gluon field-strength component on the light cone.
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
* `FieldContent.twist_eq_two_iff`: a quark-number-neutral operator of twist two is a bilinear in
  good quark fields or in transverse field strengths, or a single `F^{+-}` or `F^{ij}`.
* `FieldContent.twist_eq_three_iff`: a quark-number-neutral operator of twist three is a bilinear
  with one twist-two field (a bad quark field, `F^{+-}` or `F^{ij}`), a trilinear in good quark
  fields and a transverse field strength or in three transverse field strengths, or a single
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
  | transverse
  /-- The components `F^{-i}`, of light-cone spin `-1`. -/
  | minusTransverse
  deriving DecidableEq

/-- A field insertion in a light-cone operator: a projection of the quark field `ψ` or of the
antiquark field `ψ̄`, or a light-cone component of the gluon field strength. -/
inductive LightConeField
  /-- A projection `ψ_±` of the quark field. -/
  | quark (p : QuarkProjection)
  /-- A projection `ψ̄_±` of the antiquark field. -/
  | antiquark (p : QuarkProjection)
  /-- A light-cone component of the gluon field strength. -/
  | fieldStrength (c : FieldStrengthComponent)
  deriving DecidableEq

namespace LightConeField

/-- The canonical mass dimension of a field component in four dimensions: `3/2` for quark and
antiquark fields and `2` for the gluon field strength. -/
def massDimension : LightConeField → ℚ
  | quark _ => 3 / 2
  | antiquark _ => 3 / 2
  | fieldStrength _ => 2

/-- The light-cone spin of a field component: the exponent of `e^η` by which it rescales under a
boost of rapidity `η` along the light-cone axis. -/
def lightConeSpin : LightConeField → ℚ
  | quark .good | antiquark .good => 1 / 2
  | quark .bad | antiquark .bad => -1 / 2
  | fieldStrength .plusTransverse => 1
  | fieldStrength .plusMinus | fieldStrength .transverse => 0
  | fieldStrength .minusTransverse => -1

/-- The collinear twist of a field component, its mass dimension minus its light-cone spin
(`twist_eq_massDimension_sub_lightConeSpin`). -/
def twist : LightConeField → ℕ
  | quark .good | antiquark .good => 1
  | quark .bad | antiquark .bad => 2
  | fieldStrength .plusTransverse => 1
  | fieldStrength .plusMinus | fieldStrength .transverse => 2
  | fieldStrength .minusTransverse => 3

/-- The quark number of a field component: `1` for a quark field, `-1` for an antiquark field
and `0` for the gluon field strength. -/
def quarkNumber : LightConeField → ℤ
  | quark _ => 1
  | antiquark _ => -1
  | fieldStrength _ => 0

@[simp] theorem massDimension_quark (p : QuarkProjection) :
    (quark p).massDimension = 3 / 2 := (rfl)

@[simp] theorem massDimension_antiquark (p : QuarkProjection) :
    (antiquark p).massDimension = 3 / 2 := (rfl)

@[simp] theorem massDimension_fieldStrength (c : FieldStrengthComponent) :
    (fieldStrength c).massDimension = 2 := (rfl)

@[simp] theorem lightConeSpin_quark_good : (quark .good).lightConeSpin = 1 / 2 := (rfl)

@[simp] theorem lightConeSpin_quark_bad : (quark .bad).lightConeSpin = -1 / 2 := (rfl)

@[simp] theorem lightConeSpin_antiquark_good : (antiquark .good).lightConeSpin = 1 / 2 := (rfl)

@[simp] theorem lightConeSpin_antiquark_bad : (antiquark .bad).lightConeSpin = -1 / 2 := (rfl)

@[simp] theorem lightConeSpin_plusTransverse :
    (fieldStrength .plusTransverse).lightConeSpin = 1 := (rfl)

@[simp] theorem lightConeSpin_plusMinus : (fieldStrength .plusMinus).lightConeSpin = 0 := (rfl)

@[simp] theorem lightConeSpin_transverse : (fieldStrength .transverse).lightConeSpin = 0 := (rfl)

@[simp] theorem lightConeSpin_minusTransverse :
    (fieldStrength .minusTransverse).lightConeSpin = -1 := (rfl)

@[simp] theorem twist_quark_good : (quark .good).twist = 1 := (rfl)

@[simp] theorem twist_quark_bad : (quark .bad).twist = 2 := (rfl)

@[simp] theorem twist_antiquark_good : (antiquark .good).twist = 1 := (rfl)

@[simp] theorem twist_antiquark_bad : (antiquark .bad).twist = 2 := (rfl)

@[simp] theorem twist_plusTransverse : (fieldStrength .plusTransverse).twist = 1 := (rfl)

@[simp] theorem twist_plusMinus : (fieldStrength .plusMinus).twist = 2 := (rfl)

@[simp] theorem twist_transverse : (fieldStrength .transverse).twist = 2 := (rfl)

@[simp] theorem twist_minusTransverse : (fieldStrength .minusTransverse).twist = 3 := (rfl)

@[simp] theorem quarkNumber_quark (p : QuarkProjection) : (quark p).quarkNumber = 1 := (rfl)

@[simp] theorem quarkNumber_antiquark (p : QuarkProjection) : (antiquark p).quarkNumber = -1 :=
  (rfl)

@[simp] theorem quarkNumber_fieldStrength (c : FieldStrengthComponent) :
    (fieldStrength c).quarkNumber = 0 := (rfl)

/-- The twist of a field component is its mass dimension minus its light-cone spin. -/
theorem twist_eq_massDimension_sub_lightConeSpin (f : LightConeField) :
    (f.twist : ℚ) = f.massDimension - f.lightConeSpin := by
  rcases f with (_ | _) | (_ | _) | (_ | _ | _ | _) <;> norm_num

/-- Every field component has twist at least one. -/
theorem one_le_twist (f : LightConeField) : 1 ≤ f.twist := by
  rcases f with (_ | _) | (_ | _) | (_ | _ | _ | _) <;> simp

/-- The field components of twist one are the good ones: `ψ_+`, `ψ̄_+` and `F^{+i}`. -/
theorem twist_eq_one_iff {f : LightConeField} :
    f.twist = 1 ↔ f = quark .good ∨ f = antiquark .good ∨ f = fieldStrength .plusTransverse := by
  rcases f with (_ | _) | (_ | _) | (_ | _ | _ | _) <;> simp

/-- The field components of twist two: `ψ_-`, `ψ̄_-`, `F^{+-}` and `F^{ij}`. -/
theorem twist_eq_two_iff {f : LightConeField} :
    f.twist = 2 ↔ f = quark .bad ∨ f = antiquark .bad ∨ f = fieldStrength .plusMinus ∨
      f = fieldStrength .transverse := by
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

/-- The quark number of an operator, the number of quark fields minus the number of antiquark
fields. -/
def quarkNumber (O : FieldContent) : ℤ := (O.map LightConeField.quarkNumber).sum

@[simp] theorem massDimension_zero : massDimension 0 = 0 := (rfl)

@[simp] theorem lightConeSpin_zero : lightConeSpin 0 = 0 := (rfl)

@[simp] theorem twist_zero : twist 0 = 0 := (rfl)

@[simp] theorem quarkNumber_zero : quarkNumber 0 = 0 := (rfl)

@[simp] theorem massDimension_cons (f : LightConeField) (O : FieldContent) :
    massDimension (f ::ₘ O) = f.massDimension + massDimension O := by
  simp [massDimension]

@[simp] theorem lightConeSpin_cons (f : LightConeField) (O : FieldContent) :
    lightConeSpin (f ::ₘ O) = f.lightConeSpin + lightConeSpin O := by
  simp [lightConeSpin]

@[simp] theorem twist_cons (f : LightConeField) (O : FieldContent) :
    twist (f ::ₘ O) = f.twist + twist O := by
  simp [twist]

@[simp] theorem quarkNumber_cons (f : LightConeField) (O : FieldContent) :
    quarkNumber (f ::ₘ O) = f.quarkNumber + quarkNumber O := by
  simp [quarkNumber]

@[simp] theorem massDimension_singleton (f : LightConeField) :
    massDimension {f} = f.massDimension := by
  simp [massDimension]

@[simp] theorem lightConeSpin_singleton (f : LightConeField) :
    lightConeSpin {f} = f.lightConeSpin := by
  simp [lightConeSpin]

@[simp] theorem twist_singleton (f : LightConeField) : twist {f} = f.twist := by
  simp [twist]

@[simp] theorem quarkNumber_singleton (f : LightConeField) : quarkNumber {f} = f.quarkNumber := by
  simp [quarkNumber]

/-- The mass dimension is additive under products of operators. -/
@[simp] theorem massDimension_add (O O' : FieldContent) :
    massDimension (O + O') = massDimension O + massDimension O' := by
  simp [massDimension]

/-- The light-cone spin is additive under products of operators. -/
@[simp] theorem lightConeSpin_add (O O' : FieldContent) :
    lightConeSpin (O + O') = lightConeSpin O + lightConeSpin O' := by
  simp [lightConeSpin]

/-- Twist is additive under products of operators. -/
@[simp] theorem twist_add (O O' : FieldContent) : twist (O + O') = twist O + twist O' := by
  simp [twist]

/-- The quark number is additive under products of operators. -/
@[simp] theorem quarkNumber_add (O O' : FieldContent) :
    quarkNumber (O + O') = quarkNumber O + quarkNumber O' := by
  simp [quarkNumber]

/-- The twist of an operator is its mass dimension minus its light-cone spin. -/
theorem twist_eq_massDimension_sub_lightConeSpin (O : FieldContent) :
    (twist O : ℚ) = massDimension O - lightConeSpin O := by
  induction O using Multiset.induction_on with
  | empty => simp
  | cons f O ih =>
    simp only [twist_cons, Nat.cast_add, massDimension_cons, lightConeSpin_cons, ih,
      LightConeField.twist_eq_massDimension_sub_lightConeSpin]
    ring

/-- An operator has twist at least its number of fields. -/
theorem card_le_twist (O : FieldContent) : Multiset.card O ≤ twist O := by
  induction O using Multiset.induction_on with
  | empty => simp
  | cons f O ih =>
    have := one_le_twist f
    simp only [Multiset.card_cons, twist_cons]
    omega

/-- An operator has twist equal to its number of fields exactly when all its fields are good
components. -/
theorem twist_eq_card_iff {O : FieldContent} :
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

/-- A quark-number-neutral operator of twist two is a bilinear `ψ̄_+ ψ_+` in good quark fields or
`F^{+i} F^{+j}` in transverse field strengths, or a single `F^{+-}` or `F^{ij}`. -/
theorem twist_eq_two_iff {O : FieldContent} (hO : quarkNumber O = 0) :
    twist O = 2 ↔ O = {antiquark .good, quark .good} ∨
      O = {fieldStrength .plusTransverse, fieldStrength .plusTransverse} ∨
      O = {fieldStrength .plusMinus} ∨ O = {fieldStrength .transverse} := by
  refine ⟨fun h ↦ ?_, by rintro (rfl | rfl | rfl | rfl) <;> simp⟩
  have hcard := card_le_twist O
  obtain h0 | h1 | h2 : Multiset.card O = 0 ∨ Multiset.card O = 1 ∨ Multiset.card O = 2 := by
    omega
  · simp_all
  · obtain ⟨a, rfl⟩ := Multiset.card_eq_one.1 h1
    rcases a with (_ | _) | (_ | _) | (_ | _ | _ | _) <;> simp_all
  · -- Two fields of total twist two: both are good components.
    have hgood := twist_eq_card_iff.1 (h.trans h2.symm)
    obtain ⟨a, b, rfl⟩ := Multiset.card_eq_two.1 h2
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton,
      forall_eq_or_imp, forall_eq, LightConeField.twist_eq_one_iff] at hgood
    obtain ⟨ha | ha | ha, hb | hb | hb⟩ := hgood <;> subst ha hb <;>
      first | decide | simp_all

/-- A quark-number-neutral operator of twist three is either a bilinear with one twist-one and
one twist-two field — `ψ̄_+ ψ_-` or `ψ̄_- ψ_+` with one bad quark field, or `F^{+i} F^{+-}` or
`F^{+i} F^{jk}` — or a trilinear `ψ̄_+ F^{+i} ψ_+` in good quark fields and a transverse field
strength or `F^{+i} F^{+j} F^{+k}` in transverse field strengths, or a single `F^{-i}`. -/
theorem twist_eq_three_iff {O : FieldContent} (hO : quarkNumber O = 0) :
    twist O = 3 ↔ O = {antiquark .good, quark .bad} ∨ O = {antiquark .bad, quark .good} ∨
      O = {fieldStrength .plusTransverse, fieldStrength .plusMinus} ∨
      O = {fieldStrength .plusTransverse, fieldStrength .transverse} ∨
      O = {antiquark .good, fieldStrength .plusTransverse, quark .good} ∨
      O = {fieldStrength .plusTransverse, fieldStrength .plusTransverse,
        fieldStrength .plusTransverse} ∨
      O = {fieldStrength .minusTransverse} := by
  refine ⟨fun h ↦ ?_, by rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> simp⟩
  have hcard := card_le_twist O
  obtain h0 | h1 | h2 | h3 : Multiset.card O = 0 ∨ Multiset.card O = 1 ∨
      Multiset.card O = 2 ∨ Multiset.card O = 3 := by
    omega
  · simp_all
  · obtain ⟨a, rfl⟩ := Multiset.card_eq_one.1 h1
    rcases a with (_ | _) | (_ | _) | (_ | _ | _ | _) <;> simp_all
  · -- Two fields: check every pair; `decide` closes the true cases up to reordering, and the
    -- remaining pairs have the wrong twist or quark number.
    obtain ⟨a, b, rfl⟩ := Multiset.card_eq_two.1 h2
    rcases a with (_ | _) | (_ | _) | (_ | _ | _ | _) <;>
      rcases b with (_ | _) | (_ | _) | (_ | _ | _ | _) <;>
      first | decide | simp_all
  · -- Three fields of total twist three: all are good components.
    have hgood := twist_eq_card_iff.1 (h.trans h3.symm)
    obtain ⟨a, b, c, rfl⟩ := Multiset.card_eq_three.1 h3
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton,
      forall_eq_or_imp, forall_eq, LightConeField.twist_eq_one_iff] at hgood
    obtain ⟨ha | ha | ha, hb | hb | hb, hc | hc | hc⟩ := hgood <;> subst ha hb hc <;>
      first | decide | simp_all

end FieldContent

end EpsilonEridani.Particles.Parton.HigherTwist
