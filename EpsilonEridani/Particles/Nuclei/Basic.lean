/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Data.Nat.Notation

/-!
# Nuclei as explicit data

A nucleus, for the purposes of nuclear parton densities and nuclear geometry, is the pair of its
mass number `A` and proton number `Z ≤ A`; the neutron number `N = A - Z` is derived. The nucleus is
a value passed to every definition that depends on it, never a typeclass, so that the mass-number
dependence of a statement is always a variable.

The free proton (`A = Z = 1`) and the free neutron (`A = 1`, `Z = 0`) are nuclei too, so that a
statement about a general nucleus has the free nucleon as an instance rather than as a separate
development.

## Main definitions

* `EpsilonEridani.Nucleus`: a mass number `0 < A` together with a proton number `Z ≤ A`.
* `EpsilonEridani.Nucleus.neutronNumber`: the neutron number `N = A - Z`.
* `EpsilonEridani.Nucleus.IsIsoscalar`: the nucleus has as many protons as neutrons, `2 Z = A`.
* `EpsilonEridani.Nucleus.proton`, `neutron`, `deuteron`, `carbon12`, `lead208`: the worked
  instances.

## Main statements

* `EpsilonEridani.Nucleus.protonNumber_add_neutronNumber`: `Z + N = A`.
* `EpsilonEridani.Nucleus.isIsoscalar_iff_protonNumber_eq_neutronNumber`: a nucleus is isoscalar
  exactly when `Z = N`.

## References

* EIC Yellow Report, `arXiv:2103.05419`, Vol. II, §7.3.3.
-/

public section

namespace EpsilonEridani

/-- A nucleus: a mass number `A` with `0 < A`, and a proton number `Z` with `Z ≤ A`. -/
@[ext]
structure Nucleus where
  /-- The mass number `A`, the number of nucleons. -/
  massNumber : ℕ
  /-- The proton number `Z`. -/
  protonNumber : ℕ
  /-- A nucleus has at least one nucleon. -/
  massNumber_pos : 0 < massNumber
  /-- The proton number does not exceed the mass number. -/
  protonNumber_le_massNumber : protonNumber ≤ massNumber

namespace Nucleus

variable (nuc : Nucleus)

/-- The neutron number `N = A - Z`. -/
def neutronNumber : ℕ := nuc.massNumber - nuc.protonNumber

lemma neutronNumber_def : nuc.neutronNumber = nuc.massNumber - nuc.protonNumber := (rfl)

/-- The proton and neutron numbers add up to the mass number. -/
@[simp]
theorem protonNumber_add_neutronNumber : nuc.protonNumber + nuc.neutronNumber = nuc.massNumber :=
  Nat.add_sub_cancel' nuc.protonNumber_le_massNumber

/-- The neutron and proton numbers add up to the mass number. -/
@[simp]
theorem neutronNumber_add_protonNumber : nuc.neutronNumber + nuc.protonNumber = nuc.massNumber := by
  rw [Nat.add_comm, protonNumber_add_neutronNumber]

lemma neutronNumber_le_massNumber : nuc.neutronNumber ≤ nuc.massNumber :=
  Nat.sub_le _ _

/-- A nucleus is *isoscalar* when it has equally many protons and neutrons, `2 Z = A`. -/
def IsIsoscalar : Prop := 2 * nuc.protonNumber = nuc.massNumber

lemma isIsoscalar_iff : nuc.IsIsoscalar ↔ 2 * nuc.protonNumber = nuc.massNumber := Iff.rfl

instance : DecidablePred IsIsoscalar := fun nuc =>
  decidable_of_iff _ (isIsoscalar_iff nuc).symm

/-- A nucleus is isoscalar exactly when its proton and neutron numbers agree. -/
theorem isIsoscalar_iff_protonNumber_eq_neutronNumber :
    nuc.IsIsoscalar ↔ nuc.protonNumber = nuc.neutronNumber := by
  have := nuc.protonNumber_add_neutronNumber
  rw [isIsoscalar_iff]
  omega

/-! ### Worked instances -/

/-- The free proton, `A = Z = 1`. -/
def proton : Nucleus := ⟨1, 1, Nat.one_pos, Nat.le_refl 1⟩

/-- The free neutron, `A = 1`, `Z = 0`. -/
def neutron : Nucleus := ⟨1, 0, Nat.one_pos, Nat.zero_le _⟩

/-- The deuteron, `A = 2`, `Z = 1`: the lightest isoscalar nucleus. -/
def deuteron : Nucleus := ⟨2, 1, Nat.two_pos, by decide⟩

/-- Carbon-12, `A = 12`, `Z = 6`. -/
def carbon12 : Nucleus := ⟨12, 6, by decide, by decide⟩

/-- Lead-208, `A = 208`, `Z = 82`: a heavy nucleus with a large neutron excess. -/
def lead208 : Nucleus := ⟨208, 82, by decide, by decide⟩

@[simp] lemma massNumber_proton : proton.massNumber = 1 := (rfl)
@[simp] lemma protonNumber_proton : proton.protonNumber = 1 := (rfl)
@[simp] lemma massNumber_neutron : neutron.massNumber = 1 := (rfl)
@[simp] lemma protonNumber_neutron : neutron.protonNumber = 0 := (rfl)
@[simp] lemma massNumber_deuteron : deuteron.massNumber = 2 := (rfl)
@[simp] lemma protonNumber_deuteron : deuteron.protonNumber = 1 := (rfl)
@[simp] lemma massNumber_carbon12 : carbon12.massNumber = 12 := (rfl)
@[simp] lemma protonNumber_carbon12 : carbon12.protonNumber = 6 := (rfl)
@[simp] lemma massNumber_lead208 : lead208.massNumber = 208 := (rfl)
@[simp] lemma protonNumber_lead208 : lead208.protonNumber = 82 := (rfl)

@[simp] lemma neutronNumber_proton : proton.neutronNumber = 0 := (rfl)
@[simp] lemma neutronNumber_neutron : neutron.neutronNumber = 1 := (rfl)
@[simp] lemma neutronNumber_deuteron : deuteron.neutronNumber = 1 := (rfl)
@[simp] lemma neutronNumber_carbon12 : carbon12.neutronNumber = 6 := (rfl)
@[simp] lemma neutronNumber_lead208 : lead208.neutronNumber = 126 := (rfl)

/-- The deuteron is isoscalar. -/
theorem isIsoscalar_deuteron : deuteron.IsIsoscalar := (rfl)

/-- Carbon-12 is isoscalar. -/
theorem isIsoscalar_carbon12 : carbon12.IsIsoscalar := (rfl)

/-- The free proton is not isoscalar. -/
theorem not_isIsoscalar_proton : ¬proton.IsIsoscalar := by decide

/-- The free neutron is not isoscalar. -/
theorem not_isIsoscalar_neutron : ¬neutron.IsIsoscalar := by decide

/-- Lead-208 is not isoscalar. -/
theorem not_isIsoscalar_lead208 : ¬lead208.IsIsoscalar := by decide

end Nucleus

end EpsilonEridani
