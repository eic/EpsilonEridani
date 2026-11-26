/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.QFT.Scattering.DIS.Tensors.Basic

/-!
# The elastic electromagnetic form factor of a spin-zero state

The elastic matrix element `J^μ = ⟨h(p')| J^μ_em(0) |h(p)⟩` of the electromagnetic current
between two spin-zero states is a vector built from the two momenta alone. This file proves
that, at one transition `p → p'` between states of equal mass, Lorentz covariance and current
conservation leave exactly one structure in it,

  `⟨h(p')| J^μ_em(0) |h(p)⟩ = A (p + p')^μ`,

with a unique real coefficient `A` (`FormFactor.IsLorentzCovariant.existsUnique_eq_smul`). That
`A` depends on the transition only through `t = (p' - p)²`, so that it is the value `F(t)` of a
form factor, is *not* proved here: it is carried as part of what `FormFactor.HasFormFactor`
asserts. Under that assumption the file shows that `F(0)` is the charge when the forward matrix
element carries the charge, defines the charge radius, and works out the single-pole form factor.

## The setting

As in `EpsilonEridani.QFT.Scattering.DIS.Tensors.Basic`, vectors live in an abstract real vector
space `V` with a symmetric bilinear form `g` in the role of the metric, with the `+---` sign
convention, so that the invariant momentum transfer `t = g q q` of `q = p' - p` is negative in
the spacelike region where the form factor is measured. Covariance at the transition `p → p'` is
`FormFactor.IsLorentzCovariant`: the matrix element is fixed by every element of the stabilizer
`Bilin.IsPairStabilizer g p p'` of the two momenta. Its content comes from the reflections
`LinearMap.BilinForm.reflection` in the *spectator* directions, those `g`-orthogonal to both
momenta, each of which is such a stabilizer element (`Bilin.reflection_isPairStabilizer`). The
linear algebra that turns this into the two-structure form is collected in
`FormFactor.SpectatorAssumptions`: every vector is a combination of the two momenta plus a
spectator, and no non-zero spectator is null. These are statements about `g`, `p` and `p'`, not
about the matrix element. They hold in Minkowski space whenever `p` is timelike, and they are
verified below for an explicit transition on the `+--` form of `Kinematics.Witness.gWit`
(`FormFactor.Witness.spectatorAssumptions_pWit`).

## The two steps

Covariance alone leaves the two momenta
(`FormFactor.IsLorentzCovariant.exists_eq_smul_add_smul`), equivalently the sum `P = p + p'`
and the difference `q = p' - p`
(`FormFactor.IsLorentzCovariant.exists_eq_smul_add_add_smul_sub`). Current conservation
`g q J = 0` then reads `A (g p' p' - g p p) + B t = 0` for the coefficients `A` of `P` and `B` of
`q` (`FormFactor.apply_sub_smul_add_add_smul_sub`). When the two states have equal mass the first
term vanishes, so a non-zero `t` forces `B = 0`
(`FormFactor.eq_zero_of_smul_add_add_smul_sub_conserved`); this equal-mass hypothesis is exactly
what fails for a transition between different states. The single surviving coefficient is
unique as soon as `P ≠ 0` (`FormFactor.IsLorentzCovariant.existsUnique_eq_smul`), as at the
witness transition (`FormFactor.Witness.existsUnique_eq_smul_pWit`). The witness
transition also shows that neither hypothesis is idle: the difference structure is covariant but
not conserved (`FormFactor.Witness.isLorentzCovariant_pWit'_sub_pWit`,
`FormFactor.Witness.gWit_pWit'_sub_pWit_self_eq_neg_twelve`), and the spectator direction is
conserved but not covariant (`FormFactor.Witness.not_isLorentzCovariant_spectator_pWit`).

## The form factor as a function of `t`

`FormFactor.HasFormFactor g m2 J F` says that a family `J p p'` of matrix elements, indexed by the
momenta on the mass shell `g p p = m2`, is `F(t) (p + p')` throughout. That the coefficient of the
pointwise theorem depends on the transition only through `t` is the further statement that the
isometries act transitively on transitions with equal `t`, a Witt-type theorem not available in
Mathlib; it is not proved here, and `HasFormFactor` assumes it. Such a family is covariant and
conserved at every transition (`FormFactor.HasFormFactor.isLorentzCovariant`,
`FormFactor.HasFormFactor.conserved`), and its form factor is determined at every
momentum transfer that a transition with `p + p' ≠ 0` realises
(`FormFactor.HasFormFactor.formFactor_eq_of_apply_eq_smul`).

The normalisation is the Ward identity for the electromagnetic current in matrix-element form:
the charge operator `Q = ∫ d³x J⁰` acts on the state as its charge `e`, which for covariantly
normalised states is the forward matrix element `⟨h(p)| J^μ_em(0) |h(p)⟩ = 2 e p^μ`. The
forward matrix element of a family with a form factor is `2 F(0) p`
(`FormFactor.HasFormFactor.apply_self`), so the form factor at `t = 0` is the
charge exactly when that hypothesis holds (`FormFactor.HasFormFactor.formFactor_zero_eq_iff`).

## The charge radius and the single-pole form factor

For a form factor normalised to unit charge, `F(0) = 1`, the squared charge radius is
`⟨r²⟩ = 6 dF/dt (0)` (`FormFactor.chargeRadiusSq`), with the sign fixed by `t` rather than
`Q² = -t`; for charge `e` the same quantity is `e ⟨r²⟩`. The single-pole form factor
`F(t) = e Λ² / (Λ² - t)` (`FormFactor.singlePole`) has `F(0) = e`, `6 dF/dt (0) = 6 e / Λ²`, so
squared charge radius `6 / Λ²` (`FormFactor.chargeRadiusSq_singlePole`), and `t F(t) → -e Λ²`
as `t → -∞` (`FormFactor.tendsto_mul_singlePole_atBot`): the single-pole form factor falls like
`1/t` at large spacelike momentum transfer.

## References

* G. P. Lepage and S. J. Brodsky, *Exclusive processes in perturbative quantum chromodynamics*,
  Phys. Rev. D 22 (1980) 2157, section V: the form factor of a spin-zero hadron.
* S. R. Amendolia et al. (NA7), *A measurement of the space-like pion electromagnetic form
  factor*, Nucl. Phys. B 277 (1986) 168: the charge radius as `6 dF/dt (0)` and the single-pole
  fit.
* R. J. Holt and C. D. Roberts, *Distribution functions of the nucleon and pion in the valence
  region*, Rev. Mod. Phys. 82 (2010) 2991.
-/

public section

namespace EpsilonEridani.QFT.Scattering.Elastic.FormFactor

open Filter Topology
open EpsilonEridani.QFT.Scattering.DIS.Kinematics (Bilin)
open EpsilonEridani.QFT.Scattering.DIS.Tensors (Bilin.IsPairStabilizer Bilin.IsSpectatorSplit
  Bilin.isSpectatorSplit_of_gram_ne_zero Bilin.reflection_isPairStabilizer)

variable {V : Type} [AddCommGroup V] [Module ℝ V]

/-! ### Covariance at one transition -/

/-- Lorentz covariance of the matrix element `J` of a vector current at the transition `p → p'`
between two spin-zero states: `J` is built from `p`, `p'` and `g` alone, so it is fixed by every
`g`-isometry fixing both momenta. -/
def IsLorentzCovariant (g : Bilin V) (p p' J : V) : Prop :=
  ∀ f : V →ₗ[ℝ] V, Bilin.IsPairStabilizer g p p' f → f J = J

/-- `IsLorentzCovariant g p p' J` unfolds to invariance of `J` under the stabilizer of
`(p, p')`. -/
theorem isLorentzCovariant_iff (g : Bilin V) (p p' J : V) :
    IsLorentzCovariant g p p' J ↔ ∀ f : V →ₗ[ℝ] V, Bilin.IsPairStabilizer g p p' f → f J = J :=
  Iff.rfl

/-- Every combination of the two momenta is covariant. -/
theorem isLorentzCovariant_smul_add_smul (g : Bilin V) (p p' : V) (a b : ℝ) :
    IsLorentzCovariant g p p' (a • p + b • p') := by
  intro f hf
  rw [map_add, map_smul, map_smul, hf.fixes_left, hf.fixes_right]

/-- Every multiple of the sum of the momenta is covariant. -/
theorem isLorentzCovariant_smul_add (g : Bilin V) (p p' : V) (A : ℝ) :
    IsLorentzCovariant g p p' (A • (p + p')) := by
  rw [smul_add]
  exact isLorentzCovariant_smul_add_smul g p p' A A

/-- Every multiple of the difference of the momenta is covariant. -/
theorem isLorentzCovariant_smul_sub (g : Bilin V) (p p' : V) (B : ℝ) :
    IsLorentzCovariant g p p' (B • (p' - p)) := by
  have h : B • (p' - p) = (-B) • p + B • p' := by module
  rw [h]
  exact isLorentzCovariant_smul_add_smul g p p' (-B) B

/-- **Covariance has content.** A covariant matrix element has no component along a non-null
spectator direction: the reflection in that direction fixes both momenta and reverses it. -/
theorem IsLorentzCovariant.apply_spectator_eq_zero {g : Bilin V} (hSymm : g.IsSymm) {p p' J u : V}
    (hJ : IsLorentzCovariant g p p' J) (hu : g u u ≠ 0) (hpu : g p u = 0) (hp'u : g p' u = 0) :
    g u J = 0 := by
  have h := hJ _ (Bilin.reflection_isPairStabilizer g hSymm u
    (by rwa [hSymm.eq]) (by rwa [hSymm.eq]))
  rw [LinearMap.BilinForm.reflection_apply, sub_eq_self, smul_eq_zero] at h
  rcases h with h | h
  · simpa [hu] using h
  · simp [h] at hu

/-- A covariant combination of the two momenta plus a spectator `u` has a null spectator part:
were `u` non-null, the reflection in it would reverse it. -/
theorem IsLorentzCovariant.apply_spectator_self_eq_zero {g : Bilin V} (hSymm : g.IsSymm)
    {p p' u : V} (hpu : g p u = 0) (hp'u : g p' u = 0) {a b : ℝ}
    (hJ : IsLorentzCovariant g p p' (a • p + b • p' + u)) : g u u = 0 := by
  have hup : g u p = 0 := by rwa [hSymm.eq]
  have hup' : g u p' = 0 := by rwa [hSymm.eq]
  by_contra huu
  exact huu (by simpa [map_add, map_smul, hup, hup'] using
    hJ.apply_spectator_eq_zero hSymm huu hpu hp'u)

/-- Linear-algebra inputs about the spectator subspace `{p, p'}^⊥` of an elastic transition that
turn covariance into the two-structure form: the momenta split `V` (`Bilin.IsSpectatorSplit`),
and no non-zero spectator is null. They are facts about `g`, `p` and `p'`, not about the matrix
element. In Minkowski space they hold as soon as `p` is timelike: the plane spanned by the
momenta then contains a timelike vector, so its orthogonal complement is spacelike and
complementary to it. -/
structure SpectatorAssumptions (g : Bilin V) (p p' : V) : Prop
    extends Bilin.IsSpectatorSplit g p p' where
  /-- No non-zero spectator is null, so the reflection in it reverses it. -/
  anisotropic : ∀ u : V, g p u = 0 → g p' u = 0 → u ≠ 0 → g u u ≠ 0

/-- Under `SpectatorAssumptions`, a covariant combination of the two momenta plus a spectator
has zero spectator part. -/
theorem IsLorentzCovariant.spectator_eq_zero {g : Bilin V} (hSymm : g.IsSymm) {p p' u : V}
    (hS : SpectatorAssumptions g p p') (hpu : g p u = 0) (hp'u : g p' u = 0) {a b : ℝ}
    (hJ : IsLorentzCovariant g p p' (a • p + b • p' + u)) : u = 0 := by
  by_contra hu
  exact hS.anisotropic u hpu hp'u hu
    (hJ.apply_spectator_self_eq_zero hSymm hpu hp'u)

/-- **Covariance leaves the two momenta.** Under `SpectatorAssumptions`, a covariant
matrix element is a combination of `p` and `p'`. -/
theorem IsLorentzCovariant.exists_eq_smul_add_smul {g : Bilin V} (hSymm : g.IsSymm) {p p' J : V}
    (hS : SpectatorAssumptions g p p') (hJ : IsLorentzCovariant g p p' J) :
    ∃ a b : ℝ, J = a • p + b • p' := by
  obtain ⟨a, b, u, hpu, hp'u, rfl⟩ := hS.span J
  obtain rfl := hJ.spectator_eq_zero hSymm hS hpu hp'u
  exact ⟨a, b, add_zero _⟩

/-- Under `SpectatorAssumptions`, covariance leaves the sum and the difference of the
momenta. -/
theorem IsLorentzCovariant.exists_eq_smul_add_add_smul_sub {g : Bilin V} (hSymm : g.IsSymm)
    {p p' J : V} (hS : SpectatorAssumptions g p p') (hJ : IsLorentzCovariant g p p' J) :
    ∃ A B : ℝ, J = A • (p + p') + B • (p' - p) := by
  obtain ⟨a, b, rfl⟩ := hJ.exists_eq_smul_add_smul hSymm hS
  refine ⟨(a + b) / 2, (b - a) / 2, ?_⟩
  module

/-! ### Conservation at one transition -/

/-- Contraction of a combination of the sum and difference structures with the momentum
transfer: `q · (A P + B q) = A (p'² - p²) + B q²`. -/
theorem apply_sub_smul_add_add_smul_sub {g : Bilin V} (hSymm : g.IsSymm) (p p' : V) (A B : ℝ) :
    g (p' - p) (A • (p + p') + B • (p' - p)) =
      A * (g p' p' - g p p) + B * g (p' - p) (p' - p) := by
  have h : g p' p = g p p' := hSymm.eq p' p
  simp only [map_add, map_sub, map_smul, LinearMap.sub_apply, smul_eq_mul]
  rw [h]
  ring

/-- **Conservation removes the difference structure.** Between states of equal mass the sum
structure is conserved on its own, so a conserved combination at non-zero momentum transfer
has no difference component. -/
theorem eq_zero_of_smul_add_add_smul_sub_conserved {g : Bilin V} (hSymm : g.IsSymm) {p p' : V}
    {A B : ℝ} (hm : g p p = g p' p') (ht : g (p' - p) (p' - p) ≠ 0)
    (hJ : g (p' - p) (A • (p + p') + B • (p' - p)) = 0) : B = 0 := by
  rw [apply_sub_smul_add_add_smul_sub hSymm, hm, sub_self, mul_zero, zero_add] at hJ
  exact (mul_eq_zero.mp hJ).resolve_right ht

/-- Between states of equal mass, every multiple of the sum of the momenta is conserved. -/
theorem smul_add_conserved {g : Bilin V} (hSymm : g.IsSymm) {p p' : V}
    (hm : g p p = g p' p') (A : ℝ) : g (p' - p) (A • (p + p')) = 0 := by
  simpa [hm] using apply_sub_smul_add_add_smul_sub hSymm p p' A 0

/-- **One elastic form factor.** Under `SpectatorAssumptions`, at a transition between
states of equal mass with non-zero momentum transfer and `p + p' ≠ 0`, a covariant and conserved
matrix element of a vector current is a multiple of `p + p'`, by a unique coefficient. -/
theorem IsLorentzCovariant.existsUnique_eq_smul {g : Bilin V} (hSymm : g.IsSymm) {p p' J : V}
    (hS : SpectatorAssumptions g p p') (hm : g p p = g p' p')
    (ht : g (p' - p) (p' - p) ≠ 0) (hP : p + p' ≠ 0) (hJ : IsLorentzCovariant g p p' J)
    (hcons : g (p' - p) J = 0) : ∃! A : ℝ, J = A • (p + p') := by
  obtain ⟨A, B, rfl⟩ := hJ.exists_eq_smul_add_add_smul_sub hSymm hS
  obtain rfl := eq_zero_of_smul_add_add_smul_sub_conserved hSymm hm ht hcons
  refine ⟨A, by rw [zero_smul, add_zero], fun A' hA' => ?_⟩
  rw [zero_smul, add_zero] at hA'
  exact (smul_left_injective ℝ hP hA').symm

/-! ### The witness transition

On the `+--` form `gWit` of `Kinematics.Witness`, the transition from `p = (3, 0, 0)` at rest to
`p' = (5, 4, 0)` is between momenta of equal mass squared `9`, with spacelike momentum transfer
`q = (2, 4, 0)`, `t = -12`, and the single spectator direction `(0, 0, 1)`. -/

namespace Witness

open EpsilonEridani.QFT.Scattering.DIS.Kinematics.Witness (gWit gWit_apply gWit_isSymm)

/-- The incoming momentum of the witness transition, at rest with mass `3`. -/
def pWit : ℝ × ℝ × ℝ := (3, 0, 0)

/-- The outgoing momentum of the witness transition, on the same mass shell. -/
def pWit' : ℝ × ℝ × ℝ := (5, 4, 0)

/-- The components of the incoming witness momentum. -/
@[simp] theorem pWit_def : pWit = ((3, 0, 0) : ℝ × ℝ × ℝ) := (rfl)

/-- The components of the outgoing witness momentum. -/
@[simp] theorem pWit'_def : pWit' = ((5, 4, 0) : ℝ × ℝ × ℝ) := (rfl)

/-- The incoming witness momentum has mass squared `9`. -/
theorem gWit_pWit_self_eq_nine : gWit pWit pWit = 9 := by
  norm_num

/-- The outgoing witness momentum has mass squared `9`. -/
theorem gWit_pWit'_self_eq_nine : gWit pWit' pWit' = 9 := by
  norm_num

/-- The witness momentum transfer is spacelike, `t = -12`. In particular the difference
structure `p' - p` is not conserved: conservation, not covariance, is what removes it. -/
theorem gWit_pWit'_sub_pWit_self_eq_neg_twelve : gWit (pWit' - pWit) (pWit' - pWit) = -12 := by
  norm_num

/-- The sum of the witness momenta is non-zero. -/
theorem pWit_add_pWit'_ne_zero : pWit + pWit' ≠ 0 := by
  norm_num [Prod.ext_iff]

/-- The spectator assumptions hold at the witness transition. -/
theorem spectatorAssumptions_pWit : SpectatorAssumptions gWit pWit pWit' := by
  -- The Gram determinant of the two momenta is `9 · 9 - 15 · 15 = -144`.
  refine ⟨Bilin.isSpectatorSplit_of_gram_ne_zero gWit (by norm_num), fun u hup hup' hu => ?_⟩
  · obtain ⟨u₀, u₁, u₂⟩ := u
    simp only [gWit_apply, pWit_def, pWit'_def] at hup hup' ⊢
    have h₀ : u₀ = 0 := by linarith
    have h₁ : u₁ = 0 := by subst h₀; linarith
    subst h₀ h₁
    have h₂ : u₂ ≠ 0 := fun h => hu (by simp [h])
    simpa using h₂

/-- **One elastic form factor at the witness transition.** A covariant and conserved matrix
element at the witness transition is a unique multiple of `pWit + pWit'`. -/
theorem existsUnique_eq_smul_pWit {J : ℝ × ℝ × ℝ}
    (hJ : IsLorentzCovariant gWit pWit pWit' J) (hcons : gWit (pWit' - pWit) J = 0) :
    ∃! A : ℝ, J = A • (pWit + pWit') :=
  hJ.existsUnique_eq_smul gWit_isSymm spectatorAssumptions_pWit
    (gWit_pWit_self_eq_nine.trans gWit_pWit'_self_eq_nine.symm)
    (by rw [gWit_pWit'_sub_pWit_self_eq_neg_twelve]; norm_num) pWit_add_pWit'_ne_zero hcons

/-- The difference structure is covariant at the witness transition. -/
theorem isLorentzCovariant_pWit'_sub_pWit : IsLorentzCovariant gWit pWit pWit' (pWit' - pWit) := by
  simpa only [one_smul] using isLorentzCovariant_smul_sub gWit pWit pWit' 1

/-- The spectator direction is conserved at the witness transition. -/
theorem gWit_pWit'_sub_pWit_spectator_eq_zero : gWit (pWit' - pWit) (0, 0, 1) = 0 := by
  norm_num

/-- The spectator direction is not covariant at the witness transition: covariance, not
conservation, is what removes it. -/
theorem not_isLorentzCovariant_spectator_pWit :
    ¬ IsLorentzCovariant gWit pWit pWit' (0, 0, 1) := by
  intro h
  have := h.apply_spectator_eq_zero gWit_isSymm (u := (0, 0, 1)) (by norm_num) (by norm_num)
    (by norm_num)
  norm_num at this

end Witness

/-! ### The form factor as a function of the momentum transfer -/

/-- A family `J p p'` of elastic matrix elements of a vector current between states on the mass
shell `g p p = m2` has the form factor `F` if `J p p' = F(t) (p + p')` for every such transition,
with `t = g (p' - p) (p' - p)` the invariant momentum transfer.

This is an assumption, not a consequence of covariance and conservation: the pointwise theorem
`IsLorentzCovariant.existsUnique_eq_smul` gives a coefficient at each transition separately, and
`HasFormFactor` additionally assumes that this coefficient depends on the transition only through
`t`. Deriving that would need the isometries to act transitively on equal-mass transitions with
equal `t`, a Witt-type theorem that is not proved here. -/
def HasFormFactor (g : Bilin V) (m2 : ℝ) (J : V → V → V) (F : ℝ → ℝ) : Prop :=
  ∀ p p' : V, g p p = m2 → g p' p' = m2 → J p p' = F (g (p' - p) (p' - p)) • (p + p')

/-- `HasFormFactor g m2 J F` unfolds to `J p p' = F(t) (p + p')` on the mass shell. -/
theorem hasFormFactor_iff (g : Bilin V) (m2 : ℝ) (J : V → V → V) (F : ℝ → ℝ) :
    HasFormFactor g m2 J F ↔
      ∀ p p' : V, g p p = m2 → g p' p' = m2 → J p p' = F (g (p' - p) (p' - p)) • (p + p') :=
  Iff.rfl

/-- Every function of the momentum transfer is the form factor of the family it defines. -/
theorem hasFormFactor_smul_add (g : Bilin V) (m2 : ℝ) (F : ℝ → ℝ) :
    HasFormFactor g m2 (fun p p' => F (g (p' - p) (p' - p)) • (p + p')) F :=
  fun _ _ _ _ => rfl

namespace HasFormFactor

variable {g : Bilin V} {m2 : ℝ} {J : V → V → V} {F : ℝ → ℝ}

/-- A family with a form factor is covariant at every transition on the mass shell. -/
theorem isLorentzCovariant (hF : HasFormFactor g m2 J F) {p p' : V} (hp : g p p = m2)
    (hp' : g p' p' = m2) : IsLorentzCovariant g p p' (J p p') := by
  rw [hF p p' hp hp']
  exact isLorentzCovariant_smul_add g p p' _

/-- A family with a form factor is conserved at every transition on the mass shell. -/
theorem conserved (hF : HasFormFactor g m2 J F) (hSymm : g.IsSymm) {p p' : V}
    (hp : g p p = m2) (hp' : g p' p' = m2) : g (p' - p) (J p p') = 0 := by
  rw [hF p p' hp hp']
  exact smul_add_conserved hSymm (hp.trans hp'.symm) _

/-- The form factor is determined by the family at every momentum transfer realised by a
transition with `p + p' ≠ 0`: if the matrix element there is `A (p + p')`, then `F(t) = A`. In
particular two form factors of one family agree at every such `t`. -/
theorem formFactor_eq_of_apply_eq_smul (hF : HasFormFactor g m2 J F) {p p' : V}
    (hp : g p p = m2) (hp' : g p' p' = m2) (hP : p + p' ≠ 0) {A : ℝ}
    (hJ : J p p' = A • (p + p')) : F (g (p' - p) (p' - p)) = A :=
  smul_left_injective ℝ hP ((hF p p' hp hp').symm.trans hJ)

/-- The forward matrix element of a family with a form factor is `2 F(0) p`. -/
theorem apply_self (hF : HasFormFactor g m2 J F) {p : V} (hp : g p p = m2) :
    J p p = (2 * F 0) • p := by
  rw [hF p p hp hp, sub_self, map_zero]
  module

/-- **Charge normalisation.** The form factor at zero momentum transfer is `e` exactly when the
forward matrix element at a non-zero momentum `p` on the mass shell is `2 e p`. That forward
matrix element is the Ward identity for the electromagnetic current in matrix-element form: the
charge operator acts on the state as its charge `e`, and the states are covariantly normalised.
This file carries no charge operator, so the Ward identity enters as this equivalent condition. -/
theorem formFactor_zero_eq_iff (hF : HasFormFactor g m2 J F) {p : V} (hp : g p p = m2)
    (hp0 : p ≠ 0) {e : ℝ} : F 0 = e ↔ J p p = (2 * e) • p := by
  refine ⟨fun h => by rw [hF.apply_self hp, h], fun hJ => ?_⟩
  have := smul_left_injective ℝ hp0 ((hF.apply_self hp).symm.trans hJ)
  linarith

end HasFormFactor

/-! ### The charge radius -/

/-- Six times the slope at zero, `6 dF/dt (0)`, of a form factor `F` of the invariant momentum
transfer `t`. For a form factor normalised to unit charge, `F 0 = 1`, this is the squared charge
radius `⟨r²⟩`; for a form factor of charge `F 0 = e` it is the charge-weighted second moment
`e ⟨r²⟩`, so the squared radius is `chargeRadiusSq F / e`. For a form factor not differentiable
at zero this is `0` by the convention of `deriv`; the statements below carry the
differentiability as a hypothesis. -/
noncomputable def chargeRadiusSq (F : ℝ → ℝ) : ℝ := 6 * deriv F 0

/-- `chargeRadiusSq F` unfolds to `6 * deriv F 0`. -/
theorem chargeRadiusSq_def (F : ℝ → ℝ) : chargeRadiusSq F = 6 * deriv F 0 := (rfl)

/-- `chargeRadiusSq F = 6 F'` for a form factor with slope `F'` at zero; it is the squared charge
radius when `F 0 = 1`. -/
theorem chargeRadiusSq_eq {F : ℝ → ℝ} {F' : ℝ} (h : HasDerivAt F F' 0) :
    chargeRadiusSq F = 6 * F' := by
  rw [chargeRadiusSq_def, h.deriv]

/-! ### The single-pole form factor -/

/-- The single-pole form factor `F(t) = e Λ² / (Λ² - t)` of charge `e` and pole position
`t = Λ²`. -/
noncomputable def singlePole (e Λsq t : ℝ) : ℝ := e * Λsq / (Λsq - t)

/-- `singlePole e Λsq t` unfolds to `e * Λsq / (Λsq - t)`. -/
theorem singlePole_def (e Λsq t : ℝ) : singlePole e Λsq t = e * Λsq / (Λsq - t) := (rfl)

/-- The single-pole form factor is normalised to its charge. -/
@[simp]
theorem singlePole_zero (e : ℝ) {Λsq : ℝ} (hΛ : Λsq ≠ 0) : singlePole e Λsq 0 = e := by
  rw [singlePole_def, sub_zero, mul_div_cancel_right₀ _ hΛ]

/-- The derivative of the single-pole form factor away from the pole. -/
theorem hasDerivAt_singlePole (e : ℝ) {Λsq t : ℝ} (ht : t ≠ Λsq) :
    HasDerivAt (singlePole e Λsq) (e * Λsq / (Λsq - t) ^ 2) t := by
  have hne : Λsq - t ≠ 0 := sub_ne_zero.mpr ht.symm
  rw [funext (singlePole_def e Λsq)]
  refine ((hasDerivAt_const t (e * Λsq)).div ((hasDerivAt_id' t).const_sub Λsq) hne).congr_deriv
    ?_
  ring

/-- **`chargeRadiusSq` of the single-pole form factor.** Six times the slope at zero of the
single-pole form factor of charge `e` is `6 e / Λ²`; divided by the charge, its squared charge
radius is `6 / Λ²`, independent of `e`. -/
theorem chargeRadiusSq_singlePole (e : ℝ) {Λsq : ℝ} (hΛ : Λsq ≠ 0) :
    chargeRadiusSq (singlePole e Λsq) = 6 * e / Λsq := by
  rw [chargeRadiusSq_eq (hasDerivAt_singlePole e hΛ.symm), sub_zero]
  field_simp

/-- At large spacelike momentum transfer the single-pole form factor falls like `1 / t`:
`t F(t) → -e Λ²` as `t → -∞`. -/
theorem tendsto_mul_singlePole_atBot (e Λsq : ℝ) :
    Tendsto (fun t => t * singlePole e Λsq t) atBot (𝓝 (-(e * Λsq))) := by
  have hden : Tendsto (fun t : ℝ => Λsq - t) atBot atTop :=
    tendsto_atTop_add_const_left _ _ tendsto_neg_atBot_atTop
  -- Partial fractions: `t F(t) = -e Λ² + e Λ² · Λ² / (Λ² - t)`, and the last term tends to `0`.
  have hlim : Tendsto (fun t : ℝ => -(e * Λsq) + e * Λsq * (Λsq / (Λsq - t))) atBot
      (𝓝 (-(e * Λsq))) := by
    simpa only [mul_zero, add_zero] using
      ((tendsto_const_nhds (x := Λsq)).div_atTop hden).const_mul (e * Λsq) |>.const_add
        (-(e * Λsq))
  refine hlim.congr' ?_
  filter_upwards [hden.eventually_gt_atTop 0] with t ht
  have hne : Λsq - t ≠ 0 := ht.ne'
  rw [singlePole_def]
  field_simp
  ring

end EpsilonEridani.QFT.Scattering.Elastic.FormFactor
