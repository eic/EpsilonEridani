/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.Particles.Meson.Basic
public import EpsilonEridani.QFT.Scattering.DIS.Tensors.Basic

/-!
# The elastic electromagnetic form factor of a spin-zero hadron

The elastic matrix element `J^μ = ⟨h(p')| J^μ_em(0) |h(p)⟩` of the electromagnetic current
between two states of a spin-zero hadron is a vector built from the two momenta alone. This file
proves that Lorentz covariance and current conservation leave exactly one structure in it,

  `⟨h(p')| J^μ_em(0) |h(p)⟩ = F(t) (p + p')^μ`,  `t = (p' - p)²`,

and that the coefficient `F`, the electromagnetic form factor, equals the hadron's charge at
`t = 0` when the forward matrix element carries the charge. It then defines the charge radius and
works out the single-pole form factor.

## The setting

As in `EpsilonEridani.QFT.Scattering.DIS.Tensors.Basic`, vectors live in an abstract real vector
space `V` with a symmetric bilinear form `g` in the role of the metric, with the `+---` sign
convention, so that the invariant momentum transfer `t = g q q` of `q = p' - p` is negative in
the spacelike region where the form factor is measured. Covariance at the transition `p → p'` is
`FormFactor.IsCovariant`: the matrix element is fixed by every `g`-isometry fixing both momenta.
Its content comes from the reflections `Bilin.reflect` in the *spectator* directions, those
`g`-orthogonal to both momenta, each of which is such an isometry
(`FormFactor.reflect_isElasticStabilizer`). The linear algebra that turns this into the
two-structure form is collected in `FormFactor.ElasticSpectatorAssumptions`: every vector is a
combination of the two momenta plus a spectator, and no non-zero spectator is null. These are
statements about `g`, `p` and `p'`, not about the matrix element. They hold in Minkowski space
whenever `p` is timelike, and they are verified below for an explicit
transition on the `+--` form of `Hadronic.Witness.gWit`
(`FormFactor.elasticSpectatorAssumptions_pWit`).

## The two steps

Covariance alone leaves two structures, the sum `P = p + p'` and the difference `q = p' - p`
(`FormFactor.IsCovariant.exists_eq_smul_add_smul`). Current conservation `g q J = 0` then reads
`A (g p' p' - g p p) + B t = 0` for the coefficients `A` of `P` and `B` of `q`
(`FormFactor.apply_sub_smul_add_smul`). When the two states have equal mass the first term
vanishes, so a non-zero `t` forces `B = 0`
(`FormFactor.coeff_sub_eq_zero_of_apply_sub_eq_zero`); this equal-mass hypothesis is exactly
what fails for a transition between different states. The single surviving coefficient is
unique as soon as `P ≠ 0` (`FormFactor.IsCovariant.existsUnique_eq_smul`). The witness
transition shows that neither hypothesis is idle: the difference structure is covariant but not
conserved (`FormFactor.isCovariant_pWit'_sub_pWit`, `FormFactor.gWit_sub_pWit`), and the spectator
direction is conserved but not covariant (`FormFactor.not_isCovariant_spectator`).

## The form factor as a function of `t`

`FormFactor.HasFormFactor g m2 J F` says that a family `J p p'` of matrix elements, indexed by the
momenta on the mass shell `g p p = m2`, is `F(t) (p + p')` throughout. Such a family is covariant
and conserved at every transition (`FormFactor.HasFormFactor.isCovariant`,
`FormFactor.HasFormFactor.apply_sub_eq_zero`), and its form factor is determined at every
momentum transfer that a transition with `p + p' ≠ 0` realises
(`FormFactor.HasFormFactor.apply_eq_of_hasFormFactor`). That the coefficient of the pointwise
theorem depends on the transition only through `t` is the further statement that the isometries
act transitively on transitions with equal `t`; it is not proved here, and `HasFormFactor` carries
it as part of what it asserts.

The normalisation is the Ward identity for the electromagnetic current in matrix-element form:
the charge operator `Q = ∫ d³x J⁰` acts on the hadron as its charge `e`, which for covariantly
normalised states is the forward matrix element `⟨h(p)| J^μ_em(0) |h(p)⟩ = 2 e p^μ`. Under that
hypothesis the form factor at `t = 0` is the charge (`FormFactor.HasFormFactor.apply_zero_eq`).

## The charge radius and the single-pole form factor

The squared charge radius is `⟨r²⟩ = 6 dF/dt (0)` (`FormFactor.chargeRadiusSq`), with the sign
fixed by `t` rather than `Q² = -t`. The single-pole form factor
`F(t) = e Λ² / (Λ² - t)` (`FormFactor.singlePole`) has `F(0) = e`, squared charge radius
`6 e / Λ²` (`FormFactor.chargeRadiusSq_singlePole`), and `t F(t) → -e Λ²` as `t → -∞`
(`FormFactor.tendsto_mul_singlePole_atBot`), so a form factor falling like `1/Q²` at large
spacelike momentum transfer needs no distribution amplitude to produce it. For the positive pion
this is a squared charge radius of `6 / Λ²` (`FormFactor.chargeRadiusSq_singlePole_piPlus`).

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

namespace EpsilonEridani.Particles.Meson.FormFactor

open Filter Topology
open EpsilonEridani.QFT.Scattering.DIS.Kinematics (Bilin)
open EpsilonEridani.QFT.Scattering.DIS.Tensors (Bilin.IsIsometry Bilin.reflect Bilin.reflect_apply
  Bilin.reflect_apply_of_orthogonal Bilin.reflect_isometry)

variable {V : Type} [AddCommGroup V] [Module ℝ V]

/-! ### Covariance at one transition -/

/-- A `g`-isometry fixing both momenta of the elastic transition `p → p'`: an element of the
stabiliser of the transition in the isometry group of `g`. Fixing `p` and `p'` is the same as
fixing `p` and the momentum transfer `p' - p`. -/
structure IsElasticStabilizer (g : Bilin V) (p p' : V) (f : V →ₗ[ℝ] V) : Prop where
  /-- `f` preserves the background form. -/
  isometry : Bilin.IsIsometry g f
  /-- `f` fixes the incoming momentum. -/
  fixes_left : f p = p
  /-- `f` fixes the outgoing momentum. -/
  fixes_right : f p' = p'

/-- Lorentz covariance of the matrix element `J` of a vector current at the transition `p → p'`
between two spin-zero states: `J` is built from `p`, `p'` and `g` alone, so it is fixed by every
isometry fixing both momenta. -/
def IsCovariant (g : Bilin V) (p p' J : V) : Prop :=
  ∀ f : V →ₗ[ℝ] V, IsElasticStabilizer g p p' f → f J = J

theorem isCovariant_iff (g : Bilin V) (p p' J : V) :
    IsCovariant g p p' J ↔ ∀ f : V →ₗ[ℝ] V, IsElasticStabilizer g p p' f → f J = J :=
  Iff.rfl

/-- Every combination of the two momenta is covariant. -/
theorem isCovariant_smul_add_smul (g : Bilin V) (p p' : V) (a b : ℝ) :
    IsCovariant g p p' (a • p + b • p') := by
  intro f hf
  rw [map_add, map_smul, map_smul, hf.fixes_left, hf.fixes_right]

/-- Every combination of the sum and the difference of the momenta is covariant. -/
theorem isCovariant_smul_add_add_smul_sub (g : Bilin V) (p p' : V) (A B : ℝ) :
    IsCovariant g p p' (A • (p + p') + B • (p' - p)) := by
  convert isCovariant_smul_add_smul g p p' (A - B) (A + B) using 1
  simp only [smul_add, smul_sub, sub_smul, add_smul]
  abel

/-- The reflection in a non-null spectator direction, one `g`-orthogonal to both momenta, is in
the stabiliser of the transition. -/
theorem reflect_isElasticStabilizer {g : Bilin V} (hSymm : g.IsSymm) {p p' u : V}
    (hu : g u u ≠ 0) (hup : g u p = 0) (hup' : g u p' = 0) :
    IsElasticStabilizer g p p' (Bilin.reflect g u) where
  isometry := Bilin.reflect_isometry g hSymm u hu
  fixes_left := Bilin.reflect_apply_of_orthogonal g u p hup
  fixes_right := Bilin.reflect_apply_of_orthogonal g u p' hup'

/-- **Covariance has content.** A covariant matrix element has no component along a non-null
spectator direction: the reflection in that direction fixes both momenta and reverses it. -/
theorem IsCovariant.apply_eq_zero {g : Bilin V} (hSymm : g.IsSymm) {p p' J u : V}
    (hJ : IsCovariant g p p' J) (hu : g u u ≠ 0) (hup : g u p = 0) (hup' : g u p' = 0) :
    g u J = 0 := by
  have h := hJ _ (reflect_isElasticStabilizer hSymm hu hup hup')
  rw [Bilin.reflect_apply, sub_eq_self, smul_eq_zero] at h
  rcases h with h | h
  · simpa [hu] using h
  · simp [h] at hu

/-- Linear-algebra inputs about the spectator subspace `{p, p'}^⊥` of an elastic transition that
turn covariance into the two-structure form. They are facts about `g`, `p` and `p'`, not about
the matrix element. In Minkowski space they hold as soon as `p` is timelike: the plane spanned by
the momenta then contains a timelike vector, so its orthogonal complement is spacelike and
complementary to it. -/
structure ElasticSpectatorAssumptions (g : Bilin V) (p p' : V) : Prop where
  /-- Every vector is a combination of the two momenta plus a spectator. -/
  span : ∀ v : V, ∃ (a b : ℝ) (u : V), g u p = 0 ∧ g u p' = 0 ∧ v = a • p + b • p' + u
  /-- No non-zero spectator is null, so the reflection in it is an isometry. -/
  anisotropic : ∀ u : V, g u p = 0 → g u p' = 0 → u ≠ 0 → g u u ≠ 0

/-- **Covariance leaves the two momenta.** Under `ElasticSpectatorAssumptions`, a covariant
matrix element is a combination of `p` and `p'`. -/
theorem IsCovariant.exists_eq_smul_add_smul {g : Bilin V} (hSymm : g.IsSymm) {p p' J : V}
    (hS : ElasticSpectatorAssumptions g p p') (hJ : IsCovariant g p p' J) :
    ∃ a b : ℝ, J = a • p + b • p' := by
  obtain ⟨a, b, u, hup, hup', rfl⟩ := hS.span J
  refine ⟨a, b, ?_⟩
  by_contra hne
  have hu : u ≠ 0 := fun h => hne (by rw [h, add_zero])
  have huu := hS.anisotropic u hup hup' hu
  apply huu
  have h := hJ.apply_eq_zero hSymm huu hup hup'
  simpa [map_add, map_smul, hup, hup'] using h

/-- Covariance leaves the sum and the difference of the momenta. -/
theorem IsCovariant.exists_eq_smul_add_add_smul_sub {g : Bilin V} (hSymm : g.IsSymm)
    {p p' J : V} (hS : ElasticSpectatorAssumptions g p p') (hJ : IsCovariant g p p' J) :
    ∃ A B : ℝ, J = A • (p + p') + B • (p' - p) := by
  obtain ⟨a, b, rfl⟩ := hJ.exists_eq_smul_add_smul hSymm hS
  refine ⟨(a + b) / 2, (b - a) / 2, ?_⟩
  module

/-! ### Conservation at one transition -/

/-- Contraction of a combination of the sum and difference structures with the momentum
transfer: `q · (A P + B q) = A (p'² - p²) + B q²`. -/
theorem apply_sub_smul_add_smul {g : Bilin V} (hSymm : g.IsSymm) (p p' : V) (A B : ℝ) :
    g (p' - p) (A • (p + p') + B • (p' - p)) =
      A * (g p' p' - g p p) + B * g (p' - p) (p' - p) := by
  have h : g p' p = g p p' := hSymm.eq p' p
  simp only [map_add, map_sub, map_smul, LinearMap.sub_apply, smul_eq_mul]
  rw [h]
  ring

/-- **Conservation removes the difference structure.** Between states of equal mass the sum
structure is conserved on its own, so a conserved combination at non-zero momentum transfer
has no difference component. -/
theorem coeff_sub_eq_zero_of_apply_sub_eq_zero {g : Bilin V} (hSymm : g.IsSymm) {p p' : V}
    {A B : ℝ} (hm : g p p = g p' p') (ht : g (p' - p) (p' - p) ≠ 0)
    (hJ : g (p' - p) (A • (p + p') + B • (p' - p)) = 0) : B = 0 := by
  rw [apply_sub_smul_add_smul hSymm, hm, sub_self, mul_zero, zero_add] at hJ
  exact (mul_eq_zero.mp hJ).resolve_right ht

/-- Between states of equal mass, every multiple of the sum of the momenta is conserved. -/
theorem apply_sub_smul_add_eq_zero {g : Bilin V} (hSymm : g.IsSymm) {p p' : V}
    (hm : g p p = g p' p') (A : ℝ) : g (p' - p) (A • (p + p')) = 0 := by
  simpa [hm] using apply_sub_smul_add_smul hSymm p p' A 0

/-- **One elastic form factor.** At a transition between states of equal mass with non-zero
momentum transfer and `p + p' ≠ 0`, a covariant and conserved matrix element of a vector current
is a multiple of `p + p'`, by a unique coefficient. -/
theorem IsCovariant.existsUnique_eq_smul {g : Bilin V} (hSymm : g.IsSymm) {p p' J : V}
    (hS : ElasticSpectatorAssumptions g p p') (hm : g p p = g p' p')
    (ht : g (p' - p) (p' - p) ≠ 0) (hP : p + p' ≠ 0) (hJ : IsCovariant g p p' J)
    (hcons : g (p' - p) J = 0) : ∃! A : ℝ, J = A • (p + p') := by
  obtain ⟨A, B, rfl⟩ := hJ.exists_eq_smul_add_add_smul_sub hSymm hS
  obtain rfl := coeff_sub_eq_zero_of_apply_sub_eq_zero hSymm hm ht hcons
  refine ⟨A, by rw [zero_smul, add_zero], fun A' hA' => ?_⟩
  rw [zero_smul, add_zero] at hA'
  exact (smul_left_injective ℝ hP hA').symm

/-! ### The witness transition

On the `+--` form `gWit` of `Hadronic.Witness`, the transition from `p = (3, 0, 0)` at rest to
`p' = (5, 4, 0)` is between momenta of equal mass squared `9`, with spacelike momentum transfer
`q = (2, 4, 0)`, `t = -12`, and the single spectator direction `(0, 0, 1)`. -/

open EpsilonEridani.QFT.Scattering.DIS.Tensors.Hadronic.Witness (gWit gWit_apply gWit_isSymm)

/-- The incoming momentum of the witness transition, at rest with mass `3`. -/
def pWit : ℝ × ℝ × ℝ := (3, 0, 0)

/-- The outgoing momentum of the witness transition, on the same mass shell. -/
def pWit' : ℝ × ℝ × ℝ := (5, 4, 0)

/-- The two witness momenta have equal mass squared. -/
theorem gWit_pWit_self_eq : gWit pWit pWit = gWit pWit' pWit' := by
  norm_num [pWit, pWit']

/-- The witness momentum transfer is spacelike, `t = -12`. In particular the difference
structure `p' - p` is not conserved: conservation, not covariance, is what removes it. -/
theorem gWit_sub_pWit : gWit (pWit' - pWit) (pWit' - pWit) = -12 := by
  norm_num [pWit, pWit']

/-- The spectator assumptions hold at the witness transition. -/
theorem elasticSpectatorAssumptions_pWit : ElasticSpectatorAssumptions gWit pWit pWit' where
  span v := ⟨v.1 / 3 - 5 * v.2.1 / 12, v.2.1 / 4, (0, 0, v.2.2), by norm_num [pWit],
    by norm_num [pWit'], by
      ext
      · simp only [pWit, pWit', Prod.fst_add, Prod.smul_fst, smul_eq_mul]
        ring
      all_goals simp [pWit, pWit']⟩
  anisotropic u hup hup' hu := by
    obtain ⟨u₀, u₁, u₂⟩ := u
    simp only [gWit_apply, pWit, pWit'] at hup hup' ⊢
    have h₀ : u₀ = 0 := by linarith
    have h₁ : u₁ = 0 := by subst h₀; linarith
    subst h₀ h₁
    have h₂ : u₂ ≠ 0 := fun h => hu (by simp [h])
    have := mul_self_ne_zero.mpr h₂
    intro h
    apply this
    linarith

/-- The difference structure is covariant at the witness transition. -/
theorem isCovariant_pWit'_sub_pWit : IsCovariant gWit pWit pWit' (pWit' - pWit) := by
  simpa using isCovariant_smul_add_add_smul_sub gWit pWit pWit' 0 1

/-- The spectator direction is conserved at the witness transition. -/
theorem gWit_sub_pWit_spectator_eq_zero : gWit (pWit' - pWit) (0, 0, 1) = 0 := by
  norm_num [pWit, pWit']

/-- The spectator direction is not covariant at the witness transition: covariance, not
conservation, is what removes it. -/
theorem not_isCovariant_spectator : ¬ IsCovariant gWit pWit pWit' (0, 0, 1) := by
  intro h
  have := h.apply_eq_zero gWit_isSymm (u := (0, 0, 1)) (by norm_num) (by norm_num [pWit])
    (by norm_num [pWit'])
  norm_num at this

/-! ### The form factor as a function of the momentum transfer -/

/-- A family `J p p'` of elastic matrix elements of a vector current between states on the mass
shell `g p p = m2` has the form factor `F` if `J p p' = F(t) (p + p')` for every such transition,
with `t = g (p' - p) (p' - p)` the invariant momentum transfer. -/
def HasFormFactor (g : Bilin V) (m2 : ℝ) (J : V → V → V) (F : ℝ → ℝ) : Prop :=
  ∀ p p' : V, g p p = m2 → g p' p' = m2 → J p p' = F (g (p' - p) (p' - p)) • (p + p')

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
theorem isCovariant (hF : HasFormFactor g m2 J F) {p p' : V} (hp : g p p = m2)
    (hp' : g p' p' = m2) : IsCovariant g p p' (J p p') := by
  rw [hF p p' hp hp']
  simpa using isCovariant_smul_add_add_smul_sub g p p' (F (g (p' - p) (p' - p))) 0

/-- A family with a form factor is conserved at every transition on the mass shell. -/
theorem apply_sub_eq_zero (hF : HasFormFactor g m2 J F) (hSymm : g.IsSymm) {p p' : V}
    (hp : g p p = m2) (hp' : g p' p' = m2) : g (p' - p) (J p p') = 0 := by
  rw [hF p p' hp hp']
  exact apply_sub_smul_add_eq_zero hSymm (hp.trans hp'.symm) _

/-- The form factor is determined by the family at every momentum transfer realised by a
transition with `p + p' ≠ 0`. -/
theorem apply_eq_of_hasFormFactor {F' : ℝ → ℝ} (hF : HasFormFactor g m2 J F)
    (hF' : HasFormFactor g m2 J F') {p p' : V} (hp : g p p = m2) (hp' : g p' p' = m2)
    (hP : p + p' ≠ 0) : F (g (p' - p) (p' - p)) = F' (g (p' - p) (p' - p)) :=
  smul_left_injective ℝ hP ((hF p p' hp hp').symm.trans (hF' p p' hp hp'))

/-- **Charge normalisation.** If the forward matrix element at a non-zero momentum `p` on the
mass shell is `2 e p`, the form factor at zero momentum transfer is `e`. The hypothesis is the
Ward identity for the electromagnetic current in matrix-element form: the charge operator acts on
the state as its charge `e`, and the states are covariantly normalised. -/
theorem apply_zero_eq (hF : HasFormFactor g m2 J F) {p : V} (hp : g p p = m2) (hp0 : p ≠ 0)
    {e : ℝ} (hJ : J p p = (2 * e) • p) : F 0 = e := by
  have h := (hF p p hp hp).symm.trans hJ
  rw [sub_self, map_zero, ← two_smul ℝ p, smul_smul] at h
  have := smul_left_injective ℝ hp0 h
  linarith

end HasFormFactor

/-! ### The charge radius -/

/-- The squared charge radius `⟨r²⟩ = 6 dF/dt (0)` of a form factor `F` of the invariant
momentum transfer `t`. For a form factor not differentiable at zero this is `0` by the
convention of `deriv`; the statements below carry the differentiability as a hypothesis. -/
noncomputable def chargeRadiusSq (F : ℝ → ℝ) : ℝ := 6 * deriv F 0

theorem chargeRadiusSq_def (F : ℝ → ℝ) : chargeRadiusSq F = 6 * deriv F 0 := (rfl)

/-- The squared charge radius of a form factor with slope `F'` at zero is `6 F'`. -/
theorem chargeRadiusSq_eq {F : ℝ → ℝ} {F' : ℝ} (h : HasDerivAt F F' 0) :
    chargeRadiusSq F = 6 * F' := by
  rw [chargeRadiusSq_def, h.deriv]

/-! ### The single-pole form factor -/

/-- The single-pole form factor `F(t) = e Λ² / (Λ² - t)` of charge `e` and pole position
`t = Λ²`. -/
noncomputable def singlePole (e Λsq t : ℝ) : ℝ := e * Λsq / (Λsq - t)

theorem singlePole_def (e Λsq t : ℝ) : singlePole e Λsq t = e * Λsq / (Λsq - t) := (rfl)

/-- The single-pole form factor is normalised to its charge. -/
@[simp]
theorem singlePole_zero (e : ℝ) {Λsq : ℝ} (hΛ : Λsq ≠ 0) : singlePole e Λsq 0 = e := by
  rw [singlePole_def, sub_zero, mul_div_cancel_right₀ _ hΛ]

/-- The derivative of the single-pole form factor away from the pole. -/
theorem hasDerivAt_singlePole (e : ℝ) {Λsq t : ℝ} (ht : t ≠ Λsq) :
    HasDerivAt (singlePole e Λsq) (e * Λsq / (Λsq - t) ^ 2) t := by
  have hne : Λsq - t ≠ 0 := sub_ne_zero.mpr ht.symm
  have h := ((hasDerivAt_id t).const_sub Λsq).inv hne
  have h' := h.const_mul (e * Λsq)
  convert h' using 1
  · ext s
    simp [singlePole_def, div_eq_mul_inv]
  · simp only [id]
    field_simp

/-- **The charge radius of the single-pole form factor** is `6 e / Λ²`. -/
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
  have hlim : Tendsto (fun t : ℝ => -(e * Λsq) + e * Λsq * (Λsq / (Λsq - t))) atBot
      (𝓝 (-(e * Λsq))) := by
    simpa using (tendsto_const_nhds.div_atTop hden).const_mul (e * Λsq) |>.const_add
      (-(e * Λsq))
  refine hlim.congr' ?_
  filter_upwards [hden.eventually_gt_atTop 0] with t ht
  rw [singlePole_def]
  field_simp
  ring

/-- The single-pole form factor of the positive pion, normalised to the pion's charge, has
squared charge radius `6 / Λ²`, six times the reciprocal of the squared pole mass. -/
theorem chargeRadiusSq_singlePole_piPlus {Λsq : ℝ} (hΛ : Λsq ≠ 0) :
    chargeRadiusSq (singlePole piPlus.charge Λsq) = 6 / Λsq := by
  rw [chargeRadiusSq_singlePole _ hΛ, piPlus_charge, mul_one]

end EpsilonEridani.Particles.Meson.FormFactor
