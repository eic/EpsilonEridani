/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.RingTheory.Polynomial.Basic
public import TauCeti.Probability.Moments.VanishingMoments

/-!
# The moment problem on a compact interval

An integrable function on a compact interval `[a, b]` is determined almost everywhere by the
numbers `∫_a^b x^n f(x) dx`, `n ∈ ℕ`: this is the uniqueness half of the Hausdorff moment
problem, and `ae_eq_of_forall_setIntegral_Icc_pow_mul_eq` is the form proved here. The analytic
work is done by TauCeti's `TauCeti.ae_eq_zero_of_forall_moment_eq_zero`, which kills a function
with vanishing moments against an arbitrary measure on `ℝ` provided some exponential weight
`e^{a|x|}` keeps it integrable. On a compact interval that weight is free: a continuous factor
against a function integrable on a compact set stays integrable, so the only hypothesis left
here is integrability on `[a, b]`.

Determinacy is sharp in the number of moments used: **no finite set of moments determines the
function.** For every `N`, the polynomials of degree at most `N + 1` annihilated by the moments
of order `0, …, N` form a nonzero subspace of the `(N + 2)`-dimensional space
`Polynomial.degreeLT ℝ (N + 2)`, namely the kernel there of the moment map
`polynomialMomentsIcc a b N`, because `N + 2` coefficients have only `N + 1` moments to match
(`ker_polynomialMomentsIcc_inf_degreeLT_ne_bot`). On a nondegenerate interval each nonzero member
is a counterexample that is not almost everywhere zero
(`exists_polynomial_ne_zero_forall_le_setIntegral_Icc_pow_mul_eq_zero`).

The two statements together are what separates a moment *constraint* from moment *knowledge*: a
function on a bounded interval is determined by all of its moments and by no finite part of
them.

## Main results

- `ae_eq_zero_of_forall_setIntegral_Icc_pow_mul_eq_zero` and
  `ae_eq_of_forall_setIntegral_Icc_pow_mul_eq`: **moment determinacy.**
- `polynomialMomentsIcc`: the moments of order `0, …, N` of a polynomial, as a linear map.
- `ker_polynomialMomentsIcc_inf_degreeLT_ne_bot`: the counterexamples of degree at most `N + 1`
  form a nonzero subspace.
- `exists_polynomial_ne_zero_forall_le_setIntegral_Icc_pow_mul_eq_zero`: **failure of determinacy
  from finitely many moments.**
- `not_eval_ae_eq_zero_of_ne_zero`: a nonzero polynomial is not almost everywhere zero on a
  nondegenerate interval.

## References

* N. I. Akhiezer, *The Classical Moment Problem*, Hafner (1965), Chapter 2, for the Hausdorff
  moment problem and the role of polynomial density, which is what the TauCeti engine supplies.

Nothing in this file is physics-specific.
-/

public section

noncomputable section

open MeasureTheory Set

namespace EpsilonEridani

variable {a b : ℝ} {f g : ℝ → ℝ}

/-- Every moment of a function integrable on a compact interval is finite: `x ^ n * f x` is
integrable on `[a, b]` whenever `f` is, because `x ^ n` is continuous. -/
theorem integrableOn_Icc_pow_mul (hf : IntegrableOn f (Icc a b)) (n : ℕ) :
    IntegrableOn (fun x => x ^ n * f x) (Icc a b) :=
  IntegrableOn.continuousOn_mul (by fun_prop) hf isCompact_Icc

/-- **Determinacy of the Hausdorff moment problem.** An integrable function on a compact
interval all of whose moments vanish is almost everywhere zero.

This is `TauCeti.ae_eq_zero_of_forall_moment_eq_zero` at `volume.restrict (Icc a b)`: the
exponential weight it asks for costs nothing on a compact interval, since multiplying an
integrable function there by a continuous one preserves integrability. -/
theorem ae_eq_zero_of_forall_setIntegral_Icc_pow_mul_eq_zero (hf : IntegrableOn f (Icc a b))
    (hmom : ∀ n : ℕ, ∫ x in Icc a b, x ^ n * f x = 0) :
    f =ᵐ[volume.restrict (Icc a b)] 0 :=
  TauCeti.ae_eq_zero_of_forall_moment_eq_zero f
    ⟨1, one_pos, IntegrableOn.continuousOn_mul (by fun_prop) hf isCompact_Icc⟩ hmom

/-- **An integrable function on a compact interval is determined by its moments.** -/
theorem ae_eq_of_forall_setIntegral_Icc_pow_mul_eq (hf : IntegrableOn f (Icc a b))
    (hg : IntegrableOn g (Icc a b))
    (hmom : ∀ n : ℕ, ∫ x in Icc a b, x ^ n * f x = ∫ x in Icc a b, x ^ n * g x) :
    f =ᵐ[volume.restrict (Icc a b)] g := by
  have hdiff : (fun x => f x - g x) =ᵐ[volume.restrict (Icc a b)] 0 := by
    refine ae_eq_zero_of_forall_setIntegral_Icc_pow_mul_eq_zero (hf.sub hg) fun n => ?_
    simp_rw [mul_sub]
    rw [integral_sub (integrableOn_Icc_pow_mul hf n) (integrableOn_Icc_pow_mul hg n), hmom n,
      sub_self]
  filter_upwards [hdiff] with x hx using by simpa [sub_eq_zero] using hx

/-! ### Failure of determinacy from finitely many moments -/

/-- The moments of order `0, …, N` of a polynomial on `[a, b]`, as a linear map to `ℝ^(N + 1)`.
Its kernel consists of the polynomials that these `N + 1` moments cannot tell apart from `0`. -/
def polynomialMomentsIcc (a b : ℝ) (N : ℕ) : Polynomial ℝ →ₗ[ℝ] Fin (N + 1) → ℝ where
  toFun p n := ∫ x in Icc a b, x ^ (n : ℕ) * p.eval x
  map_add' p q := by
    funext n
    simp only [Polynomial.eval_add, mul_add, Pi.add_apply]
    exact integral_add (integrableOn_Icc_pow_mul p.continuous.integrableOn_Icc n)
      (integrableOn_Icc_pow_mul q.continuous.integrableOn_Icc n)
  map_smul' c p := by
    funext n
    simp only [Polynomial.eval_smul, smul_eq_mul, RingHom.id_apply, Pi.smul_apply,
      ← integral_const_mul, mul_left_comm]

/-- Unfolding lemma for `polynomialMomentsIcc`, whose body is not exposed. -/
@[simp]
theorem polynomialMomentsIcc_apply (N : ℕ) (p : Polynomial ℝ) (n : Fin (N + 1)) :
    polynomialMomentsIcc a b N p n = ∫ x in Icc a b, x ^ (n : ℕ) * p.eval x :=
  (rfl)

/-- **The counterexamples to determinacy from `N + 1` moments form a nonzero subspace.** The
polynomials of degree at most `N + 1` whose moments of order `0, …, N` on `[a, b]` all vanish are
the kernel of `polynomialMomentsIcc a b N` inside the `(N + 2)`-dimensional space
`Polynomial.degreeLT ℝ (N + 2)`, and that kernel is nonzero: `N + 2` coefficients are mapped to
only `N + 1` moments. -/
theorem ker_polynomialMomentsIcc_inf_degreeLT_ne_bot (N : ℕ) :
    LinearMap.ker (polynomialMomentsIcc a b N) ⊓ Polynomial.degreeLT ℝ (N + 2) ≠ ⊥ := by
  let e := Polynomial.degreeLTEquiv ℝ (N + 2)
  have : FiniteDimensional ℝ (Polynomial.degreeLT ℝ (N + 2)) := e.symm.finiteDimensional
  have hker : LinearMap.ker
      ((polynomialMomentsIcc a b N).comp (Polynomial.degreeLT ℝ (N + 2)).subtype) ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (by simp [e.finrank_eq])
  obtain ⟨q, hq, hq0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  exact (Submodule.ne_bot_iff _).mpr ⟨q, ⟨hq, q.2⟩, fun h => hq0 (Subtype.ext h)⟩

/-- A nonzero polynomial is not almost everywhere zero on a nondegenerate interval: it has
finitely many roots, a null set, while `[a, b]` has positive length. -/
theorem not_eval_ae_eq_zero_of_ne_zero (hab : a < b) {p : Polynomial ℝ} (hp : p ≠ 0) :
    ¬ (fun x => p.eval x) =ᵐ[volume.restrict (Icc a b)] 0 := by
  intro hp0
  have : (ae (volume.restrict (Icc a b))).NeBot :=
    ae_neBot.mpr (by simp [Measure.restrict_eq_zero, Real.volume_Icc, hab])
  have hroots : ∀ᵐ x ∂volume.restrict (Icc a b), p.eval x ≠ 0 := by
    rw [ae_iff]
    simpa using (Polynomial.finite_setOfPred_isRoot hp).measure_zero (volume.restrict (Icc a b))
  obtain ⟨x, hx, hxne⟩ := (hp0.and hroots).exists
  exact hxne hx

/-- **No finite set of moments determines a function on `[a, b]`.** For every `N` there is a
nonzero polynomial of degree at most `N + 1`, *not* almost everywhere zero on `[a, b]`, all of
whose moments of order `0, …, N` on `[a, b]` vanish. Negating the almost-everywhere relation is
what makes this sharp: the counterexample is not a null perturbation of `0`, so it is one that
`ae_eq_of_forall_setIntegral_Icc_pow_mul_eq` would have ruled out had all the moments been
known.

Any nonzero element of the subspace of `ker_polynomialMomentsIcc_inf_degreeLT_ne_bot` will do. -/
theorem exists_polynomial_ne_zero_forall_le_setIntegral_Icc_pow_mul_eq_zero (hab : a < b)
    (N : ℕ) :
    ∃ p : Polynomial ℝ, p ≠ 0 ∧ p.natDegree ≤ N + 1 ∧
      ¬ (fun x => p.eval x) =ᵐ[volume.restrict (Icc a b)] 0 ∧
      ∀ n ≤ N, ∫ x in Icc a b, x ^ n * p.eval x = 0 := by
  obtain ⟨p, ⟨hker, hdeg⟩, hp⟩ :=
    (Submodule.ne_bot_iff _).mp
      (ker_polynomialMomentsIcc_inf_degreeLT_ne_bot (a := a) (b := b) N)
  refine ⟨p, hp, ?_, not_eval_ae_eq_zero_of_ne_zero hab hp, fun n hn => ?_⟩
  · rw [SetLike.mem_coe, Polynomial.mem_degreeLT,
      ← Polynomial.natDegree_lt_iff_degree_lt hp] at hdeg
    omega
  · simpa using congrFun (LinearMap.mem_ker.mp hker) ⟨n, Nat.lt_succ_of_le hn⟩

end EpsilonEridani
