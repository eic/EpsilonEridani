/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.QFT.Factorization.Evolution.Kernel.NormalForm
public import EpsilonEridani.QFT.QCD.Basic

/-!
# The leading-order splitting kernels

The four leading-order (Gribov–Lipatov–Altarelli–Parisi) splitting kernels of QCD, written in
the normal form `r(z) + p [1 / (1 - z)]₊ + d δ(1 - z)` of
`EpsilonEridani.QFT.Factorization.Evolution.KernelForm`. They are normalised to the coupling
`α_s / (2π)`, and `P_ab` is the kernel for finding parton `a` inside parton `b`:

* `P_qq(z) = C_F [2 [1/(1-z)]₊ - (1 + z) + (3/2) δ(1-z)]`;
* `P_gq(z) = C_F (1 + (1-z)²) / z`;
* `P_qg(z) = T_F (z² + (1-z)²)` per flavour, and `2 n_f` times this in the singlet sector;
* `P_gg(z) = 2 C_A [z [1/(1-z)]₊ + (1-z)/z + z (1-z)] + ((11/6) C_A - (2/3) n_f T_F) δ(1-z)`.

The colour factors `C_F`, `C_A`, `T_F` and the number of active flavours `n_f` are the fields of
`EpsilonEridani.QFT.QCD.ColorFactors`, never numerals, so the kernels can be evaluated at any
gauge group, or at points such as `C_F = C_A = 2 n_f T_F` that are not QCD.

The familiar forms `C_F [(1 + z²)/(1 - z)]₊` of `P_qq` and `2 C_A z [1/(1-z)]₊ + …` of `P_gg`
are theorems about the pairing with test functions (`pair_pqq`, `pair_pgg`), not definitions.
The Mellin moments are computed in closed form at natural indices. At `N = 1` and `N = 2` they
give the conservation identities: quark number, `M[P_qq](1) = 0`, and momentum,
`M[P_qq](2) + M[P_gq](2) = 0` and `M[P_gg](2) + M[2 n_f P_qg](2) = 0`. These are derived from the
kernels and not imposed on them: the `n_f`-dependent delta coefficient of `P_gg` is what makes
the second momentum identity hold.

## Main definitions

* `pqq`, `pgq`, `pqg`, `pgg`: the four leading-order kernels, for given colour factors.
* `pqgSinglet`: the singlet-normalised quark-in-gluon kernel `2 n_f P_qg`.

## Main results

* `pair_pqq`: `P_qq` is the plus distribution `C_F [(1 + z²)/(1 - z)]₊`.
* `pair_pgg`: `P_gg` is `2 C_A [z [1/(1-z)]₊ + (1-z)/z + z (1-z)]` plus its delta term.
* `moment_pqq`, `moment_pgq`, `moment_pqg`, `moment_pqgSinglet`, `moment_pgg`: the moments in
  closed form, in terms of the harmonic numbers `S₁(N) = H_N`.
* `moment_pqq_one`: quark-number conservation.
* `moment_pqq_two_add_moment_pgq_two`, `moment_pgg_two_add_moment_pqgSinglet_two`: momentum
  conservation in the quark and the gluon column.

## References

* G. Altarelli and G. Parisi, *Asymptotic freedom in parton language*, Nucl. Phys. B 126 (1977)
  298.
* R. K. Ellis, W. J. Stirling and B. R. Webber, *QCD and Collider Physics*, Cambridge University
  Press (1996), §4.3.
* F. J. Yndurain, *The Theory of Quark and Gluon Interactions*, 4th ed., Springer (2006), ch. 4.
-/

public section

namespace EpsilonEridani
namespace QFT
namespace Factorization
namespace Evolution

open MeasureTheory QCD

variable (c : ColorFactors)

/-! ### The four kernels -/

/-- The leading-order quark-to-quark kernel
`P_qq(z) = C_F [2 [1/(1-z)]₊ - (1 + z) + (3/2) δ(1-z)]`. -/
noncomputable def pqq : KernelForm :=
  ⟨fun z => -c.cF * (1 + z), 2 * c.cF, 3 / 2 * c.cF⟩

/-- The leading-order gluon-in-quark kernel `P_gq(z) = C_F (1 + (1-z)²) / z`. It has no plus or
delta part; its `1 / z` singularity makes the moments converge only for `N > 1`. -/
noncomputable def pgq : KernelForm :=
  ⟨fun z => c.cF * (1 + (1 - z) ^ 2) / z, 0, 0⟩

/-- The leading-order quark-in-gluon kernel per flavour, `P_qg(z) = T_F (z² + (1-z)²)`. -/
noncomputable def pqg : KernelForm :=
  ⟨fun z => c.tF * (z ^ 2 + (1 - z) ^ 2), 0, 0⟩

/-- The singlet-normalised quark-in-gluon kernel `2 n_f P_qg`: a gluon splits into each of the
`n_f` active quark flavours and their antiquarks. -/
noncomputable def pqgSinglet : KernelForm :=
  (2 * c.nF) • pqg c

/-- The leading-order gluon-to-gluon kernel
`P_gg(z) = 2 C_A [z [1/(1-z)]₊ + (1-z)/z + z (1-z)] + ((11/6) C_A - (2/3) n_f T_F) δ(1-z)`,
in normal form through `z [1/(1-z)]₊ = [1/(1-z)]₊ - 1` (`pair_pgg`). -/
noncomputable def pgg : KernelForm :=
  ⟨fun z => 2 * c.cA * (-1 + (1 - z) / z + z * (1 - z)), 2 * c.cA,
    11 / 6 * c.cA - 2 / 3 * c.nF * c.tF⟩

@[simp]
theorem pqq_regular : (pqq c).regular = fun z => -c.cF * (1 + z) :=
  (rfl)

/-- The coefficient of `[1/(1-z)]₊` in `P_qq` is `2 C_F`: the soft singularity of quark
emission is weighted by the colour charge of the quark. -/
@[simp]
theorem pqq_plusCoeff : (pqq c).plusCoeff = 2 * c.cF :=
  (rfl)

@[simp]
theorem pqq_deltaCoeff : (pqq c).deltaCoeff = 3 / 2 * c.cF :=
  (rfl)

@[simp]
theorem pgq_regular : (pgq c).regular = fun z => c.cF * (1 + (1 - z) ^ 2) / z :=
  (rfl)

@[simp]
theorem pgq_plusCoeff : (pgq c).plusCoeff = 0 :=
  (rfl)

@[simp]
theorem pgq_deltaCoeff : (pgq c).deltaCoeff = 0 :=
  (rfl)

@[simp]
theorem pqg_regular : (pqg c).regular = fun z => c.tF * (z ^ 2 + (1 - z) ^ 2) :=
  (rfl)

@[simp]
theorem pqg_plusCoeff : (pqg c).plusCoeff = 0 :=
  (rfl)

@[simp]
theorem pqg_deltaCoeff : (pqg c).deltaCoeff = 0 :=
  (rfl)

/-- The singlet-normalised quark-in-gluon kernel is `2 n_f` times the per-flavour one. Conflating
the two breaks the gluon-column momentum identity by exactly this factor. -/
theorem pqgSinglet_def : pqgSinglet c = (2 * c.nF) • pqg c :=
  (rfl)

@[simp]
theorem pgg_regular :
    (pgg c).regular = fun z => 2 * c.cA * (-1 + (1 - z) / z + z * (1 - z)) :=
  (rfl)

/-- The coefficient of `[1/(1-z)]₊` in `P_gg` is `2 C_A`: the soft singularity of gluon
emission is weighted by the colour charge of the gluon. -/
@[simp]
theorem pgg_plusCoeff : (pgg c).plusCoeff = 2 * c.cA :=
  (rfl)

@[simp]
theorem pgg_deltaCoeff : (pgg c).deltaCoeff = 11 / 6 * c.cA - 2 / 3 * c.nF * c.tF :=
  (rfl)

/-! ### The unregularised forms -/

/-- **`P_qq` is `C_F [(1 + z²)/(1 - z)]₊`.** The normal form of `P_qq` pairs with a test
function `φ` as the plus functional of `C_F (1 + z²)/(1 - z)`, for every `φ` integrable on
`[0, 1]` whose pairing with `[1/(1-z)]₊` converges. -/
theorem pair_pqq {φ : ℝ → ℝ} (hφ : IntervalIntegrable φ volume 0 1)
    (hφ₁ : IntervalIntegrable (fun z => (1 - z)⁻¹ * (φ z - φ 1)) volume 0 1) :
    (pqq c).pair φ = c.cF * plusFunctional (fun z => (1 + z ^ 2) / (1 - z)) φ := by
  have hlin : IntervalIntegrable (fun z => (1 + z) * φ z) volume 0 1 :=
    hφ.continuousOn_mul (by fun_prop)
  have hconst : IntervalIntegrable (fun z : ℝ => φ 1 * (1 + z)) volume 0 1 :=
    (by fun_prop : Continuous fun z : ℝ => φ 1 * (1 + z)).intervalIntegrable 0 1
  -- Off `z = 1`, `(1 + z²)/(1 - z) = 2/(1 - z) - (1 + z)`.
  have hsplit : (∫ z in (0 : ℝ)..1, (1 + z ^ 2) / (1 - z) * (φ z - φ 1)) =
      ∫ z in (0 : ℝ)..1,
        (2 * ((1 - z)⁻¹ * (φ z - φ 1)) - (1 + z) * φ z + φ 1 * (1 + z)) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [Measure.ae_ne volume (1 : ℝ)] with z hz _
    have h1z : (1 : ℝ) - z ≠ 0 := sub_ne_zero.2 (Ne.symm hz)
    field_simp
    ring
  have h32 : ∫ z in (0 : ℝ)..1, (1 + z) = 3 / 2 := by
    rw [intervalIntegral.integral_add (intervalIntegrable_const (c := (1 : ℝ)))
      intervalIntegral.intervalIntegrable_id]
    norm_num
  rw [plusFunctional_def, hsplit, intervalIntegral.integral_add ((hφ₁.const_mul 2).sub hlin) hconst,
    intervalIntegral.integral_sub (hφ₁.const_mul 2) hlin]
  simp only [KernelForm.pair_def, pqq_regular, pqq_plusCoeff, pqq_deltaCoeff, plusOneMinus_def,
    plusFunctional_def, neg_mul, mul_assoc, intervalIntegral.integral_neg,
    intervalIntegral.integral_const_mul, h32]
  ring

/-- **`P_gg` in its familiar form.** The normal form of `P_gg` pairs with a test function `φ` as
`2 C_A [z [1/(1-z)]₊ + (1-z)/z + z (1-z)] + ((11/6) C_A - (2/3) n_f T_F) δ(1-z)`, for every `φ`
integrable on `[0, 1]` against which the regular part converges and whose pairing with
`[1/(1-z)]₊` converges. -/
theorem pair_pgg {φ : ℝ → ℝ} (hφ : IntervalIntegrable φ volume 0 1)
    (hφ₁ : IntervalIntegrable (fun z => (1 - z)⁻¹ * (φ z - φ 1)) volume 0 1)
    (hreg : IntervalIntegrable (fun z => ((1 - z) / z + z * (1 - z)) * φ z) volume 0 1) :
    (pgg c).pair φ =
      2 * c.cA * (plusOneMinus (fun z => z * φ z) +
          ∫ z in (0 : ℝ)..1, ((1 - z) / z + z * (1 - z)) * φ z) +
        (11 / 6 * c.cA - 2 / 3 * c.nF * c.tF) * φ 1 := by
  -- `z [1/(1-z)]₊ = [1/(1-z)]₊ - 1`, the multiplication identity with `g z = z`.
  have hneg : (fun z => (1 - z)⁻¹ * (z - 1) * φ z) =ᵐ[volume] fun z => -φ z := by
    filter_upwards [Measure.ae_ne volume (1 : ℝ)] with z hz
    have h1z : (1 : ℝ) - z ≠ 0 := sub_ne_zero.2 (Ne.symm hz)
    field_simp
    ring
  have hmul : plusOneMinus (fun z => z * φ z) = plusOneMinus φ - ∫ z in (0 : ℝ)..1, φ z := by
    rw [plusOneMinus_mul (g := fun z => z) hφ₁ (hφ.neg.congr_ae (ae_restrict_of_ae hneg.symm)),
      intervalIntegral.integral_congr_ae (hneg.mono fun z hz _ => hz),
      intervalIntegral.integral_neg]
    ring
  have hsplit : (fun z => 2 * c.cA * (-1 + (1 - z) / z + z * (1 - z)) * φ z) =
      fun z => 2 * c.cA * (-φ z + ((1 - z) / z + z * (1 - z)) * φ z) := by
    funext z
    ring
  simp only [hmul, KernelForm.pair_def, pgg_regular, pgg_plusCoeff, pgg_deltaCoeff, hsplit,
    intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_add (f := fun z => -φ z) hφ.neg hreg, intervalIntegral.integral_neg]
  ring

/-! ### Moments in closed form -/

/-- The quark-to-quark moment `γ_qq(N) = C_F [3/2 - 2 S₁(N) + 1/(N (N+1))]`, for `N ≥ 1`. -/
theorem moment_pqq {N : ℕ} (hN : N ≠ 0) :
    (pqq c).moment N = c.cF * (3 / 2 - 2 * harmonic N + 1 / (N * (N + 1))) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN
  have hint : ∫ z in (0 : ℝ)..1, -c.cF * (1 + z) * z ^ n =
      -c.cF * (1 / (n + 1) + 1 / (n + 2)) := by
    have hi (k : ℕ) : IntervalIntegrable (fun z : ℝ => -c.cF * z ^ k) volume 0 1 :=
      (intervalIntegral.intervalIntegrable_pow k).const_mul _
    rw [show (fun z : ℝ => -c.cF * (1 + z) * z ^ n) =
        fun z => -c.cF * z ^ n + -c.cF * z ^ (n + 1) by funext z; ring,
      intervalIntegral.integral_add (hi n) (hi (n + 1))]
    simp only [intervalIntegral.integral_const_mul, integral_pow]
    push_cast
    ring
  rw [Nat.succ_eq_add_one, Nat.cast_add_one, KernelForm.moment_natCast_add_one,
    KernelForm.pair_pow]
  simp only [pqq_regular, hint, pqq_plusCoeff, pqq_deltaCoeff, harmonic_succ]
  push_cast
  field_simp
  ring

/-- The gluon-in-quark moment `γ_gq(N) = C_F (N² + N + 2) / ((N - 1) N (N + 1))`, for `N ≥ 2`.
At `N = 1` the integral defining the moment diverges: this is the pole of `γ_gq` at `N = 1`. -/
theorem moment_pgq {N : ℕ} (hN : 2 ≤ N) :
    (pgq c).moment N = c.cF * (N ^ 2 + N + 2) / ((N - 1) * N * (N + 1)) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hN
  have hint : ∫ z in (0 : ℝ)..1, c.cF * (1 + (1 - z) ^ 2) / z * z ^ (n + 1) =
      c.cF * (2 / (n + 1) - 2 / (n + 2) + 1 / (n + 3)) := by
    have hi (a : ℝ) (k : ℕ) : IntervalIntegrable (fun z : ℝ => a * z ^ k) volume 0 1 :=
      (intervalIntegral.intervalIntegrable_pow k).const_mul a
    rw [intervalIntegral.integral_congr_ae (g := fun z =>
        2 * c.cF * z ^ n + -(2 * c.cF) * z ^ (n + 1) + c.cF * z ^ (n + 2)) ?_,
      intervalIntegral.integral_add ((hi _ n).add (hi _ (n + 1))) (hi _ (n + 2)),
      intervalIntegral.integral_add (hi _ n) (hi _ (n + 1))]
    · simp only [intervalIntegral.integral_const_mul, integral_pow]
      push_cast
      ring
    · filter_upwards [Measure.ae_ne volume (0 : ℝ)] with z hz _
      field_simp
      ring
  rw [show ((2 + n : ℕ) : ℝ) = ((n + 1 : ℕ) : ℝ) + 1 by push_cast; ring,
    KernelForm.moment_natCast_add_one, KernelForm.pair_pow]
  simp only [pgq_regular, hint, pgq_plusCoeff, pgq_deltaCoeff]
  push_cast
  field_simp
  ring

/-- The per-flavour quark-in-gluon moment `T_F (N² + N + 2) / (N (N + 1) (N + 2))`, for
`N ≥ 1`. -/
theorem moment_pqg {N : ℕ} (hN : N ≠ 0) :
    (pqg c).moment N = c.tF * (N ^ 2 + N + 2) / (N * (N + 1) * (N + 2)) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN
  have hint : ∫ z in (0 : ℝ)..1, c.tF * (z ^ 2 + (1 - z) ^ 2) * z ^ n =
      c.tF * (1 / (n + 1) - 2 / (n + 2) + 2 / (n + 3)) := by
    have hi (a : ℝ) (k : ℕ) : IntervalIntegrable (fun z : ℝ => a * z ^ k) volume 0 1 :=
      (intervalIntegral.intervalIntegrable_pow k).const_mul a
    rw [show (fun z : ℝ => c.tF * (z ^ 2 + (1 - z) ^ 2) * z ^ n) =
        fun z => c.tF * z ^ n + -(2 * c.tF) * z ^ (n + 1) + 2 * c.tF * z ^ (n + 2) by
          funext z; ring,
      intervalIntegral.integral_add ((hi _ n).add (hi _ (n + 1))) (hi _ (n + 2)),
      intervalIntegral.integral_add (hi _ n) (hi _ (n + 1))]
    simp only [intervalIntegral.integral_const_mul, integral_pow]
    push_cast
    ring
  rw [Nat.succ_eq_add_one, Nat.cast_add_one, KernelForm.moment_natCast_add_one,
    KernelForm.pair_pow]
  simp only [pqg_regular, hint, pqg_plusCoeff, pqg_deltaCoeff]
  field_simp
  ring

/-- The singlet quark-in-gluon moment `γ_qg(N) = 2 n_f T_F (N² + N + 2) / (N (N + 1) (N + 2))`,
for `N ≥ 1`. -/
theorem moment_pqgSinglet {N : ℕ} (hN : N ≠ 0) :
    (pqgSinglet c).moment N = 2 * c.nF * c.tF * (N ^ 2 + N + 2) / (N * (N + 1) * (N + 2)) := by
  rw [pqgSinglet_def, KernelForm.moment_smul, moment_pqg c hN]
  ring

/-- The gluon-to-gluon moment
`γ_gg(N) = 2 C_A [-S₁(N) + 1/(N-1) - 1/N + 1/(N+1) - 1/(N+2)] + (11/6) C_A - (2/3) n_f T_F`,
for `N ≥ 2`. -/
theorem moment_pgg {N : ℕ} (hN : 2 ≤ N) :
    (pgg c).moment N =
      2 * c.cA * (-harmonic N + 1 / (N - 1) - 1 / N + 1 / (N + 1) - 1 / (N + 2)) +
        11 / 6 * c.cA - 2 / 3 * c.nF * c.tF := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hN
  have hint : ∫ z in (0 : ℝ)..1, 2 * c.cA * (-1 + (1 - z) / z + z * (1 - z)) * z ^ (n + 1) =
      2 * c.cA * (1 / (n + 1) - 2 / (n + 2) + 1 / (n + 3) - 1 / (n + 4)) := by
    have hi (a : ℝ) (k : ℕ) : IntervalIntegrable (fun z : ℝ => a * z ^ k) volume 0 1 :=
      (intervalIntegral.intervalIntegrable_pow k).const_mul a
    rw [intervalIntegral.integral_congr_ae (g := fun z =>
        2 * c.cA * z ^ n + -(4 * c.cA) * z ^ (n + 1) + 2 * c.cA * z ^ (n + 2) +
          -(2 * c.cA) * z ^ (n + 3)) ?_,
      intervalIntegral.integral_add (((hi _ n).add (hi _ (n + 1))).add (hi _ (n + 2)))
        (hi _ (n + 3)),
      intervalIntegral.integral_add ((hi _ n).add (hi _ (n + 1))) (hi _ (n + 2)),
      intervalIntegral.integral_add (hi _ n) (hi _ (n + 1))]
    · simp only [intervalIntegral.integral_const_mul, integral_pow]
      push_cast
      ring
    · filter_upwards [Measure.ae_ne volume (0 : ℝ)] with z hz _
      field_simp
      ring
  rw [show ((2 + n : ℕ) : ℝ) = ((n + 1 : ℕ) : ℝ) + 1 by push_cast; ring,
    KernelForm.moment_natCast_add_one, KernelForm.pair_pow, show 2 + n = n + 1 + 1 by omega]
  simp only [pgg_regular, hint, pgg_plusCoeff, pgg_deltaCoeff, harmonic_succ (n + 1)]
  push_cast
  field_simp
  ring

/-! ### Conservation -/

/-- **Quark-number conservation.** The quark-number moment of the non-singlet kernel vanishes,
`M[P_qq](1) = 0`, so evolution preserves the number of quarks minus antiquarks of each
flavour. -/
theorem moment_pqq_one : (pqq c).moment 1 = 0 := by
  have h := moment_pqq c one_ne_zero
  norm_num [harmonic, Finset.sum_range_succ] at h
  exact h

/-- The momentum moment of the quark-to-quark kernel, `M[P_qq](2) = -(4/3) C_F`. -/
theorem moment_pqq_two : (pqq c).moment 2 = -(4 / 3 * c.cF) := by
  have h := moment_pqq c two_ne_zero
  norm_num [harmonic, Finset.sum_range_succ] at h
  rw [h]
  ring

/-- The momentum moment of the gluon-in-quark kernel, `M[P_gq](2) = (4/3) C_F`. -/
theorem moment_pgq_two : (pgq c).moment 2 = 4 / 3 * c.cF := by
  have h := moment_pgq c le_rfl
  norm_num at h
  rw [h]
  ring

/-- The momentum moment of the singlet quark-in-gluon kernel, `M[2 n_f P_qg](2) = (2/3) n_f T_F`.
-/
theorem moment_pqgSinglet_two : (pqgSinglet c).moment 2 = 2 / 3 * c.nF * c.tF := by
  have h := moment_pqgSinglet c two_ne_zero
  norm_num at h
  rw [h]
  ring

/-- The momentum moment of the gluon-to-gluon kernel, `M[P_gg](2) = -(2/3) n_f T_F`: the
`C_A` terms cancel between the regular, plus and delta parts. -/
theorem moment_pgg_two : (pgg c).moment 2 = -(2 / 3 * c.nF * c.tF) := by
  have h := moment_pgg c le_rfl
  norm_num [harmonic, Finset.sum_range_succ] at h
  rw [h]
  ring

/-- **Momentum conservation in the quark column.** `M[P_qq](2) + M[P_gq](2) = 0`: the momentum
a quark loses to radiated gluons is the momentum they carry. -/
theorem moment_pqq_two_add_moment_pgq_two : (pqq c).moment 2 + (pgq c).moment 2 = 0 := by
  rw [moment_pqq_two, moment_pgq_two]
  ring

/-- **Momentum conservation in the gluon column.** `M[P_gg](2) + M[2 n_f P_qg](2) = 0`: the
momentum a gluon loses to quark-antiquark pairs is the momentum they carry. -/
theorem moment_pgg_two_add_moment_pqgSinglet_two :
    (pgg c).moment 2 + (pqgSinglet c).moment 2 = 0 := by
  rw [moment_pgg_two, moment_pqgSinglet_two]
  ring

end Evolution
end Factorization
end QFT
end EpsilonEridani
