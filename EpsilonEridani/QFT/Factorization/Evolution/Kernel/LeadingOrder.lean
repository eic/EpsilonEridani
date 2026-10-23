/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.Mathematics.Calculus.IntegralRpow
public import EpsilonEridani.Mathematics.HarmonicSum.Basic
public import EpsilonEridani.QFT.Factorization.Evolution.Kernel.NormalForm
public import EpsilonEridani.QFT.QCD.Basic

/-!
# The leading-order splitting kernels

The four leading-order (Dokshitzer–Gribov–Lipatov–Altarelli–Parisi) splitting kernels of QCD,
written in the normal form `r(z) + p [1 / (1 - z)]₊ + d δ(1 - z)` of
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
The Mellin moments are computed in closed form: at every real index in the half-line of
convergence for the three kernels whose moments are rational functions of `N`, and at natural
indices for `P_qq` and `P_gg`, whose moments involve the harmonic numbers. At `N = 1` and `N = 2`
they give the conservation identities: quark number, `M[P_qq](1) = 0`, and momentum,
`M[P_qq](2) + M[P_gq](2) = 0` and `M[P_gg](2) + M[2 n_f P_qg](2) = 0`. These are derived from the
kernels and not imposed on them: the `n_f`-dependent delta coefficient of `P_gg`, which is half
the one-loop beta-function coefficient `β₀` (`pgg_deltaCoeff_eq_beta0`), is what makes the second
momentum identity hold.

## Main definitions

* `pqq`, `pgq`, `pqg`, `pgg`: the four leading-order kernels, for given colour factors.
* `pqgSinglet`: the singlet-normalised quark-in-gluon kernel `2 n_f P_qg`.

## Main results

* `pair_pqq`: `P_qq` is the plus distribution `C_F [(1 + z²)/(1 - z)]₊`.
* `pair_pgg`: `P_gg` is `2 C_A [z [1/(1-z)]₊ + (1-z)/z + z (1-z)]` plus its delta term.
* `moment_pgq`, `moment_pqg`, `moment_pqgSinglet`: the moments in closed form at every real
  index `N` for which the integral converges, as rational functions of `N`.
* `moment_pqq`, `moment_pgg`: the moments in closed form at natural indices, in terms of the
  harmonic numbers `S₁(N) = H_N`.
* `pgg_deltaCoeff_eq_beta0`: the delta coefficient of `P_gg` is `β₀ / 2`.
* `moment_pqq_one`: quark-number conservation.
* `moment_pqq_two_add_moment_pgq_two`, `moment_pgg_two_add_moment_pqgSinglet_two`: momentum
  conservation in the quark and the gluon column.

## References

* V. N. Gribov and L. N. Lipatov, *Deep inelastic e p scattering in perturbation theory*,
  Sov. J. Nucl. Phys. 15 (1972) 438.
* G. Altarelli and G. Parisi, *Asymptotic freedom in parton language*, Nucl. Phys. B 126 (1977)
  298.
* Yu. L. Dokshitzer, *Calculation of the structure functions for deep inelastic scattering and
  e⁺e⁻ annihilation by perturbation theory in quantum chromodynamics*, Sov. Phys. JETP 46 (1977)
  641.
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
delta part. Its `1 / z` singularity makes the integral defining the moments converge only for
`N > 1`; at smaller `N` the moment takes the junk value of the Bochner integral. -/
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
in normal form through `z [1/(1-z)]₊ = [1/(1-z)]₊ - 1` (`pair_pgg`). The `(1-z)/z` term of its
regular part makes the integral defining the moments converge only for `N > 1`, as for `P_gq`;
at smaller `N` the moment takes the junk value of the Bochner integral. -/
noncomputable def pgg : KernelForm :=
  ⟨fun z => 2 * c.cA * (-1 + (1 - z) / z + z * (1 - z)), 2 * c.cA,
    11 / 6 * c.cA - 2 / 3 * c.nF * c.tF⟩

@[simp]
theorem pqq_regular : (pqq c).regular = fun z => -c.cF * (1 + z) :=
  (rfl)

/-- The coefficient of `[1/(1-z)]₊` in `P_qq` is `2 C_F`: the soft singularity of gluon
emission off a quark is weighted by the colour charge of the quark. -/
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

/-- The regular part of the singlet-normalised `P_qg` is `2 n_f T_F (z² + (1-z)²)`. -/
@[simp]
theorem pqgSinglet_regular :
    (pqgSinglet c).regular = fun z => 2 * c.nF * c.tF * (z ^ 2 + (1 - z) ^ 2) := by
  funext z
  simp only [pqgSinglet_def, KernelForm.smul_regular, pqg_regular]
  ring

/-- The singlet-normalised `P_qg` has no plus part: quark-pair emission has no soft `z → 1`
singularity. -/
@[simp]
theorem pqgSinglet_plusCoeff : (pqgSinglet c).plusCoeff = 0 := by
  simp [pqgSinglet_def]

/-- The singlet-normalised `P_qg` has no delta part. -/
@[simp]
theorem pqgSinglet_deltaCoeff : (pqgSinglet c).deltaCoeff = 0 := by
  simp [pqgSinglet_def]

@[simp]
theorem pgg_regular :
    (pgg c).regular = fun z => 2 * c.cA * (-1 + (1 - z) / z + z * (1 - z)) :=
  (rfl)

/-- The coefficient of `[1/(1-z)]₊` in `P_gg` is `2 C_A`: the soft singularity of gluon
emission off a gluon is weighted by the colour charge of the gluon. -/
@[simp]
theorem pgg_plusCoeff : (pgg c).plusCoeff = 2 * c.cA :=
  (rfl)

@[simp]
theorem pgg_deltaCoeff : (pgg c).deltaCoeff = 11 / 6 * c.cA - 2 / 3 * c.nF * c.tF :=
  (rfl)

/-- The coefficient of `δ(1-z)` in `P_gg` is half the one-loop beta-function coefficient,
`β₀ / 2 = (11/6) C_A - (2/3) n_f T_F`. This is what makes the gluon-column momentum identity
`moment_pgg_two_add_moment_pqgSinglet_two` hold: the virtual term of `P_gg` carries the same
gluon self-energy that drives the running of `α_s`. -/
theorem pgg_deltaCoeff_eq_beta0 : (pgg c).deltaCoeff = beta0 c / 2 := by
  rw [pgg_deltaCoeff, beta0]
  ring

/-! ### The unregularised forms -/

/-- **`P_qq` is `C_F [(1 + z²)/(1 - z)]₊`.** The normal form of `P_qq` pairs with a test
function `φ` as the plus functional of `C_F (1 + z²)/(1 - z)`, for every `φ` whose pairing with
`[1/(1-z)]₊` converges; such a `φ` is integrable on `[0, 1]` by
`EpsilonEridani.intervalIntegrable_of_plusOneMinus_integrand`. -/
theorem pair_pqq {φ : ℝ → ℝ}
    (hφ₁ : IntervalIntegrable (fun z => (1 - z)⁻¹ * (φ z - φ 1)) volume 0 1) :
    (pqq c).pair φ = c.cF * plusFunctional (fun z => (1 + z ^ 2) / (1 - z)) φ := by
  have hφ := intervalIntegrable_of_plusOneMinus_integrand hφ₁
  have hlin : IntervalIntegrable (fun z => (1 + z) * φ z) volume 0 1 :=
    hφ.continuousOn_mul (by fun_prop)
  have hconst : IntervalIntegrable (fun z : ℝ => φ 1 * (1 + z)) volume 0 1 :=
    (by fun_prop : Continuous fun z : ℝ => φ 1 * (1 + z)).intervalIntegrable 0 1
  -- Off `z = 1`, `(1 + z²)/(1 - z) = 2/(1 - z) - (1 + z)`.
  have hK : (fun z : ℝ => (1 + z ^ 2) / (1 - z)) =ᵐ[volume.restrict (Set.Ioc 0 1)]
      fun z => 2 * (1 - z)⁻¹ + -(1 + z) := by
    filter_upwards [ae_restrict_of_ae (Measure.ae_ne volume (1 : ℝ))] with z hz
    have h1z : (1 : ℝ) - z ≠ 0 := sub_ne_zero.2 (Ne.symm hz)
    field_simp
    ring
  have hsing : IntervalIntegrable (fun z => 2 * (1 - z)⁻¹ * (φ z - φ 1)) volume 0 1 := by
    simpa only [mul_assoc] using hφ₁.const_mul 2
  have hreg : IntervalIntegrable (fun z => -(1 + z) * (φ z - φ 1)) volume 0 1 :=
    (hconst.sub hlin).congr fun z _ => by ring
  have h32 : ∫ z in (0 : ℝ)..1, (1 + z) = 3 / 2 := by
    rw [intervalIntegral.integral_add (intervalIntegrable_const (c := (1 : ℝ)))
      intervalIntegral.intervalIntegrable_id]
    norm_num
  have hKφ : IntervalIntegrable (fun z => -(1 + z) * φ z) volume 0 1 :=
    (hlin.const_mul (-1)).congr fun z _ => by ring
  have hK : IntervalIntegrable (fun z : ℝ => -(1 + z)) volume 0 1 :=
    (by fun_prop : Continuous fun z : ℝ => -(1 + z)).intervalIntegrable 0 1
  have hplus : plusFunctional (fun z => -(1 + z)) φ =
      φ 1 * (3 / 2) - ∫ z in (0 : ℝ)..1, (1 + z) * φ z := by
    rw [plusFunctional_of_intervalIntegrable hKφ hK]
    simp only [neg_mul, intervalIntegral.integral_neg, h32]
    ring
  rw [plusFunctional_congr_ae_left φ hK, plusFunctional_add_left hsing hreg,
    plusFunctional_const_mul_left, hplus]
  simp only [KernelForm.pair_def, pqq_regular, pqq_plusCoeff, pqq_deltaCoeff, plusOneMinus_def,
    neg_mul, mul_assoc, intervalIntegral.integral_neg, intervalIntegral.integral_const_mul]
  ring

/-- **`P_gg` in its familiar form.** The normal form of `P_gg` pairs with a test function `φ` as
`2 C_A [z [1/(1-z)]₊ + (1-z)/z + z (1-z)] + ((11/6) C_A - (2/3) n_f T_F) δ(1-z)`, for every `φ`
whose pairing with `[1/(1-z)]₊` converges and against which the regular part converges. -/
theorem pair_pgg {φ : ℝ → ℝ}
    (hφ₁ : IntervalIntegrable (fun z => (1 - z)⁻¹ * (φ z - φ 1)) volume 0 1)
    (hreg : IntervalIntegrable (fun z => ((1 - z) / z + z * (1 - z)) * φ z) volume 0 1) :
    (pgg c).pair φ =
      2 * c.cA * (plusOneMinus (fun z => z * φ z) +
          ∫ z in (0 : ℝ)..1, ((1 - z) / z + z * (1 - z)) * φ z) +
        (11 / 6 * c.cA - 2 / 3 * c.nF * c.tF) * φ 1 := by
  have hφ := intervalIntegrable_of_plusOneMinus_integrand hφ₁
  have hsplit : (fun z => 2 * c.cA * (-1 + (1 - z) / z + z * (1 - z)) * φ z) =
      fun z => 2 * c.cA * (-φ z + ((1 - z) / z + z * (1 - z)) * φ z) := by
    funext z
    ring
  simp only [plusOneMinus_id_mul hφ₁, KernelForm.pair_def, pgg_regular, pgg_plusCoeff,
    pgg_deltaCoeff, hsplit,
    intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_add (f := fun z => -φ z) hφ.neg hreg, intervalIntegral.integral_neg]
  ring

/-! ### Moments in closed form -/

/-- The quark-to-quark moment `γ_qq(N) = C_F [3/2 - 2 S₁(N) + 1/(N (N+1))]`, for `N ≥ 1`. -/
theorem moment_pqq {N : ℕ} (hN : N ≠ 0) :
    (pqq c).moment N = c.cF * (3 / 2 - 2 * harmonic N + 1 / (N * (N + 1))) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN
  have hint : ∫ z in (0 : ℝ)..1, -c.cF * (1 + z) * z ^ n =
      -c.cF / (n + 1) + -c.cF / (n + 2) + 0 / (n + 3) + 0 / (n + 4) :=
    (intervalIntegral.integral_congr fun z _ => by simp only [Real.rpow_natCast]; ring).trans
      (integral_cubic_mul_rpow _ _ _ _ (neg_one_lt_zero.trans_le n.cast_nonneg))
  rw [Nat.succ_eq_add_one, Nat.cast_add_one, KernelForm.moment_natCast_add_one,
    KernelForm.pair_pow]
  simp only [pqq_regular, hint, pqq_plusCoeff, pqq_deltaCoeff, harmonic_succ]
  push_cast
  field_simp
  ring

/-- The gluon-in-quark moment `γ_gq(N) = C_F (N² + N + 2) / ((N - 1) N (N + 1))`, at every real
`N > 1`. The closed form has a pole at `N = 1`, where the integral defining the moment does not
converge and `(pgq c).moment 1` is the junk value of the Bochner integral. -/
theorem moment_pgq {N : ℝ} (hN : 1 < N) :
    (pgq c).moment N = c.cF * (N ^ 2 + N + 2) / ((N - 1) * N * (N + 1)) := by
  have hint : ∫ z in (0 : ℝ)..1, c.cF * (1 + (1 - z) ^ 2) / z * z ^ (N - 1) =
      2 * c.cF / (N - 2 + 1) + -(2 * c.cF) / (N - 2 + 2) + c.cF / (N - 2 + 3) +
        0 / (N - 2 + 4) := by
    refine (intervalIntegral.integral_congr_ae ?_).trans
      (integral_cubic_mul_rpow _ _ _ _ (by linarith : (-1 : ℝ) < N - 2))
    filter_upwards [Measure.ae_ne volume (0 : ℝ)] with z hz _
    rw [show N - 1 = N - 2 + 1 by ring, Real.rpow_add_one hz]
    field_simp
    ring
  have h1 : N - 1 ≠ 0 := by intro h; linarith
  have h0 : N ≠ 0 := by intro h; linarith
  have h2 : N + 1 ≠ 0 := by intro h; linarith
  have h3 : N + 2 ≠ 0 := by intro h; linarith
  rw [KernelForm.moment_def, KernelForm.pair_def]
  simp only [pgq_regular, hint, pgq_plusCoeff, pgq_deltaCoeff, zero_mul, add_zero]
  rw [show N - 2 + 1 = N - 1 by ring, show N - 2 + 2 = N by ring, show N - 2 + 3 = N + 1 by ring,
    show N - 2 + 4 = N + 2 by ring]
  field_simp
  ring

/-- The per-flavour quark-in-gluon moment `T_F (N² + N + 2) / (N (N + 1) (N + 2))`, at every
real `N > 0`. -/
theorem moment_pqg {N : ℝ} (hN : 0 < N) :
    (pqg c).moment N = c.tF * (N ^ 2 + N + 2) / (N * (N + 1) * (N + 2)) := by
  have hint : ∫ z in (0 : ℝ)..1, c.tF * (z ^ 2 + (1 - z) ^ 2) * z ^ (N - 1) =
      c.tF / (N - 1 + 1) + -(2 * c.tF) / (N - 1 + 2) + 2 * c.tF / (N - 1 + 3) +
        0 / (N - 1 + 4) :=
    (intervalIntegral.integral_congr fun z _ => by ring).trans
      (integral_cubic_mul_rpow _ _ _ _ (by linarith : (-1 : ℝ) < N - 1))
  have h0 : N ≠ 0 := hN.ne'
  have h1 : N + 1 ≠ 0 := by intro h; linarith
  have h2 : N + 2 ≠ 0 := by intro h; linarith
  have h3 : N + 3 ≠ 0 := by intro h; linarith
  rw [KernelForm.moment_def, KernelForm.pair_def]
  simp only [pqg_regular, hint, pqg_plusCoeff, pqg_deltaCoeff, zero_mul, add_zero]
  rw [show N - 1 + 1 = N by ring, show N - 1 + 2 = N + 1 by ring, show N - 1 + 3 = N + 2 by ring,
    show N - 1 + 4 = N + 3 by ring]
  field_simp
  ring

/-- The singlet quark-in-gluon moment `γ_qg(N) = 2 n_f T_F (N² + N + 2) / (N (N + 1) (N + 2))`,
at every real `N > 0`. -/
theorem moment_pqgSinglet {N : ℝ} (hN : 0 < N) :
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
      2 * c.cA / (n + 1) + -(4 * c.cA) / (n + 2) + 2 * c.cA / (n + 3) +
        -(2 * c.cA) / (n + 4) := by
    refine (intervalIntegral.integral_congr_ae ?_).trans
      (integral_cubic_mul_rpow _ _ _ _ (neg_one_lt_zero.trans_le n.cast_nonneg))
    filter_upwards [Measure.ae_ne volume (0 : ℝ)] with z hz _
    simp only [Real.rpow_natCast]
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
@[simp]
theorem moment_pqq_one : (pqq c).moment 1 = 0 := by
  rw [show (pqq c).moment 1 = (pqq c).moment ((1 : ℕ) : ℝ) by norm_num, moment_pqq c one_ne_zero,
    harmonic_one]
  norm_num

/-- The momentum moment of the quark-to-quark kernel, `M[P_qq](2) = -(4/3) C_F`. -/
@[simp]
theorem moment_pqq_two : (pqq c).moment 2 = -(4 / 3 * c.cF) := by
  rw [show (pqq c).moment 2 = (pqq c).moment ((2 : ℕ) : ℝ) by norm_num, moment_pqq c two_ne_zero,
    harmonic_two]
  push_cast
  ring

/-- The momentum moment of the gluon-in-quark kernel, `M[P_gq](2) = (4/3) C_F`. -/
@[simp]
theorem moment_pgq_two : (pgq c).moment 2 = 4 / 3 * c.cF := by
  rw [moment_pgq c one_lt_two]
  ring

/-- The momentum moment of the singlet quark-in-gluon kernel, `M[2 n_f P_qg](2) = (2/3) n_f T_F`.
-/
@[simp]
theorem moment_pqgSinglet_two : (pqgSinglet c).moment 2 = 2 / 3 * c.nF * c.tF := by
  rw [moment_pqgSinglet c two_pos]
  ring

/-- The momentum moment of the gluon-to-gluon kernel, `M[P_gg](2) = -(2/3) n_f T_F`: the
`C_A` terms cancel between the regular, plus and delta parts. -/
@[simp]
theorem moment_pgg_two : (pgg c).moment 2 = -(2 / 3 * c.nF * c.tF) := by
  rw [show (pgg c).moment 2 = (pgg c).moment ((2 : ℕ) : ℝ) by norm_num, moment_pgg c le_rfl,
    harmonic_two]
  push_cast
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
