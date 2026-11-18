/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.QFT.Factorization.Convolution.Algebra

/-!
# The double Mellin convolution on the unit square

A two-variable coefficient function `C (y, w)` acts on a pair of densities, one in each variable,
by the Mellin convolution in each variable:
```
(f ⊗ C ⊗ D) (x, z) = ∫_x^1 (dy / y) ∫_z^1 (dw / w) C (y, w) f (x / y) D (z / w),
```
for `x, z ∈ (0,1]`, and zero otherwise. This is the shape of the factorized cross section of
semi-inclusive deep-inelastic scattering, where `f` is a parton density in the momentum fraction
`x` of the struck parton, `D` is a fragmentation function in the momentum fraction `z` of the
observed hadron, and `C` is the coefficient function. The definition is the iterated
`mellinConv` of `EpsilonEridani.QFT.Factorization.Convolution.Algebra`, the inner one in `z` and
the outer one in `x`. In each variable the density is evaluated at the ratio (`f (x / y)`,
`D (z / w)`) and the coefficient at the integration variable.

Exchanging the roles of the two densities is a symmetry only together with the transposition
`C (y, w) ↦ C (w, y)` of the coefficient function (`doubleMellinConv_swap`, by Fubini). Without
the transposition the exchange fails (`exists_doubleMellinConv_ne`), so the two arguments of a
coefficient function cannot be interchanged silently. A coefficient function that is a product
`A (y) B (w)` gives the product of the two single convolutions (`doubleMellinConv_mul`).

## Main definitions

* `Convolution.doubleMellinConv C f D`: the double Mellin convolution `f ⊗ C ⊗ D`.

## Main results

* `doubleMellinConv_apply_of_mem`: the defining iterated integral on `(0,1]²`.
* `doubleMellinConv_of_notMem_left`, `doubleMellinConv_of_notMem_right`: support in `(0,1]²`.
* `doubleMellinConv_mul`: a product coefficient function factorizes the double convolution.
* `doubleMellinConv_swap`: exchanging the two densities transposes the coefficient function.
* `exists_doubleMellinConv_ne`: the exchange without transposition is not a symmetry.

## References

* G. Altarelli, R. K. Ellis, G. Martinelli and S.-Y. Pi, *Processes involving fragmentation
  functions beyond the leading order in QCD*, Nucl. Phys. B 160 (1979) 301.
* D. de Florian, M. Stratmann and W. Vogelsang, *QCD analysis of unpolarized and polarized
  Λ-baryon production in leading and next-to-leading order*, Phys. Rev. D 57 (1998) 5811.
-/

public section

noncomputable section

open MeasureTheory Set

namespace EpsilonEridani
namespace QFT
namespace Factorization
namespace Convolution

/-- The double Mellin convolution of a coefficient function `C (y, w)` with a density `f` in the
first variable and a density `D` in the second:
`doubleMellinConv C f D x z = ∫_x^1 (dy / y) ∫_z^1 (dw / w) C y w * f (x / y) * D (z / w)` for
`x, z ∈ (0,1]`, and `0` otherwise. It is the Mellin convolution in `z` of `C y` with `D`, followed
by the Mellin convolution in `x` of the result with `f`. -/
def doubleMellinConv (C : ℝ → ℝ → ℝ) (f D : ℝ → ℝ) (x z : ℝ) : ℝ :=
  mellinConv (fun y => mellinConv (C y) D z) f x

/-- Unfolding lemma for `doubleMellinConv`: the convolution in `x` of the convolutions in `z`. -/
theorem doubleMellinConv_def (C : ℝ → ℝ → ℝ) (f D : ℝ → ℝ) (x z : ℝ) :
    doubleMellinConv C f D x z = mellinConv (fun y => mellinConv (C y) D z) f x :=
  (rfl)

/-- The defining iterated integral of the double Mellin convolution on `(0,1]²`. -/
theorem doubleMellinConv_apply_of_mem (C : ℝ → ℝ → ℝ) (f D : ℝ → ℝ) {x z : ℝ}
    (hx : x ∈ Ioc (0 : ℝ) 1) (hz : z ∈ Ioc (0 : ℝ) 1) :
    doubleMellinConv C f D x z =
      ∫ y in Icc x 1, (∫ w in Icc z 1, C y w * D (z / w) / w) * f (x / y) / y := by
  simp only [doubleMellinConv_def, mellinConv_apply_of_mem _ _ hx, mellinConv_apply_of_mem _ _ hz]

/-- The double Mellin convolution vanishes when the first momentum fraction lies outside
`(0,1]`. -/
theorem doubleMellinConv_of_notMem_left (C : ℝ → ℝ → ℝ) (f D : ℝ → ℝ) {x : ℝ}
    (hx : x ∉ Ioc (0 : ℝ) 1) (z : ℝ) : doubleMellinConv C f D x z = 0 :=
  mellinConv_apply_eq_zero_of_notMem _ _ hx

/-- The double Mellin convolution vanishes when the second momentum fraction lies outside
`(0,1]`. -/
theorem doubleMellinConv_of_notMem_right (C : ℝ → ℝ → ℝ) (f D : ℝ → ℝ) (x : ℝ) {z : ℝ}
    (hz : z ∉ Ioc (0 : ℝ) 1) : doubleMellinConv C f D x z = 0 := by
  have h : (fun y => mellinConv (C y) D z) = 0 :=
    funext fun _ => mellinConv_apply_eq_zero_of_notMem _ _ hz
  rw [doubleMellinConv_def, h, mellinConv_zero_left, Pi.zero_apply]

/-- The double Mellin convolution with the zero coefficient function vanishes. -/
@[simp]
theorem zero_doubleMellinConv (f D : ℝ → ℝ) : doubleMellinConv 0 f D = 0 := by
  have h (z : ℝ) : (fun y => mellinConv ((0 : ℝ → ℝ → ℝ) y) D z) = 0 := by
    funext y
    rw [Pi.zero_apply, mellinConv_zero_left, Pi.zero_apply, Pi.zero_apply]
  funext x z
  rw [doubleMellinConv_def, h, mellinConv_zero_left, Pi.zero_apply, Pi.zero_apply,
    Pi.zero_apply]

/-- **Factorization for a product coefficient function.** If `C (y, w) = A y * B w`, the double
Mellin convolution is the product of the Mellin convolution of `A` with `f` in `x` and of `B` with
`D` in `z`. No integrability hypothesis is needed. -/
theorem doubleMellinConv_mul (A B : ℝ → ℝ) (f D : ℝ → ℝ) (x z : ℝ) :
    doubleMellinConv (fun y w => A y * B w) f D x z = mellinConv A f x * mellinConv B D z := by
  have hin : (fun y => mellinConv (fun w => A y * B w) D z) =
      mellinConv B D z • A := by
    funext y
    have hB : (fun w => A y * B w) = A y • B :=
      funext fun w => by rw [Pi.smul_apply, smul_eq_mul]
    rw [hB, mellinConv_smul_left, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
      mul_comm]
  rw [doubleMellinConv_def, hin, mellinConv_smul_left, Pi.smul_apply, smul_eq_mul, mul_comm]

/-- **Exchanging the densities transposes the coefficient function.** The double convolution of
`C` with `f` in `x` and `D` in `z` equals the double convolution of the transposed coefficient
function `(y, w) ↦ C w y` with `D` in the first variable and `f` in the second, evaluated at
`(z, x)`. This is Fubini's theorem, under joint integrability of the integrand on
`[x, 1] × [z, 1]` for `x, z ∈ (0,1]`. -/
theorem doubleMellinConv_swap (C : ℝ → ℝ → ℝ) (f D : ℝ → ℝ) {x z : ℝ}
    (h : x ∈ Ioc (0 : ℝ) 1 → z ∈ Ioc (0 : ℝ) 1 →
      IntegrableOn (fun p : ℝ × ℝ => C p.1 p.2 * (f (x / p.1) / p.1) * (D (z / p.2) / p.2))
        (Icc x 1 ×ˢ Icc z 1)) :
    doubleMellinConv (Function.swap C) D f z x = doubleMellinConv C f D x z := by
  by_cases hx : x ∈ Ioc (0 : ℝ) 1
  · by_cases hz : z ∈ Ioc (0 : ℝ) 1
    · have hint : Integrable
          (Function.uncurry fun y w => C y w * (f (x / y) / y) * (D (z / w) / w))
          ((volume.restrict (Icc x 1)).prod (volume.restrict (Icc z 1))) := by
        rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
        exact h hx hz
      rw [doubleMellinConv_apply_of_mem _ _ _ hz hx, doubleMellinConv_apply_of_mem _ _ _ hx hz]
      -- Both sides are the iterated integrals, in the two orders, of one function on the
      -- rectangle `[x, 1] × [z, 1]`.
      have hl : (∫ w in Icc z 1, (∫ y in Icc x 1, Function.swap C w y * f (x / y) / y) *
            D (z / w) / w) =
          ∫ w in Icc z 1, ∫ y in Icc x 1, C y w * (f (x / y) / y) * (D (z / w) / w) := by
        refine setIntegral_congr_fun measurableSet_Icc fun w _ => ?_
        rw [mul_div_assoc, ← integral_mul_const]
        refine setIntegral_congr_fun measurableSet_Icc fun y _ => ?_
        simp only [Function.swap]
        ring
      have hr : (∫ y in Icc x 1, (∫ w in Icc z 1, C y w * D (z / w) / w) *
            f (x / y) / y) =
          ∫ y in Icc x 1, ∫ w in Icc z 1, C y w * (f (x / y) / y) * (D (z / w) / w) := by
        refine setIntegral_congr_fun measurableSet_Icc fun y _ => ?_
        rw [mul_div_assoc, ← integral_mul_const]
        refine setIntegral_congr_fun measurableSet_Icc fun w _ => ?_
        ring
      rw [hl, hr, integral_integral_swap hint]
    · rw [doubleMellinConv_of_notMem_left _ _ _ hz, doubleMellinConv_of_notMem_right _ _ _ _ hz]
  · rw [doubleMellinConv_of_notMem_right _ _ _ _ hx, doubleMellinConv_of_notMem_left _ _ _ hx]

/-- **Exchanging the densities without transposing is not a symmetry.** For the coefficient
function `C (y, w) = y w²` and the density `1` on `(0,1]` in both variables,
`doubleMellinConv C 1 1 (1/2) (1/4) = 15/64` while `doubleMellinConv C 1 1 (1/4) (1/2) = 9/32`. -/
theorem exists_doubleMellinConv_ne :
    ∃ (C : ℝ → ℝ → ℝ) (f D : ℝ → ℝ) (x z : ℝ),
      doubleMellinConv C D f z x ≠ doubleMellinConv C f D x z := by
  set one := (Ioc (0 : ℝ) 1).indicator (1 : ℝ → ℝ)
  -- The two single convolutions against `1` on `(0,1]`, in closed form.
  have hA {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) : mellinConv (fun y => y) one t = 1 - t := by
    rw [mellinConv_indicator_one_apply_of_mem _ ht,
      setIntegral_congr_fun measurableSet_Icc fun y hy => div_self (ht.1.trans_le hy.1).ne',
      setIntegral_const, Real.volume_real_Icc_of_le ht.2, smul_eq_mul, mul_one]
  have hB {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
      mellinConv (fun y => y ^ 2) one t = (1 - t ^ 2) / 2 := by
    rw [mellinConv_indicator_one_apply_of_mem _ ht,
      setIntegral_congr_fun measurableSet_Icc fun y hy => by
        rw [sq, mul_div_cancel_right₀ _ (ht.1.trans_le hy.1).ne'],
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht.2, integral_id]
    ring
  have h₁ : (1 / 2 : ℝ) ∈ Ioc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have h₂ : (1 / 4 : ℝ) ∈ Ioc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  refine ⟨fun y w => y * w ^ 2, one, one, 1 / 2, 1 / 4, ?_⟩
  rw [doubleMellinConv_mul, doubleMellinConv_mul, hA h₁, hA h₂, hB h₁, hB h₂]
  norm_num

end Convolution
end Factorization
end QFT
end EpsilonEridani
