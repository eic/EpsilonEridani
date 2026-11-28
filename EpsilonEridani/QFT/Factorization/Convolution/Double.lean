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
`C (y, w) ↦ C (w, y)` of the coefficient function, provided the integrand is jointly integrable on
`[x, 1] × [z, 1]` (`doubleMellinConv_swap`, by Fubini). Without
the transposition the exchange fails (`exists_doubleMellinConv_swap_densities_ne`), so the two
arguments of a coefficient function cannot be interchanged silently. A coefficient function
that is a product `A (y) B (w)` gives the product of the two single convolutions
(`doubleMellinConv_prod_mul`).

## Main definitions

* `Convolution.doubleMellinConv C f D`: the double Mellin convolution `f ⊗ C ⊗ D`.

## Main results

* `doubleMellinConv_apply_of_mem`: the defining iterated integral on `(0,1]²`.
* `doubleMellinConv_apply_eq_convolveAt_of_mem`: the same as iterated collinear convolutions.
* `doubleMellinConv_congr_of_eqOn`: only the values on `(0,1]²` and `(0,1]` enter.
* `doubleMellinConv_apply_eq_zero_of_notMem_left`, `doubleMellinConv_apply_eq_zero_of_notMem_right`:
  support in `(0,1]²`.
* `doubleMellinConv_prod_mul`: a product coefficient function factorizes the double convolution.
* `doubleMellinConv_zero`, `doubleMellinConv_zero_density_left`,
  `doubleMellinConv_zero_density_right`: the zero coefficient function and the zero densities.
* `doubleMellinConv_swap`: exchanging the two densities transposes the coefficient function,
  under joint integrability.
* `exists_doubleMellinConv_swap_densities_ne`: the exchange without transposition is not a
  symmetry.

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

/-- The double Mellin convolution on `(0,1]²` as iterated collinear convolutions `convolveAt`. -/
theorem doubleMellinConv_apply_eq_convolveAt_of_mem (C : ℝ → ℝ → ℝ) (f D : ℝ → ℝ) {x z : ℝ}
    (hx : x ∈ Ioc (0 : ℝ) 1) (hz : z ∈ Ioc (0 : ℝ) 1) :
    doubleMellinConv C f D x z =
      convolveAt (collinearKernel f) (fun y => convolveAt (collinearKernel D) (C y) z) x := by
  simp only [doubleMellinConv_def, mellinConv_apply_eq_convolveAt_of_mem _ _ hx,
    mellinConv_apply_eq_convolveAt_of_mem _ _ hz]

/-- The double Mellin convolution depends only on the values of the coefficient function on
`(0,1]²` and of the densities on `(0,1]`. -/
theorem doubleMellinConv_congr_of_eqOn {C C' : ℝ → ℝ → ℝ} {f f' D D' : ℝ → ℝ}
    (hC : EqOn (Function.uncurry C) (Function.uncurry C') (Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1))
    (hf : EqOn f f' (Ioc (0 : ℝ) 1)) (hD : EqOn D D' (Ioc (0 : ℝ) 1)) :
    doubleMellinConv C f D = doubleMellinConv C' f' D' := by
  funext x z
  rw [doubleMellinConv_def, doubleMellinConv_def]
  refine congrFun (mellinConv_congr_of_eqOn (fun y hy => ?_) hf) x
  refine congrFun (mellinConv_congr_of_eqOn (fun w hw => ?_) hD) z
  simpa only [Function.uncurry_apply_pair] using hC (mk_mem_prod hy hw)

/-- The double Mellin convolution vanishes when the first momentum fraction lies outside
`(0,1]`. -/
theorem doubleMellinConv_apply_eq_zero_of_notMem_left (C : ℝ → ℝ → ℝ) (f D : ℝ → ℝ) {x : ℝ}
    (hx : x ∉ Ioc (0 : ℝ) 1) (z : ℝ) : doubleMellinConv C f D x z = 0 := by
  rw [doubleMellinConv_def]
  exact mellinConv_apply_eq_zero_of_notMem _ _ hx

/-- The double Mellin convolution vanishes when the second momentum fraction lies outside
`(0,1]`. -/
theorem doubleMellinConv_apply_eq_zero_of_notMem_right (C : ℝ → ℝ → ℝ) (f D : ℝ → ℝ) (x : ℝ) {z : ℝ}
    (hz : z ∉ Ioc (0 : ℝ) 1) : doubleMellinConv C f D x z = 0 := by
  have h : (fun y => mellinConv (C y) D z) = 0 :=
    funext fun _ => mellinConv_apply_eq_zero_of_notMem _ _ hz
  rw [doubleMellinConv_def, h, mellinConv_zero_left, Pi.zero_apply]

/-- The double Mellin convolution with the zero coefficient function vanishes. -/
@[simp]
theorem doubleMellinConv_zero (f D : ℝ → ℝ) : doubleMellinConv 0 f D = 0 := by
  funext x z
  simp [doubleMellinConv_def, ← Pi.zero_def]

/-- The double Mellin convolution with the zero density in the first variable vanishes. -/
@[simp]
theorem doubleMellinConv_zero_density_left (C : ℝ → ℝ → ℝ) (D : ℝ → ℝ) :
    doubleMellinConv C 0 D = 0 := by
  funext x z
  simp [doubleMellinConv_def]

/-- The double Mellin convolution with the zero density in the second variable vanishes. -/
@[simp]
theorem doubleMellinConv_zero_density_right (C : ℝ → ℝ → ℝ) (f : ℝ → ℝ) :
    doubleMellinConv C f 0 = 0 := by
  funext x z
  simp [doubleMellinConv_def, ← Pi.zero_def]

/-- **Factorization for a product coefficient function.** If `C (y, w) = A y * B w`, the double
Mellin convolution is the product of the Mellin convolution of `A` with `f` in `x` and of `B` with
`D` in `z`. No integrability hypothesis is needed. -/
theorem doubleMellinConv_prod_mul (A B : ℝ → ℝ) (f D : ℝ → ℝ) (x z : ℝ) :
    doubleMellinConv (fun y w => A y * B w) f D x z = mellinConv A f x * mellinConv B D z := by
  have hin : (fun y => mellinConv (fun w => A y * B w) D z) = mellinConv B D z • A := by
    funext y
    have hB : (fun w => A y * B w) = A y • B :=
      funext fun w => by rw [Pi.smul_apply, smul_eq_mul]
    rw [hB]
    simp [mul_comm]
  simp [doubleMellinConv_def, hin, mul_comm]

/-- Moving the outer factor `u a / v a` of an iterated set integral into the inner integral, with
a pointwise rearrangement `G a b * (u a / v a) = H a b` of the integrand. -/
private theorem setIntegral_integral_mul_div {s t : Set ℝ} (hs : MeasurableSet s)
    (ht : MeasurableSet t) {G H : ℝ → ℝ → ℝ} {u v : ℝ → ℝ}
    (hGH : ∀ a ∈ s, ∀ b ∈ t, G a b * (u a / v a) = H a b) :
    ∫ a in s, (∫ b in t, G a b) * u a / v a = ∫ a in s, ∫ b in t, H a b :=
  setIntegral_congr_fun hs fun a ha => by
    rw [mul_div_assoc, ← integral_mul_const]
    exact setIntegral_congr_fun ht fun b hb => hGH a ha b hb

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
        rw [Measure.prod_restrict, ← Measure.volume_eq_prod, Function.uncurry_def]
        exact h hx hz
      rw [doubleMellinConv_apply_of_mem _ _ _ hz hx, doubleMellinConv_apply_of_mem _ _ _ hx hz]
      -- Both sides are the iterated integrals, in the two orders, of one function on the
      -- rectangle `[x, 1] × [z, 1]`.
      set F := fun y w => C y w * (f (x / y) / y) * (D (z / w) / w) with hF
      rw [setIntegral_integral_mul_div (H := Function.swap F) measurableSet_Icc measurableSet_Icc
          fun w _ y _ => by rw [Function.swap_def, hF]; ring,
        setIntegral_integral_mul_div (H := F) measurableSet_Icc measurableSet_Icc
          fun y _ w _ => by rw [hF]; ring,
        integral_integral_swap hint]
    · rw [doubleMellinConv_apply_eq_zero_of_notMem_left _ _ _ hz,
        doubleMellinConv_apply_eq_zero_of_notMem_right _ _ _ _ hz]
  · rw [doubleMellinConv_apply_eq_zero_of_notMem_right _ _ _ _ hx,
      doubleMellinConv_apply_eq_zero_of_notMem_left _ _ _ hx]

/-- **Exchanging the densities without transposing is not a symmetry.** For the coefficient
function `C (y, w) = y w²` and the density `1` on `(0,1]` in both variables,
`doubleMellinConv C 1 1 (1/2) (1/4) = 15/64` while `doubleMellinConv C 1 1 (1/4) (1/2) = 9/32`. -/
theorem exists_doubleMellinConv_swap_densities_ne :
    ∃ (C : ℝ → ℝ → ℝ) (f D : ℝ → ℝ) (x z : ℝ),
      doubleMellinConv C D f z x ≠ doubleMellinConv C f D x z := by
  -- The two single convolutions against `1` on `(0,1]`, in closed form.
  have hA {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
      mellinConv (fun y => y) ((Ioc (0 : ℝ) 1).indicator 1) t = 1 - t := by
    simpa using mellinConv_pow_succ_indicator_one_apply_of_mem 0 ht
  have hB {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
      mellinConv (fun y => y ^ 2) ((Ioc (0 : ℝ) 1).indicator 1) t = (1 - t ^ 2) / 2 := by
    simpa [one_add_one_eq_two] using mellinConv_pow_succ_indicator_one_apply_of_mem 1 ht
  have h₁ : (1 / 2 : ℝ) ∈ Ioc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have h₂ : (1 / 4 : ℝ) ∈ Ioc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  refine ⟨fun y w => y * w ^ 2, (Ioc (0 : ℝ) 1).indicator 1, (Ioc (0 : ℝ) 1).indicator 1, 1 / 2,
    1 / 4, ?_⟩
  rw [doubleMellinConv_prod_mul, doubleMellinConv_prod_mul, hA h₁, hA h₂, hB h₁, hB h₂]
  norm_num

end Convolution
end Factorization
end QFT
end EpsilonEridani
