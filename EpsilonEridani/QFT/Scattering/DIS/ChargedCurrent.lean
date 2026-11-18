/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.Particles.Parton.PDF.ChargeConjugation
public import EpsilonEridani.QFT.Scattering.DIS.CrossSection
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.Matrix.Diagonal

/-!
# Charged-current structure functions in the quark-parton model

In charged-current deep-inelastic scattering the target absorbs a `W` boson. A `W⁻` (emitted by an
incoming electron, `e⁻ p → ν X`, or by an incoming antineutrino, `νbar p → e⁺ X`) turns an up-type
quark into a down-type quark and a down-type antiquark into an up-type antiquark. A `W⁺` (from
`e⁺ p → νbar X` or `ν p → e⁻ X`) does the reverse. The vertex joining the up-type flavour `i` to the
down-type flavour `j` carries the mixing-matrix entry `V i j`, so at leading order each channel
`i ↔ j` enters with the weight `‖V i j‖²`, and the structure functions of a target with parton
densities `f` are

* `F₂^{W⁻} = 2 x Σᵢⱼ ‖V i j‖² (u_i + dbar_j)` and `x F₃^{W⁻} = 2 x Σᵢⱼ ‖V i j‖² (u_i - dbar_j)`,
* `F₂^{W⁺} = 2 x Σᵢⱼ ‖V i j‖² (d_j + ubar_i)` and `x F₃^{W⁺} = 2 x Σᵢⱼ ‖V i j‖² (d_j - ubar_i)`,

where `u_i` is the density of the up-type quark `up i`, `d_j` that of the down-type quark
`down j`, and the bars denote antiquarks. The up-type and down-type flavours are indexed by
arbitrary finite types `ι` and `κ`, embedded in the target's flavour type by `up` and `down`, and
the mixing matrix `V : Matrix ι κ ℂ` is a parameter. It need not be square: below the charm
threshold the only active up-type flavour is `u`, and its row `(V_ud, V_us)` distributes the `W⁻`
over `d` and `s`.

Summing over the final-state flavour collapses the weights to the row sums `Σⱼ ‖V i j‖²` on the
quark side and the column sums `Σᵢ ‖V i j‖²` on the antiquark side (`f2CCMinusLO_eq_sum_add_sum`).
These weighted forms hold for every `V`, rectangular or not. When every row and every column of
`V` has unit norm, as for a unitary mixing matrix (which forces `V` to be square), the mixing
drops out of every inclusive structure function and the flavour-diagonal formulas hold:
`F₂^{W⁻} = 2 x (Σᵢ u_i + Σⱼ dbar_j)` (`f2CCMinusLO_eq_of_sum_norm_sq_eq_one`), which for the
four light flavours is the familiar `F₂^{e⁻p} = 2 x (u + c + dbar + sbar)`. No mixing,
`V = 1`, is the special case `f2CCMinusLO_one`.

The quark-parton model makes the following consequences exact at leading order.

* *Charge conjugation.* The `W⁺` structure functions of a target are the `W⁻` structure functions
  of its charge conjugate, with `x F₃` changing sign (`f2CCPlusLO_eq_f2CCMinusLO_chargeConj`,
  `xf3CCPlusLO_eq_neg_xf3CCMinusLO_chargeConj`).
* *Quark/antiquark separation.* `F₂ + x F₃` sees only quarks and `F₂ - x F₃` only antiquarks
  (`f2CCMinusLO_add_xf3CCMinusLO`, `f2CCMinusLO_sub_xf3CCMinusLO`, and their `W⁺` versions).
* *Positivity.* For `0 ≤ x` and non-negative quark and antiquark densities in the active
  channels, `F₂ ≥ 0` and `|x F₃| ≤ F₂`
  (`abs_xf3CCMinusLO_le_f2CCMinusLO`, `abs_xf3CCPlusLO_le_f2CCPlusLO`).
* *The sum-rule integrands.* `F₂^{W⁻} - F₂^{W⁺}` and `x F₃^{W⁻} + x F₃^{W⁺}` are combinations of
  valence densities, weighted by the squared norms of the rows and columns of `V`
  (`f2CCMinusLO_sub_f2CCPlusLO`, `xf3CCMinusLO_add_xf3CCPlusLO`). With unit-norm rows and columns,
  `F₂^{W⁻} - F₂^{W⁺} = 2 x (Σᵢ (u_i - ubar_i) - Σⱼ (d_j - dbar_j))`, the integrand of the Adler
  sum rule (`f2CCMinusLO_sub_f2CCPlusLO_eq_of_sum_norm_sq_eq_one`), and
  `x F₃^{W⁻} + x F₃^{W⁺} = 2 x (Σᵢ (u_i - ubar_i) + Σⱼ (d_j - dbar_j))`, a sum of valence
  densities (`xf3CCMinusLO_add_xf3CCPlusLO_eq_of_sum_norm_sq_eq_one`).
* *Agreement with the neutral current in the flavour-blind limit.* When the up-type and down-type
  flavours together exhaust the flavour type and the rows and columns of `V` have unit norm, the
  average of the `W⁻` and `W⁺` structure functions is the neutral-current `F₂` with every charge
  equal to one (`f2CCMinusLO_add_f2CCPlusLO_eq_two_mul_f2LO`), so the two hard kernels are
  normalised the same way.

## Main definitions

* `f2CCMinusLO`, `xf3CCMinusLO`: `F₂` and `x F₃` for `W⁻` absorption.
* `f2CCPlusLO`, `xf3CCPlusLO`: `F₂` and `x F₃` for `W⁺` absorption.

## References

* R. Devenish and A. Cooper-Sarkar, *Deep Inelastic Scattering*, Oxford University Press (2004),
  ch. 5.
* S. Navas et al. (Particle Data Group), *Review of Particle Physics*, Phys. Rev. D 110 (2024)
  030001, review *Structure functions*.
-/

public section

noncomputable section

namespace EpsilonEridani
namespace QFT
namespace Scattering
namespace DIS

open Particles.Parton (Species)
open Particles.Parton.Species (quark antiquark)
open Particles.Parton.PDF (Pdf chargeConj chargeConj_apply)

variable {Flavor ι κ : Type} [Fintype ι] [Fintype κ]

/-!
## The structure functions
-/

/-- The leading-order charged-current structure function `F₂` for absorption of a `W⁻` by a
target with parton densities `f`: `F₂^{W⁻} = 2 x Σᵢⱼ ‖V i j‖² (u_i + dbar_j)`. The `W⁻` is absorbed
on the up-type quark `up i` and on the down-type antiquark `down j`, each channel `i ↔ j` weighted
by the squared modulus of the mixing-matrix entry `V i j`. This is `F₂` for `e⁻ p` and `νbar p`
scattering. -/
def f2CCMinusLO (V : Matrix ι κ ℂ) (up : ι → Flavor) (down : κ → Flavor)
    (f : Pdf (Species Flavor)) (x Q2 : ℝ) : ℝ :=
  2 * x * ∑ i, ∑ j, ‖V i j‖ ^ 2 * (f (quark (up i)) x Q2 + f (antiquark (down j)) x Q2)

/-- The leading-order charged-current structure function `x F₃` for absorption of a `W⁻`:
`x F₃^{W⁻} = 2 x Σᵢⱼ ‖V i j‖² (u_i - dbar_j)`. The quark and antiquark channels of `f2CCMinusLO`
enter with opposite signs. -/
def xf3CCMinusLO (V : Matrix ι κ ℂ) (up : ι → Flavor) (down : κ → Flavor)
    (f : Pdf (Species Flavor)) (x Q2 : ℝ) : ℝ :=
  2 * x * ∑ i, ∑ j, ‖V i j‖ ^ 2 * (f (quark (up i)) x Q2 - f (antiquark (down j)) x Q2)

/-- The leading-order charged-current structure function `F₂` for absorption of a `W⁺` by a
target with parton densities `f`: `F₂^{W⁺} = 2 x Σᵢⱼ ‖V i j‖² (d_j + ubar_i)`. The `W⁺` is absorbed
on the down-type quark `down j` and on the up-type antiquark `up i`. This is `F₂` for `e⁺ p` and
`ν p` scattering. -/
def f2CCPlusLO (V : Matrix ι κ ℂ) (up : ι → Flavor) (down : κ → Flavor)
    (f : Pdf (Species Flavor)) (x Q2 : ℝ) : ℝ :=
  2 * x * ∑ i, ∑ j, ‖V i j‖ ^ 2 * (f (quark (down j)) x Q2 + f (antiquark (up i)) x Q2)

/-- The leading-order charged-current structure function `x F₃` for absorption of a `W⁺`:
`x F₃^{W⁺} = 2 x Σᵢⱼ ‖V i j‖² (d_j - ubar_i)`. -/
def xf3CCPlusLO (V : Matrix ι κ ℂ) (up : ι → Flavor) (down : κ → Flavor)
    (f : Pdf (Species Flavor)) (x Q2 : ℝ) : ℝ :=
  2 * x * ∑ i, ∑ j, ‖V i j‖ ^ 2 * (f (quark (down j)) x Q2 - f (antiquark (up i)) x Q2)

variable (V : Matrix ι κ ℂ) (up : ι → Flavor) (down : κ → Flavor) (f : Pdf (Species Flavor))
  (x Q2 : ℝ)

/-- The defining formula of `F₂^{W⁻}`, `2 x Σᵢⱼ ‖V i j‖² (u_i + dbar_j)`. -/
theorem f2CCMinusLO_def : f2CCMinusLO V up down f x Q2 =
    2 * x * ∑ i, ∑ j, ‖V i j‖ ^ 2 * (f (quark (up i)) x Q2 + f (antiquark (down j)) x Q2) :=
  (rfl)

/-- The defining formula of `x F₃^{W⁻}`, `2 x Σᵢⱼ ‖V i j‖² (u_i - dbar_j)`. -/
theorem xf3CCMinusLO_def : xf3CCMinusLO V up down f x Q2 =
    2 * x * ∑ i, ∑ j, ‖V i j‖ ^ 2 * (f (quark (up i)) x Q2 - f (antiquark (down j)) x Q2) :=
  (rfl)

/-- The defining formula of `F₂^{W⁺}`, `2 x Σᵢⱼ ‖V i j‖² (d_j + ubar_i)`. -/
theorem f2CCPlusLO_def : f2CCPlusLO V up down f x Q2 =
    2 * x * ∑ i, ∑ j, ‖V i j‖ ^ 2 * (f (quark (down j)) x Q2 + f (antiquark (up i)) x Q2) :=
  (rfl)

/-- The defining formula of `x F₃^{W⁺}`, `2 x Σᵢⱼ ‖V i j‖² (d_j - ubar_i)`. -/
theorem xf3CCPlusLO_def : xf3CCPlusLO V up down f x Q2 =
    2 * x * ∑ i, ∑ j, ‖V i j‖ ^ 2 * (f (quark (down j)) x Q2 - f (antiquark (up i)) x Q2) :=
  (rfl)

/-!
## Charge conjugation
-/

/-- **`W⁺` on a target is `W⁻` on its charge conjugate.** -/
theorem f2CCPlusLO_eq_f2CCMinusLO_chargeConj :
    f2CCPlusLO V up down f x Q2 = f2CCMinusLO V up down (chargeConj f) x Q2 := by
  simp only [f2CCPlusLO_def, f2CCMinusLO_def, chargeConj_apply, Species.conj_quark,
    Species.conj_antiquark, add_comm]

/-- **`x F₃` changes sign under charge conjugation.** `x F₃^{W⁺}` of a target is minus
`x F₃^{W⁻}` of its charge conjugate. -/
theorem xf3CCPlusLO_eq_neg_xf3CCMinusLO_chargeConj :
    xf3CCPlusLO V up down f x Q2 = -xf3CCMinusLO V up down (chargeConj f) x Q2 := by
  simp only [xf3CCPlusLO_def, xf3CCMinusLO_def, chargeConj_apply, Species.conj_quark,
    Species.conj_antiquark, ← mul_neg, ← Finset.sum_neg_distrib, neg_sub]

/-!
## Summing over the final-state flavour

A channel sum `Σᵢⱼ ‖V i j‖² (a_i ± b_j)` weights `a_i` by the squared norm of row `i` of `V` and
`b_j` by the squared norm of column `j`.
-/

/-- `F₂^{W⁻}` with the final-state flavour summed: each up-type quark is weighted by the squared
norm `Σⱼ ‖V i j‖²` of its row of `V`, and each down-type antiquark by the squared norm
`Σᵢ ‖V i j‖²` of its column. -/
theorem f2CCMinusLO_eq_sum_add_sum : f2CCMinusLO V up down f x Q2 =
    2 * x * (∑ i, (∑ j, ‖V i j‖ ^ 2) * f (quark (up i)) x Q2 +
      ∑ j, (∑ i, ‖V i j‖ ^ 2) * f (antiquark (down j)) x Q2) := by
  simp only [f2CCMinusLO_def, mul_add, Finset.sum_add_distrib, Finset.sum_mul]
  rw [Finset.sum_comm (f := fun i j => ‖V i j‖ ^ 2 * f (antiquark (down j)) x Q2)]

/-- `x F₃^{W⁻}` with the final-state flavour summed. -/
theorem xf3CCMinusLO_eq_sum_sub_sum : xf3CCMinusLO V up down f x Q2 =
    2 * x * (∑ i, (∑ j, ‖V i j‖ ^ 2) * f (quark (up i)) x Q2 -
      ∑ j, (∑ i, ‖V i j‖ ^ 2) * f (antiquark (down j)) x Q2) := by
  simp only [xf3CCMinusLO_def, mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]
  rw [Finset.sum_comm (f := fun i j => ‖V i j‖ ^ 2 * f (antiquark (down j)) x Q2)]

/-- `F₂^{W⁺}` with the final-state flavour summed: each down-type quark is weighted by the squared
norm `Σᵢ ‖V i j‖²` of its column of `V`, and each up-type antiquark by the squared norm
`Σⱼ ‖V i j‖²` of its row. -/
theorem f2CCPlusLO_eq_sum_add_sum : f2CCPlusLO V up down f x Q2 =
    2 * x * (∑ j, (∑ i, ‖V i j‖ ^ 2) * f (quark (down j)) x Q2 +
      ∑ i, (∑ j, ‖V i j‖ ^ 2) * f (antiquark (up i)) x Q2) := by
  rw [f2CCPlusLO_eq_f2CCMinusLO_chargeConj, f2CCMinusLO_eq_sum_add_sum, add_comm]
  simp only [chargeConj_apply, Species.conj_quark, Species.conj_antiquark]

/-- `x F₃^{W⁺}` with the final-state flavour summed. -/
theorem xf3CCPlusLO_eq_sum_sub_sum : xf3CCPlusLO V up down f x Q2 =
    2 * x * (∑ j, (∑ i, ‖V i j‖ ^ 2) * f (quark (down j)) x Q2 -
      ∑ i, (∑ j, ‖V i j‖ ^ 2) * f (antiquark (up i)) x Q2) := by
  rw [xf3CCPlusLO_eq_neg_xf3CCMinusLO_chargeConj, xf3CCMinusLO_eq_sum_sub_sum, ← mul_neg, neg_sub]
  simp only [chargeConj_apply, Species.conj_quark, Species.conj_antiquark]

/-!
## Unit-norm rows and columns: the flavour-diagonal formulas
-/

variable {V}

/-- **The mixing drops out of `F₂^{W⁻}`.** When every row and every column of the mixing matrix
has unit norm, as for a unitary matrix, `F₂^{W⁻} = 2 x (Σᵢ u_i + Σⱼ dbar_j)`. For the four light
flavours this is `F₂^{e⁻p} = 2 x (u + c + dbar + sbar)`. -/
theorem f2CCMinusLO_eq_of_sum_norm_sq_eq_one (hrow : ∀ i, ∑ j, ‖V i j‖ ^ 2 = 1)
    (hcol : ∀ j, ∑ i, ‖V i j‖ ^ 2 = 1) : f2CCMinusLO V up down f x Q2 =
      2 * x * (∑ i, f (quark (up i)) x Q2 + ∑ j, f (antiquark (down j)) x Q2) := by
  simp [f2CCMinusLO_eq_sum_add_sum, hrow, hcol]

/-- **The mixing drops out of `x F₃^{W⁻}`.** With unit-norm rows and columns,
`x F₃^{W⁻} = 2 x (Σᵢ u_i - Σⱼ dbar_j)`. -/
theorem xf3CCMinusLO_eq_of_sum_norm_sq_eq_one (hrow : ∀ i, ∑ j, ‖V i j‖ ^ 2 = 1)
    (hcol : ∀ j, ∑ i, ‖V i j‖ ^ 2 = 1) : xf3CCMinusLO V up down f x Q2 =
      2 * x * (∑ i, f (quark (up i)) x Q2 - ∑ j, f (antiquark (down j)) x Q2) := by
  simp [xf3CCMinusLO_eq_sum_sub_sum, hrow, hcol]

/-- **The mixing drops out of `F₂^{W⁺}`.** With unit-norm rows and columns,
`F₂^{W⁺} = 2 x (Σⱼ d_j + Σᵢ ubar_i)`. For the four light flavours this is
`F₂^{e⁺p} = 2 x (d + s + ubar + cbar)`. -/
theorem f2CCPlusLO_eq_of_sum_norm_sq_eq_one (hrow : ∀ i, ∑ j, ‖V i j‖ ^ 2 = 1)
    (hcol : ∀ j, ∑ i, ‖V i j‖ ^ 2 = 1) : f2CCPlusLO V up down f x Q2 =
      2 * x * (∑ j, f (quark (down j)) x Q2 + ∑ i, f (antiquark (up i)) x Q2) := by
  simp [f2CCPlusLO_eq_sum_add_sum, hrow, hcol]

/-- **The mixing drops out of `x F₃^{W⁺}`.** With unit-norm rows and columns,
`x F₃^{W⁺} = 2 x (Σⱼ d_j - Σᵢ ubar_i)`. -/
theorem xf3CCPlusLO_eq_of_sum_norm_sq_eq_one (hrow : ∀ i, ∑ j, ‖V i j‖ ^ 2 = 1)
    (hcol : ∀ j, ∑ i, ‖V i j‖ ^ 2 = 1) : xf3CCPlusLO V up down f x Q2 =
      2 * x * (∑ j, f (quark (down j)) x Q2 - ∑ i, f (antiquark (up i)) x Q2) := by
  simp [xf3CCPlusLO_eq_sum_sub_sum, hrow, hcol]

section NoMixing

variable {n : Type} [Fintype n] [DecidableEq n] (up : n → Flavor) (down : n → Flavor)

/-- Each row of the identity matrix has unit squared norm. -/
private theorem sum_norm_sq_one_row (i : n) : ∑ j, ‖(1 : Matrix n n ℂ) i j‖ ^ 2 = 1 := by
  simp [Matrix.one_apply, apply_ite (fun z : ℂ => ‖z‖ ^ 2)]

/-- Each column of the identity matrix has unit squared norm. -/
private theorem sum_norm_sq_one_col (j : n) : ∑ i, ‖(1 : Matrix n n ℂ) i j‖ ^ 2 = 1 := by
  simp [Matrix.one_apply, apply_ite (fun z : ℂ => ‖z‖ ^ 2)]

/-- **`F₂^{W⁻}` without mixing.** With `V = 1` each up-type flavour `up i` is paired with the
down-type flavour `down i` of its generation: `F₂^{W⁻} = 2 x Σᵢ (u_i + dbar_i)`. -/
@[simp]
theorem f2CCMinusLO_one :
    f2CCMinusLO 1 up down f x Q2 =
      2 * x * ∑ i, (f (quark (up i)) x Q2 + f (antiquark (down i)) x Q2) := by
  rw [f2CCMinusLO_eq_of_sum_norm_sq_eq_one up down f x Q2 sum_norm_sq_one_row sum_norm_sq_one_col,
    Finset.sum_add_distrib]

/-- **`x F₃^{W⁻}` without mixing.** `x F₃^{W⁻} = 2 x Σᵢ (u_i - dbar_i)`. -/
@[simp]
theorem xf3CCMinusLO_one :
    xf3CCMinusLO 1 up down f x Q2 =
      2 * x * ∑ i, (f (quark (up i)) x Q2 - f (antiquark (down i)) x Q2) := by
  rw [xf3CCMinusLO_eq_of_sum_norm_sq_eq_one up down f x Q2 sum_norm_sq_one_row sum_norm_sq_one_col,
    Finset.sum_sub_distrib]

/-- **`F₂^{W⁺}` without mixing.** `F₂^{W⁺} = 2 x Σᵢ (d_i + ubar_i)`. -/
@[simp]
theorem f2CCPlusLO_one :
    f2CCPlusLO 1 up down f x Q2 =
      2 * x * ∑ i, (f (quark (down i)) x Q2 + f (antiquark (up i)) x Q2) := by
  rw [f2CCPlusLO_eq_of_sum_norm_sq_eq_one up down f x Q2 sum_norm_sq_one_row sum_norm_sq_one_col,
    Finset.sum_add_distrib]

/-- **`x F₃^{W⁺}` without mixing.** `x F₃^{W⁺} = 2 x Σᵢ (d_i - ubar_i)`. -/
@[simp]
theorem xf3CCPlusLO_one :
    xf3CCPlusLO 1 up down f x Q2 =
      2 * x * ∑ i, (f (quark (down i)) x Q2 - f (antiquark (up i)) x Q2) := by
  rw [xf3CCPlusLO_eq_of_sum_norm_sq_eq_one up down f x Q2 sum_norm_sq_one_row sum_norm_sq_one_col,
    Finset.sum_sub_distrib]

end NoMixing

variable (V)

/-!
## Quark/antiquark separation
-/

/-- **`F₂ + x F₃` sees only the quarks.** For `W⁻` absorption,
`F₂^{W⁻} + x F₃^{W⁻} = 4 x Σᵢ (Σⱼ ‖V i j‖²) u_i`. -/
theorem f2CCMinusLO_add_xf3CCMinusLO :
    f2CCMinusLO V up down f x Q2 + xf3CCMinusLO V up down f x Q2 =
      4 * x * ∑ i, (∑ j, ‖V i j‖ ^ 2) * f (quark (up i)) x Q2 := by
  rw [f2CCMinusLO_eq_sum_add_sum, xf3CCMinusLO_eq_sum_sub_sum]
  ring

/-- **`F₂ - x F₃` sees only the antiquarks.** For `W⁻` absorption,
`F₂^{W⁻} - x F₃^{W⁻} = 4 x Σⱼ (Σᵢ ‖V i j‖²) dbar_j`. -/
theorem f2CCMinusLO_sub_xf3CCMinusLO :
    f2CCMinusLO V up down f x Q2 - xf3CCMinusLO V up down f x Q2 =
      4 * x * ∑ j, (∑ i, ‖V i j‖ ^ 2) * f (antiquark (down j)) x Q2 := by
  rw [f2CCMinusLO_eq_sum_add_sum, xf3CCMinusLO_eq_sum_sub_sum]
  ring

/-- **`F₂ + x F₃` sees only the quarks.** For `W⁺` absorption,
`F₂^{W⁺} + x F₃^{W⁺} = 4 x Σⱼ (Σᵢ ‖V i j‖²) d_j`. -/
theorem f2CCPlusLO_add_xf3CCPlusLO : f2CCPlusLO V up down f x Q2 + xf3CCPlusLO V up down f x Q2 =
    4 * x * ∑ j, (∑ i, ‖V i j‖ ^ 2) * f (quark (down j)) x Q2 := by
  rw [f2CCPlusLO_eq_sum_add_sum, xf3CCPlusLO_eq_sum_sub_sum]
  ring

/-- **`F₂ - x F₃` sees only the antiquarks.** For `W⁺` absorption,
`F₂^{W⁺} - x F₃^{W⁺} = 4 x Σᵢ (Σⱼ ‖V i j‖²) ubar_i`. -/
theorem f2CCPlusLO_sub_xf3CCPlusLO : f2CCPlusLO V up down f x Q2 - xf3CCPlusLO V up down f x Q2 =
    4 * x * ∑ i, (∑ j, ‖V i j‖ ^ 2) * f (antiquark (up i)) x Q2 := by
  rw [f2CCPlusLO_eq_sum_add_sum, xf3CCPlusLO_eq_sum_sub_sum]
  ring

/-!
## Positivity
-/

variable {f x Q2}

/-- **`|x F₃^{W⁻}| ≤ F₂^{W⁻}`** for `0 ≤ x` and non-negative quark and antiquark densities in
the active channels, the up-type quarks and down-type antiquarks: the parity-odd structure function
cannot exceed the parity-even one, because `F₂ + x F₃` and `F₂ - x F₃` are both non-negative. -/
theorem abs_xf3CCMinusLO_le_f2CCMinusLO (hx : 0 ≤ x) (hq : ∀ i, 0 ≤ f (quark (up i)) x Q2)
    (hqbar : ∀ j, 0 ≤ f (antiquark (down j)) x Q2) :
    |xf3CCMinusLO V up down f x Q2| ≤ f2CCMinusLO V up down f x Q2 := by
  have hadd := f2CCMinusLO_add_xf3CCMinusLO V up down f x Q2
  have hsub := f2CCMinusLO_sub_xf3CCMinusLO V up down f x Q2
  have hquark : 0 ≤ 4 * x * ∑ i, (∑ j, ‖V i j‖ ^ 2) * f (quark (up i)) x Q2 :=
    mul_nonneg (by positivity) <| Finset.sum_nonneg fun i _ => mul_nonneg (by positivity) (hq _)
  have hantiquark : 0 ≤ 4 * x * ∑ j, (∑ i, ‖V i j‖ ^ 2) * f (antiquark (down j)) x Q2 :=
    mul_nonneg (by positivity) <| Finset.sum_nonneg fun j _ => mul_nonneg (by positivity) (hqbar _)
  rw [abs_le]
  constructor <;> linarith

/-- **`|x F₃^{W⁺}| ≤ F₂^{W⁺}`** for `0 ≤ x` and non-negative quark and antiquark densities in
the active channels, the down-type quarks and up-type antiquarks. -/
theorem abs_xf3CCPlusLO_le_f2CCPlusLO (hx : 0 ≤ x) (hq : ∀ j, 0 ≤ f (quark (down j)) x Q2)
    (hqbar : ∀ i, 0 ≤ f (antiquark (up i)) x Q2) :
    |xf3CCPlusLO V up down f x Q2| ≤ f2CCPlusLO V up down f x Q2 := by
  rw [xf3CCPlusLO_eq_neg_xf3CCMinusLO_chargeConj, abs_neg, f2CCPlusLO_eq_f2CCMinusLO_chargeConj]
  exact abs_xf3CCMinusLO_le_f2CCMinusLO V up down hx (by simpa using hqbar) (by simpa using hq)

/-- `F₂^{W⁻}` is non-negative for `0 ≤ x` and non-negative up-type quark and down-type antiquark
densities. -/
theorem f2CCMinusLO_nonneg (hx : 0 ≤ x) (hq : ∀ i, 0 ≤ f (quark (up i)) x Q2)
    (hqbar : ∀ j, 0 ≤ f (antiquark (down j)) x Q2) : 0 ≤ f2CCMinusLO V up down f x Q2 :=
  (abs_nonneg _).trans (abs_xf3CCMinusLO_le_f2CCMinusLO V up down hx hq hqbar)

/-- `F₂^{W⁺}` is non-negative for `0 ≤ x` and non-negative down-type quark and up-type antiquark
densities. -/
theorem f2CCPlusLO_nonneg (hx : 0 ≤ x) (hq : ∀ j, 0 ≤ f (quark (down j)) x Q2)
    (hqbar : ∀ i, 0 ≤ f (antiquark (up i)) x Q2) : 0 ≤ f2CCPlusLO V up down f x Q2 :=
  (abs_nonneg _).trans (abs_xf3CCPlusLO_le_f2CCPlusLO V up down hx hq hqbar)

/-!
## The sum-rule integrands
-/

variable (f x Q2)

/-- **The Adler integrand for an arbitrary mixing matrix.**
`F₂^{W⁻} - F₂^{W⁺} = 2 x (Σᵢ (Σⱼ ‖V i j‖²) (u_i - ubar_i) - Σⱼ (Σᵢ ‖V i j‖²) (d_j - dbar_j))`:
each up-type valence density is weighted by the squared norm of its row of `V`, and each
down-type one by the squared norm of its column. -/
theorem f2CCMinusLO_sub_f2CCPlusLO :
    f2CCMinusLO V up down f x Q2 - f2CCPlusLO V up down f x Q2 =
      2 * x * (∑ i, (∑ j, ‖V i j‖ ^ 2) * (f (quark (up i)) x Q2 - f (antiquark (up i)) x Q2) -
        ∑ j, (∑ i, ‖V i j‖ ^ 2) * (f (quark (down j)) x Q2 - f (antiquark (down j)) x Q2)) := by
  simp only [f2CCMinusLO_eq_sum_add_sum, f2CCPlusLO_eq_sum_add_sum, mul_sub,
    Finset.sum_sub_distrib]
  ring

/-- **The valence sum `x F₃^{W⁻} + x F₃^{W⁺}` for an arbitrary mixing matrix.**
`x F₃^{W⁻} + x F₃^{W⁺} = 2 x (Σᵢ (Σⱼ ‖V i j‖²) (u_i - ubar_i) + Σⱼ (Σᵢ ‖V i j‖²) (d_j - dbar_j))`,
with the same row and column weights as in `f2CCMinusLO_sub_f2CCPlusLO`. -/
theorem xf3CCMinusLO_add_xf3CCPlusLO :
    xf3CCMinusLO V up down f x Q2 + xf3CCPlusLO V up down f x Q2 =
      2 * x * (∑ i, (∑ j, ‖V i j‖ ^ 2) * (f (quark (up i)) x Q2 - f (antiquark (up i)) x Q2) +
        ∑ j, (∑ i, ‖V i j‖ ^ 2) * (f (quark (down j)) x Q2 - f (antiquark (down j)) x Q2)) := by
  simp only [xf3CCMinusLO_eq_sum_sub_sum, xf3CCPlusLO_eq_sum_sub_sum, mul_sub,
    Finset.sum_sub_distrib]
  ring

variable {V}

/-- **The Adler integrand.** With unit-norm rows and columns of the mixing matrix,
`F₂^{W⁻} - F₂^{W⁺} = 2 x (Σᵢ (u_i - ubar_i) - Σⱼ (d_j - dbar_j))`: a difference of valence
densities, whose `dx / x` integral is fixed by the valence content of the target. For a proton,
`F₂^{W⁻} - F₂^{W⁺} = F₂^{νbar p} - F₂^{ν p}`. -/
theorem f2CCMinusLO_sub_f2CCPlusLO_eq_of_sum_norm_sq_eq_one (hrow : ∀ i, ∑ j, ‖V i j‖ ^ 2 = 1)
    (hcol : ∀ j, ∑ i, ‖V i j‖ ^ 2 = 1) :
    f2CCMinusLO V up down f x Q2 - f2CCPlusLO V up down f x Q2 =
      2 * x * (∑ i, (f (quark (up i)) x Q2 - f (antiquark (up i)) x Q2) -
        ∑ j, (f (quark (down j)) x Q2 - f (antiquark (down j)) x Q2)) := by
  simp [f2CCMinusLO_sub_f2CCPlusLO, hrow, hcol]

/-- **The valence sum `x F₃^{W⁻} + x F₃^{W⁺}`.** With unit-norm rows and columns of the mixing
matrix, `x F₃^{W⁻} + x F₃^{W⁺} = 2 x (Σᵢ (u_i - ubar_i) + Σⱼ (d_j - dbar_j))`, the sum of the
valence densities of all the active flavours. For a proton this is
`x F₃^{νbar p} + x F₃^{ν p}`. -/
theorem xf3CCMinusLO_add_xf3CCPlusLO_eq_of_sum_norm_sq_eq_one (hrow : ∀ i, ∑ j, ‖V i j‖ ^ 2 = 1)
    (hcol : ∀ j, ∑ i, ‖V i j‖ ^ 2 = 1) :
    xf3CCMinusLO V up down f x Q2 + xf3CCPlusLO V up down f x Q2 =
      2 * x * (∑ i, (f (quark (up i)) x Q2 - f (antiquark (up i)) x Q2) +
        ∑ j, (f (quark (down j)) x Q2 - f (antiquark (down j)) x Q2)) := by
  simp [xf3CCMinusLO_add_xf3CCPlusLO, hrow, hcol]

/-!
## The flavour-blind limit
-/

/-- **Charged and neutral currents agree in the flavour-blind limit.** If the up-type and
down-type flavours together are all the flavours, each exactly once, and the rows and columns of
the mixing matrix have unit norm, then the average of `F₂^{W⁻}` and `F₂^{W⁺}` is the
neutral-current `F₂ = x Σ_f e_f² (q_f + qbar_f)` with every charge `e_f = 1`. -/
theorem f2CCMinusLO_add_f2CCPlusLO_eq_two_mul_f2LO [Fintype Flavor]
    (hbij : Function.Bijective (Sum.elim up down)) (hrow : ∀ i, ∑ j, ‖V i j‖ ^ 2 = 1)
    (hcol : ∀ j, ∑ i, ‖V i j‖ ^ 2 = 1) :
    f2CCMinusLO V up down f x Q2 + f2CCPlusLO V up down f x Q2 =
      2 * f2LO (fun _ => 1) (fun a x Q2 => f (quark a) x Q2 + f (antiquark a) x Q2) x Q2 := by
  have hsum := (Equiv.ofBijective _ hbij).sum_comp
    (fun a => f (quark a) x Q2 + f (antiquark a) x Q2)
  simp only [Fintype.sum_sum_type, Equiv.ofBijective_apply, Sum.elim_inl, Sum.elim_inr] at hsum
  rw [f2CCMinusLO_eq_of_sum_norm_sq_eq_one up down f x Q2 hrow hcol,
    f2CCPlusLO_eq_of_sum_norm_sq_eq_one up down f x Q2 hrow hcol, f2LO_def]
  simp only [one_pow, one_mul]
  rw [← hsum, Finset.sum_add_distrib, Finset.sum_add_distrib]
  ring

end DIS
end Scattering
end QFT
end EpsilonEridani
