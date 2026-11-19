/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.QFT.Factorization.Convolution.Double
public import EpsilonEridani.QFT.Scattering.DIS.SIDIS.Basic

/-!
# Semi-inclusive coefficient functions and the double convolution

In collinear factorization of semi-inclusive deep-inelastic scattering at large hadron transverse
momentum, a structure function is a double convolution
```
F (x, z) = ∑_{i, j} ∫_x^1 (dy / y) ∫_z^1 (dw / w) C_{ij} (y, w) f_i (x / y) D_j (z / w)
```
of the parton density `f_i` of the struck parton, the fragmentation function `D_j` of the
fragmenting parton and a coefficient function `C_{ij}`. The coefficient function is not a function:
at leading order it is `e_i² δ_{ij} δ(1 - y) δ(1 - w)`, and beyond leading order it contains
`δ(1 - y)` and `δ(1 - w)` times functions of the other variable.

This file records a coefficient function in the form
```
C (y, w) = c δ(1 - y) δ(1 - w) + δ(1 - y) a (w) + b (y) δ(1 - w) + R (y, w)
```
(`SIDIS.CoefficientFunction`), defines its double convolution with a density and a fragmentation
function through `Convolution.mellinConv` and `Convolution.doubleMellinConv`, and proves:

* the decomposition of the double convolution into the contributions of the four components
  (`CoefficientFunction.doubleConv_eq_add`);
* the transposition symmetry: exchanging the two densities is a symmetry once the coefficient
  function is transposed, provided the integrand of the regular part is jointly integrable on
  `[x, 1] × [z, 1]` (`CoefficientFunction.doubleConv_transpose`), and the exchange without the
  transposition is not a symmetry (`CoefficientFunction.exists_doubleConv_ne`);
* the leading-order reduction: for the flavour-diagonal coefficient functions
  `c_i δ_{ij} δ(1 - y) δ(1 - w)`, at leading order with `c_i = e_i²`, the double convolution is
  `∑ᵢ c_i f_i (x) D_i (z)` (`doubleConvStructureFunction_diagonal_ofDeltaDelta`);
* compatibility with `EpsilonEridani.QFT.Scattering.DIS.SIDIS.sidisStructureFunction` in the
  fragmentation variable only: for the coefficient function `δ_{ij} b_i (y) δ(1 - w)`, with `b_i`
  the coefficient function of a collinear hard kernel, the double convolution is
  `sidisStructureFunction` (`doubleConvStructureFunction_diagonal_ofRegularDelta`, from the
  single-channel `CoefficientFunction.doubleConv_ofRegularDelta_eq_sidisChannel`).

The leading-order coefficient function, with delta functions in both variables, is not related to
`sidisStructureFunction` here, and cannot be while `Factorization.DIS.HardKernel` is a function
type: the parton side of `sidisStructureFunction` is the convolution `Factorization.DIS.loChannel`
with a function kernel, and `δ(1 - y)` is not such a kernel, since `mellinConv` has no unit
(`Convolution.not_exists_forall_mellinConv_ae_eq`). That statement needs a distributional
hard-kernel interface first.

The delta functions act as the unit of the Mellin convolution, that is, as the restriction of a
density to `(0,1]`. Plus distributions in either variable, which the next-to-leading-order
coefficient functions also contain, are not part of `SIDIS.CoefficientFunction`. As for the
densities, whose support in `[0, 1]` is a hypothesis and not part of their type, only the values
of the component functions on `(0,1]` enter the double convolution
(`CoefficientFunction.doubleConv_congr_of_eqOn`).

## Main definitions

* `SIDIS.CoefficientFunction`: a coefficient function with delta parts at `y = 1` and `w = 1`.
* `SIDIS.CoefficientFunction.transpose`: the transposed coefficient function `C (w, y)`.
* `SIDIS.CoefficientFunction.doubleConv`: its double convolution with two densities.
* `SIDIS.CoefficientFunction.ofDeltaDelta`, `SIDIS.CoefficientFunction.ofDeltaRegular`,
  `SIDIS.CoefficientFunction.ofRegularDelta`, `SIDIS.CoefficientFunction.ofRegular`: the
  coefficient functions `c δ(1 - y) δ(1 - w)`, `δ(1 - y) a (w)`, `b (y) δ(1 - w)` and `R (y, w)`.
* `SIDIS.doubleConvStructureFunction`: the flavour-summed double convolution.

## References

* G. Altarelli, R. K. Ellis, G. Martinelli and S.-Y. Pi, *Processes involving fragmentation
  functions beyond the leading order in QCD*, Nucl. Phys. B 160 (1979) 301.
* D. de Florian, M. Stratmann and W. Vogelsang, *QCD analysis of unpolarized and polarized
  Λ-baryon production in leading and next-to-leading order*, Phys. Rev. D 57 (1998) 5811.
-/

public section

noncomputable section

open MeasureTheory Set
open EpsilonEridani.QFT.Factorization.Convolution

namespace EpsilonEridani
namespace QFT
namespace Factorization
namespace SIDIS

/-- A semi-inclusive coefficient function on the unit square in the form
`c δ(1 - y) δ(1 - w) + δ(1 - y) a (w) + b (y) δ(1 - w) + R (y, w)`, where `y` is the momentum
fraction conjugate to the parton density and `w` the one conjugate to the fragmentation function. -/
@[ext]
structure CoefficientFunction where
  /-- The coefficient `c` of `δ(1 - y) δ(1 - w)`. -/
  deltaDelta : ℝ
  /-- The function `a (w)` multiplying `δ(1 - y)`. -/
  deltaRegular : ℝ → ℝ
  /-- The function `b (y)` multiplying `δ(1 - w)`. -/
  regularDelta : ℝ → ℝ
  /-- The regular part `R (y, w)`. -/
  regular : ℝ → ℝ → ℝ

namespace CoefficientFunction

instance : Zero CoefficientFunction := ⟨⟨0, 0, 0, 0⟩⟩

@[simp]
theorem zero_deltaDelta : (0 : CoefficientFunction).deltaDelta = 0 := (rfl)

@[simp]
theorem zero_deltaRegular : (0 : CoefficientFunction).deltaRegular = 0 := (rfl)

@[simp]
theorem zero_regularDelta : (0 : CoefficientFunction).regularDelta = 0 := (rfl)

@[simp]
theorem zero_regular : (0 : CoefficientFunction).regular = 0 := (rfl)

/-! ### Transposition -/

/-- The transposed coefficient function `(y, w) ↦ C (w, y)`: it exchanges `δ(1 - y) a (w)` with
`a (y) δ(1 - w)` and transposes the regular part. -/
def transpose (C : CoefficientFunction) : CoefficientFunction :=
  ⟨C.deltaDelta, C.regularDelta, C.deltaRegular, Function.swap C.regular⟩

@[simp]
theorem transpose_deltaDelta (C : CoefficientFunction) :
    C.transpose.deltaDelta = C.deltaDelta := (rfl)

@[simp]
theorem transpose_deltaRegular (C : CoefficientFunction) :
    C.transpose.deltaRegular = C.regularDelta := (rfl)

@[simp]
theorem transpose_regularDelta (C : CoefficientFunction) :
    C.transpose.regularDelta = C.deltaRegular := (rfl)

@[simp]
theorem transpose_regular (C : CoefficientFunction) :
    C.transpose.regular = Function.swap C.regular := (rfl)

@[simp]
theorem transpose_transpose (C : CoefficientFunction) : C.transpose.transpose = C := (rfl)

@[simp]
theorem transpose_zero : (0 : CoefficientFunction).transpose = 0 := (rfl)

/-! ### The double convolution -/

/-- The double convolution of a coefficient function `C` with a density `f` in the first variable
and a density `D` in the second:
`c f (x) D (z) + f (x) (a ⊗ D) (z) + (b ⊗ f) (x) D (z) + (f ⊗ R ⊗ D) (x, z)`, with `⊗` the Mellin
convolution `Convolution.mellinConv`. Each delta function acts as the unit of the Mellin
convolution, the restriction of the density to `(0,1]`. -/
def doubleConv (C : CoefficientFunction) (f D : ℝ → ℝ) (x z : ℝ) : ℝ :=
  C.deltaDelta * (Ioc (0 : ℝ) 1).indicator f x * (Ioc (0 : ℝ) 1).indicator D z +
    (Ioc (0 : ℝ) 1).indicator f x * mellinConv C.deltaRegular D z +
    mellinConv C.regularDelta f x * (Ioc (0 : ℝ) 1).indicator D z +
    doubleMellinConv C.regular f D x z

/-- Unfolding lemma for `CoefficientFunction.doubleConv`. -/
theorem doubleConv_def (C : CoefficientFunction) (f D : ℝ → ℝ) (x z : ℝ) :
    C.doubleConv f D x z =
      C.deltaDelta * (Ioc (0 : ℝ) 1).indicator f x * (Ioc (0 : ℝ) 1).indicator D z +
        (Ioc (0 : ℝ) 1).indicator f x * mellinConv C.deltaRegular D z +
        mellinConv C.regularDelta f x * (Ioc (0 : ℝ) 1).indicator D z +
        doubleMellinConv C.regular f D x z :=
  (rfl)

/-- The double convolution on `(0,1]²`. -/
theorem doubleConv_apply_of_mem (C : CoefficientFunction) (f D : ℝ → ℝ) {x z : ℝ}
    (hx : x ∈ Ioc (0 : ℝ) 1) (hz : z ∈ Ioc (0 : ℝ) 1) :
    C.doubleConv f D x z =
      C.deltaDelta * f x * D z + f x * mellinConv C.deltaRegular D z +
        mellinConv C.regularDelta f x * D z + doubleMellinConv C.regular f D x z := by
  rw [doubleConv_def, indicator_of_mem hx, indicator_of_mem hz]

/-- The double convolution depends only on the values of the components on `(0,1]` and `(0,1]²`
and of the densities on `(0,1]`. -/
theorem doubleConv_congr_of_eqOn {C C' : CoefficientFunction} {f f' D D' : ℝ → ℝ}
    (hdd : C.deltaDelta = C'.deltaDelta)
    (hdr : EqOn C.deltaRegular C'.deltaRegular (Ioc (0 : ℝ) 1))
    (hrd : EqOn C.regularDelta C'.regularDelta (Ioc (0 : ℝ) 1))
    (hr : EqOn (Function.uncurry C.regular) (Function.uncurry C'.regular)
      (Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1))
    (hf : EqOn f f' (Ioc (0 : ℝ) 1)) (hD : EqOn D D' (Ioc (0 : ℝ) 1)) :
    C.doubleConv f D = C'.doubleConv f' D' := by
  funext x z
  rw [doubleConv_def, doubleConv_def, hdd, mellinConv_congr_of_eqOn hdr hD,
    mellinConv_congr_of_eqOn hrd hf, doubleMellinConv_congr_of_eqOn hr hf hD,
    indicator_congr hf, indicator_congr hD]

/-- The double convolution vanishes when the first momentum fraction lies outside `(0,1]`. -/
theorem doubleConv_apply_eq_zero_of_notMem_left (C : CoefficientFunction) (f D : ℝ → ℝ) {x : ℝ}
    (hx : x ∉ Ioc (0 : ℝ) 1) (z : ℝ) : C.doubleConv f D x z = 0 := by
  rw [doubleConv_def, indicator_of_notMem hx, mellinConv_apply_eq_zero_of_notMem _ _ hx,
    doubleMellinConv_apply_eq_zero_of_notMem_left _ _ _ hx]
  ring

/-- The double convolution vanishes when the second momentum fraction lies outside `(0,1]`. -/
theorem doubleConv_apply_eq_zero_of_notMem_right (C : CoefficientFunction) (f D : ℝ → ℝ) (x : ℝ)
    {z : ℝ} (hz : z ∉ Ioc (0 : ℝ) 1) : C.doubleConv f D x z = 0 := by
  rw [doubleConv_def, indicator_of_notMem hz, mellinConv_apply_eq_zero_of_notMem _ _ hz,
    doubleMellinConv_apply_eq_zero_of_notMem_right _ _ _ _ hz]
  ring

/-- The double convolution with the zero coefficient function vanishes. -/
@[simp]
theorem doubleConv_zero (f D : ℝ → ℝ) : (0 : CoefficientFunction).doubleConv f D = 0 := by
  funext x z
  simp [doubleConv_def]

/-- The double convolution with the zero density in the first variable vanishes. -/
@[simp]
theorem doubleConv_zero_density_left (C : CoefficientFunction) (D : ℝ → ℝ) :
    C.doubleConv 0 D = 0 := by
  funext x z
  simp [doubleConv_def]

/-- The double convolution with the zero density in the second variable vanishes. -/
@[simp]
theorem doubleConv_zero_density_right (C : CoefficientFunction) (f : ℝ → ℝ) :
    C.doubleConv f 0 = 0 := by
  funext x z
  simp [doubleConv_def]

/-- **Exchanging the densities transposes the coefficient function.** The double convolution of
`C` with `f` in `x` and `D` in `z` equals that of the transposed coefficient function with `D` in
the first variable and `f` in the second, at `(z, x)`, provided the integrand of the regular part
is jointly integrable on `[x, 1] × [z, 1]`. -/
theorem doubleConv_transpose (C : CoefficientFunction) (f D : ℝ → ℝ) {x z : ℝ}
    (h : x ∈ Ioc (0 : ℝ) 1 → z ∈ Ioc (0 : ℝ) 1 →
      IntegrableOn
        (fun p : ℝ × ℝ => C.regular p.1 p.2 * (f (x / p.1) / p.1) * (D (z / p.2) / p.2))
        (Icc x 1 ×ˢ Icc z 1)) :
    C.transpose.doubleConv D f z x = C.doubleConv f D x z := by
  rw [doubleConv_def, doubleConv_def, transpose_regular, doubleMellinConv_swap _ _ _ h]
  simp only [transpose_deltaDelta, transpose_deltaRegular, transpose_regularDelta]
  ring

/-! ### The coefficient functions with a single component -/

/-- The coefficient function `c δ(1 - y) δ(1 - w)`. With `c = e_i²` it is the leading-order
coefficient function of a quark flavour `i`. -/
def ofDeltaDelta (c : ℝ) : CoefficientFunction := ⟨c, 0, 0, 0⟩

@[simp]
theorem ofDeltaDelta_deltaDelta (c : ℝ) : (ofDeltaDelta c).deltaDelta = c := (rfl)

@[simp]
theorem ofDeltaDelta_deltaRegular (c : ℝ) : (ofDeltaDelta c).deltaRegular = 0 := (rfl)

@[simp]
theorem ofDeltaDelta_regularDelta (c : ℝ) : (ofDeltaDelta c).regularDelta = 0 := (rfl)

@[simp]
theorem ofDeltaDelta_regular (c : ℝ) : (ofDeltaDelta c).regular = 0 := (rfl)

/-- The coefficient function `c δ(1 - y) δ(1 - w)` is symmetric. -/
@[simp]
theorem transpose_ofDeltaDelta (c : ℝ) : (ofDeltaDelta c).transpose = ofDeltaDelta c := (rfl)

/-- The double convolution with `c δ(1 - y) δ(1 - w)` multiplies the two densities, restricted
to `(0,1]`, at the same momentum fractions. -/
@[simp]
theorem doubleConv_ofDeltaDelta (c : ℝ) (f D : ℝ → ℝ) (x z : ℝ) :
    (ofDeltaDelta c).doubleConv f D x z =
      c * (Ioc (0 : ℝ) 1).indicator f x * (Ioc (0 : ℝ) 1).indicator D z := by
  simp [doubleConv_def]

/-- **The leading-order double convolution.** The coefficient function `c δ(1 - y) δ(1 - w)`
multiplies the two densities at the same momentum fractions: `c f (x) D (z)` on `(0,1]²`. -/
theorem doubleConv_ofDeltaDelta_of_mem (c : ℝ) (f D : ℝ → ℝ) {x z : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1)
    (hz : z ∈ Ioc (0 : ℝ) 1) : (ofDeltaDelta c).doubleConv f D x z = c * f x * D z := by
  rw [doubleConv_ofDeltaDelta, indicator_of_mem hx, indicator_of_mem hz]

/-- The coefficient function `δ(1 - y) a (w)`: a coefficient function `a` in the momentum fraction
conjugate to the fragmentation function, concentrated at `y = 1` in the parton variable. -/
def ofDeltaRegular (a : ℝ → ℝ) : CoefficientFunction := ⟨0, a, 0, 0⟩

@[simp]
theorem ofDeltaRegular_deltaDelta (a : ℝ → ℝ) : (ofDeltaRegular a).deltaDelta = 0 := (rfl)

@[simp]
theorem ofDeltaRegular_deltaRegular (a : ℝ → ℝ) : (ofDeltaRegular a).deltaRegular = a := (rfl)

@[simp]
theorem ofDeltaRegular_regularDelta (a : ℝ → ℝ) : (ofDeltaRegular a).regularDelta = 0 := (rfl)

@[simp]
theorem ofDeltaRegular_regular (a : ℝ → ℝ) : (ofDeltaRegular a).regular = 0 := (rfl)

/-- The double convolution with `δ(1 - y) a (w)` is the parton density at `x`, restricted to
`(0,1]`, times the Mellin convolution of `a` with the fragmentation density in `z`. -/
@[simp]
theorem doubleConv_ofDeltaRegular (a f D : ℝ → ℝ) (x z : ℝ) :
    (ofDeltaRegular a).doubleConv f D x z = (Ioc (0 : ℝ) 1).indicator f x * mellinConv a D z := by
  simp [doubleConv_def]

/-- The double convolution with `δ(1 - y) a (w)` is the parton density at `x` times the Mellin
convolution of `a` with the fragmentation density in `z`, for `x ∈ (0,1]`. -/
theorem doubleConv_ofDeltaRegular_of_mem (a f D : ℝ → ℝ) {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1)
    (z : ℝ) : (ofDeltaRegular a).doubleConv f D x z = f x * mellinConv a D z := by
  rw [doubleConv_ofDeltaRegular, indicator_of_mem hx]

/-- The coefficient function `b (y) δ(1 - w)`: a coefficient function `b` in the momentum fraction
conjugate to the parton density, concentrated at `w = 1` in the fragmentation variable. -/
def ofRegularDelta (b : ℝ → ℝ) : CoefficientFunction := ⟨0, 0, b, 0⟩

@[simp]
theorem ofRegularDelta_deltaDelta (b : ℝ → ℝ) : (ofRegularDelta b).deltaDelta = 0 := (rfl)

@[simp]
theorem ofRegularDelta_deltaRegular (b : ℝ → ℝ) : (ofRegularDelta b).deltaRegular = 0 := (rfl)

@[simp]
theorem ofRegularDelta_regularDelta (b : ℝ → ℝ) : (ofRegularDelta b).regularDelta = b := (rfl)

@[simp]
theorem ofRegularDelta_regular (b : ℝ → ℝ) : (ofRegularDelta b).regular = 0 := (rfl)

/-- The double convolution with `b (y) δ(1 - w)` is the Mellin convolution of `b` with the
density in `x`, times the fragmentation density at `z` restricted to `(0,1]`. -/
@[simp]
theorem doubleConv_ofRegularDelta (b f D : ℝ → ℝ) (x z : ℝ) :
    (ofRegularDelta b).doubleConv f D x z = mellinConv b f x * (Ioc (0 : ℝ) 1).indicator D z := by
  simp [doubleConv_def]

/-- The double convolution with `b (y) δ(1 - w)` is the Mellin convolution of `b` with the
density in `x`, times the fragmentation density at `z`, for `z ∈ (0,1]`. -/
theorem doubleConv_ofRegularDelta_of_mem (b f D : ℝ → ℝ) (x : ℝ) {z : ℝ}
    (hz : z ∈ Ioc (0 : ℝ) 1) : (ofRegularDelta b).doubleConv f D x z = mellinConv b f x * D z := by
  rw [doubleConv_ofRegularDelta, indicator_of_mem hz]

/-- The double convolution with `b (y) δ(1 - w)` against a collinear kernel `K` with coefficient
function `b`: the collinear convolution `convolveAt K` of the density in `x`, times the
fragmentation density at `z`, on `(0,1]²`. -/
theorem doubleConv_ofRegularDelta_eq_convolveAt {K : Kernel} {b : ℝ → ℝ}
    (hK : IsCollinearKernel K b) (f D : ℝ → ℝ) {x z : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1)
    (hz : z ∈ Ioc (0 : ℝ) 1) : (ofRegularDelta b).doubleConv f D x z = convolveAt K f x * D z := by
  rw [doubleConv_ofRegularDelta_of_mem _ _ _ _ hz, hK.convolveAt_eq_mellinConv _ hx]

/-- Transposition exchanges `b (y) δ(1 - w)` with `δ(1 - y) b (w)`. -/
@[simp]
theorem transpose_ofRegularDelta (b : ℝ → ℝ) :
    (ofRegularDelta b).transpose = ofDeltaRegular b := (rfl)

/-- Transposition exchanges `δ(1 - y) a (w)` with `a (y) δ(1 - w)`. -/
@[simp]
theorem transpose_ofDeltaRegular (a : ℝ → ℝ) :
    (ofDeltaRegular a).transpose = ofRegularDelta a := (rfl)

/-- The coefficient function with only a regular part `R (y, w)`. -/
def ofRegular (R : ℝ → ℝ → ℝ) : CoefficientFunction := ⟨0, 0, 0, R⟩

@[simp]
theorem ofRegular_deltaDelta (R : ℝ → ℝ → ℝ) : (ofRegular R).deltaDelta = 0 := (rfl)

@[simp]
theorem ofRegular_deltaRegular (R : ℝ → ℝ → ℝ) : (ofRegular R).deltaRegular = 0 := (rfl)

@[simp]
theorem ofRegular_regularDelta (R : ℝ → ℝ → ℝ) : (ofRegular R).regularDelta = 0 := (rfl)

@[simp]
theorem ofRegular_regular (R : ℝ → ℝ → ℝ) : (ofRegular R).regular = R := (rfl)

/-- The double convolution with a purely regular coefficient function is the double Mellin
convolution. -/
@[simp]
theorem doubleConv_ofRegular (R : ℝ → ℝ → ℝ) (f D : ℝ → ℝ) :
    (ofRegular R).doubleConv f D = doubleMellinConv R f D := by
  funext x z
  simp [doubleConv_def]

/-- **The decomposition of the double convolution** into the contributions of the four
components `c δ(1 - y) δ(1 - w)`, `δ(1 - y) a (w)`, `b (y) δ(1 - w)` and `R (y, w)`. -/
theorem doubleConv_eq_add (C : CoefficientFunction) (f D : ℝ → ℝ) (x z : ℝ) :
    C.doubleConv f D x z =
      (ofDeltaDelta C.deltaDelta).doubleConv f D x z +
        (ofDeltaRegular C.deltaRegular).doubleConv f D x z +
        (ofRegularDelta C.regularDelta).doubleConv f D x z +
        (ofRegular C.regular).doubleConv f D x z := by
  simp [doubleConv_def]

/-- Transposition of a purely regular coefficient function transposes its regular part. -/
@[simp]
theorem transpose_ofRegular (R : ℝ → ℝ → ℝ) :
    (ofRegular R).transpose = ofRegular (Function.swap R) := (rfl)

/-- **Exchanging the densities without transposing is not a symmetry**: some coefficient
function, already one with only a regular part, has a double convolution that changes when the
two densities and the two momentum fractions are exchanged. -/
theorem exists_doubleConv_ne :
    ∃ (C : CoefficientFunction) (f D : ℝ → ℝ) (x z : ℝ),
      C.doubleConv D f z x ≠ C.doubleConv f D x z := by
  obtain ⟨R, f, D, x, z, h⟩ := exists_doubleMellinConv_ne
  exact ⟨ofRegular R, f, D, x, z, by rwa [doubleConv_ofRegular, doubleConv_ofRegular]⟩

end CoefficientFunction

/-! ### The flavour-summed structure function -/

variable {Flavor Hadron : Type}

/-- The semi-inclusive structure function in collinear factorization: the flavour sum
`∑_{i, j} (f_i ⊗ C_{ij} ⊗ D_j) (x, z)` of the double convolutions of the parton densities `f_i` at
the scale `Q2`, the coefficient functions `C_{ij}` at that scale, and the fragmentation functions
`D_j` of the fragmenting parton `j` into the hadron `h`. -/
def doubleConvStructureFunction [Fintype Flavor] (C : Flavor → Flavor → ℝ → CoefficientFunction)
    (f : Particles.Parton.PDF.Pdf Flavor) (D : Particles.Fragmentation.Frag Hadron Flavor)
    (h : Hadron) (x z Q2 : ℝ) : ℝ :=
  ∑ i, ∑ j, (C i j Q2).doubleConv (fun y => f i y Q2) (fun y => D h j y Q2) x z

/-- Unfolding lemma for `SIDIS.doubleConvStructureFunction`. -/
theorem doubleConvStructureFunction_def [Fintype Flavor]
    (C : Flavor → Flavor → ℝ → CoefficientFunction)
    (f : Particles.Parton.PDF.Pdf Flavor) (D : Particles.Fragmentation.Frag Hadron Flavor)
    (h : Hadron) (x z Q2 : ℝ) :
    doubleConvStructureFunction C f D h x z Q2 =
      ∑ i, ∑ j, (C i j Q2).doubleConv (fun y => f i y Q2) (fun y => D h j y Q2) x z :=
  (rfl)

/-- The structure function vanishes when the first momentum fraction lies outside `(0,1]`. -/
theorem doubleConvStructureFunction_apply_eq_zero_of_notMem_left [Fintype Flavor]
    (C : Flavor → Flavor → ℝ → CoefficientFunction) (f : Particles.Parton.PDF.Pdf Flavor)
    (D : Particles.Fragmentation.Frag Hadron Flavor) (h : Hadron) {x : ℝ}
    (hx : x ∉ Ioc (0 : ℝ) 1) (z Q2 : ℝ) : doubleConvStructureFunction C f D h x z Q2 = 0 := by
  rw [doubleConvStructureFunction_def]
  exact Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ =>
    CoefficientFunction.doubleConv_apply_eq_zero_of_notMem_left _ _ _ hx _

/-- The structure function vanishes when the second momentum fraction lies outside `(0,1]`. -/
theorem doubleConvStructureFunction_apply_eq_zero_of_notMem_right [Fintype Flavor]
    (C : Flavor → Flavor → ℝ → CoefficientFunction) (f : Particles.Parton.PDF.Pdf Flavor)
    (D : Particles.Fragmentation.Frag Hadron Flavor) (h : Hadron) (x : ℝ) {z : ℝ}
    (hz : z ∉ Ioc (0 : ℝ) 1) (Q2 : ℝ) : doubleConvStructureFunction C f D h x z Q2 = 0 := by
  rw [doubleConvStructureFunction_def]
  exact Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ =>
    CoefficientFunction.doubleConv_apply_eq_zero_of_notMem_right _ _ _ _ hz

/-- For a coefficient function diagonal in flavour at the scale `Q2`, the structure function is a
single flavour sum. -/
theorem doubleConvStructureFunction_diagonal [Fintype Flavor]
    (C : Flavor → Flavor → ℝ → CoefficientFunction) (f : Particles.Parton.PDF.Pdf Flavor)
    (D : Particles.Fragmentation.Frag Hadron Flavor) (h : Hadron) (x z : ℝ) {Q2 : ℝ}
    (hC : ∀ i j, i ≠ j → C i j Q2 = 0) :
    doubleConvStructureFunction C f D h x z Q2 =
      ∑ i, (C i i Q2).doubleConv (fun y => f i y Q2) (fun y => D h i y Q2) x z := by
  rw [doubleConvStructureFunction_def]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i (fun j _ hji => by simp [hC i j (Ne.symm hji)])
    (fun hi => absurd (Finset.mem_univ i) hi)]

/-- **The leading-order structure function.** For a coefficient function diagonal in flavour at
the scale `Q2`, with diagonal entries `c_i δ(1 - y) δ(1 - w)` (at leading order `c_i = e_i²`, with
`e_i` the charge of flavour `i`), the structure function is `∑ᵢ c_i f_i (x) D_i (z)` on `(0,1]²`. -/
theorem doubleConvStructureFunction_diagonal_ofDeltaDelta [Fintype Flavor]
    (C : Flavor → Flavor → ℝ → CoefficientFunction) (c : Flavor → ℝ)
    (f : Particles.Parton.PDF.Pdf Flavor) (D : Particles.Fragmentation.Frag Hadron Flavor)
    (h : Hadron) {x z Q2 : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1) (hz : z ∈ Ioc (0 : ℝ) 1)
    (hC : ∀ i j, i ≠ j → C i j Q2 = 0)
    (hc : ∀ i, C i i Q2 = CoefficientFunction.ofDeltaDelta (c i)) :
    doubleConvStructureFunction C f D h x z Q2 = ∑ i, c i * f i x Q2 * D h i z Q2 := by
  rw [doubleConvStructureFunction_diagonal C f D h x z hC]
  exact Finset.sum_congr rfl fun i _ => by
    rw [hc i, CoefficientFunction.doubleConv_ofDeltaDelta_of_mem _ _ _ hx hz]

/-- **Compatibility with `sidisStructureFunction` in a single channel.** If the hard kernel `C'`
of `EpsilonEridani.QFT.Scattering.DIS.SIDIS.sidisStructureFunction` is, at the scale `Q2` and for
the flavour `i`, the collinear kernel of the coefficient function `b`, then the channel
`sidisChannel` is the double convolution with `b (y) δ(1 - w)` on `(0,1]²`. -/
theorem CoefficientFunction.doubleConv_ofRegularDelta_eq_sidisChannel
    (C' : DIS.HardKernel Flavor) (b : ℝ → ℝ) (i : Flavor) {Q2 : ℝ}
    (hc : Convolution.IsCollinearKernel (fun x' z => C' i x' z Q2) b)
    (f : Particles.Parton.PDF.Pdf Flavor) (D : Particles.Fragmentation.Frag Hadron Flavor)
    (h : Hadron) {x z : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1) (hz : z ∈ Ioc (0 : ℝ) 1) :
    (ofRegularDelta b).doubleConv (fun y => f i y Q2) (fun y => D h i y Q2) x z =
      Scattering.DIS.SIDIS.sidisChannel C' f D h i x z Q2 := by
  rw [doubleConv_ofRegularDelta_eq_convolveAt hc _ _ hx hz, Scattering.DIS.SIDIS.sidisChannel,
    DIS.loChannel]

/-- **Compatibility with `sidisStructureFunction` in the fragmentation variable.** If the hard
kernel `C'` of `EpsilonEridani.QFT.Scattering.DIS.SIDIS.sidisStructureFunction` is, at the scale
`Q2`, the collinear kernel of the coefficient function `b i` for every flavour `i`, then
`sidisStructureFunction` is the double convolution with a coefficient function diagonal in
flavour at `Q2`, with diagonal entries `b_i (y) δ(1 - w)`, on `(0,1]²`. -/
theorem doubleConvStructureFunction_diagonal_ofRegularDelta [Fintype Flavor]
    (C' : DIS.HardKernel Flavor) (b : Flavor → ℝ → ℝ) {Q2 : ℝ}
    (hc : ∀ i, Convolution.IsCollinearKernel (fun x' z => C' i x' z Q2) (b i))
    (C : Flavor → Flavor → ℝ → CoefficientFunction) (hC : ∀ i j, i ≠ j → C i j Q2 = 0)
    (hCc : ∀ i, C i i Q2 = CoefficientFunction.ofRegularDelta (b i))
    (f : Particles.Parton.PDF.Pdf Flavor) (D : Particles.Fragmentation.Frag Hadron Flavor)
    (h : Hadron) {x z : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1) (hz : z ∈ Ioc (0 : ℝ) 1) :
    doubleConvStructureFunction C f D h x z Q2 =
      Scattering.DIS.SIDIS.sidisStructureFunction C' f D h x z Q2 := by
  rw [doubleConvStructureFunction_diagonal C f D h x z hC,
    Scattering.DIS.SIDIS.sidisStructureFunction]
  exact Finset.sum_congr rfl fun i _ => by
    rw [hCc i]
    exact CoefficientFunction.doubleConv_ofRegularDelta_eq_sidisChannel C' (b i) i (hc i) f D h
      hx hz

end SIDIS
end Factorization
end QFT
end EpsilonEridani
