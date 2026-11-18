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
(`SIDIS.Coefficient`), defines its double convolution with a density and a fragmentation function
through `Convolution.mellinConv` and `Convolution.doubleMellinConv`, and proves:

* the transposition symmetry: exchanging the two densities is a symmetry once the coefficient
  function is transposed (`Coefficient.doubleConv_transpose`), and the exchange without the
  transposition is not a symmetry (`Coefficient.exists_doubleConv_ne`);
* the leading-order reduction: for the coefficient functions `e_i δ_{ij} δ(1 - y) δ(1 - w)`, with
  `e_i` the squared charge of flavour `i`, the double convolution is `∑ᵢ e_i f_i (x) D_i (z)`
  (`structureFunction_delta`);
* compatibility with `EpsilonEridani.QFT.Scattering.DIS.SIDIS.sidisStructureFunction`: for the
  coefficient function `δ_{ij} c_i (y) δ(1 - w)`, with `c_i` the coefficient function of a
  collinear hard kernel, the double convolution is `sidisStructureFunction`
  (`structureFunction_ofRegularDelta`).

The delta functions act as the unit of the Mellin convolution, that is, as the restriction of a
density to `(0,1]`. Plus distributions in either variable, which the next-to-leading-order
coefficient functions also contain, are not part of `SIDIS.Coefficient`. As for the densities,
whose support in `[0, 1]` is a hypothesis and not part of their type, only the values of the
component functions on `(0,1]` enter the double convolution.

## Main definitions

* `SIDIS.Coefficient`: a coefficient function with delta parts at `y = 1` and `w = 1`.
* `SIDIS.Coefficient.transpose`: the transposed coefficient function `C (w, y)`.
* `SIDIS.Coefficient.doubleConv`: its double convolution with two densities.
* `SIDIS.Coefficient.delta`, `SIDIS.Coefficient.ofRegularDelta`: the coefficient functions
  `c δ(1 - y) δ(1 - w)` and `b (y) δ(1 - w)`.
* `SIDIS.structureFunction`: the flavour-summed double convolution.

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
structure Coefficient where
  /-- The coefficient `c` of `δ(1 - y) δ(1 - w)`. -/
  deltaDelta : ℝ
  /-- The function `a (w)` multiplying `δ(1 - y)`. -/
  deltaRegular : ℝ → ℝ
  /-- The function `b (y)` multiplying `δ(1 - w)`. -/
  regularDelta : ℝ → ℝ
  /-- The regular part `R (y, w)`. -/
  regular : ℝ → ℝ → ℝ

namespace Coefficient

instance : Zero Coefficient := ⟨⟨0, 0, 0, 0⟩⟩

@[simp]
theorem zero_deltaDelta : (0 : Coefficient).deltaDelta = 0 := (rfl)

@[simp]
theorem zero_deltaRegular : (0 : Coefficient).deltaRegular = 0 := (rfl)

@[simp]
theorem zero_regularDelta : (0 : Coefficient).regularDelta = 0 := (rfl)

@[simp]
theorem zero_regular : (0 : Coefficient).regular = 0 := (rfl)

/-! ### Transposition -/

/-- The transposed coefficient function `(y, w) ↦ C (w, y)`: it exchanges `δ(1 - y) a (w)` with
`a (y) δ(1 - w)` and transposes the regular part. -/
def transpose (C : Coefficient) : Coefficient :=
  ⟨C.deltaDelta, C.regularDelta, C.deltaRegular, Function.swap C.regular⟩

@[simp]
theorem transpose_deltaDelta (C : Coefficient) : C.transpose.deltaDelta = C.deltaDelta := (rfl)

@[simp]
theorem transpose_deltaRegular (C : Coefficient) :
    C.transpose.deltaRegular = C.regularDelta := (rfl)

@[simp]
theorem transpose_regularDelta (C : Coefficient) :
    C.transpose.regularDelta = C.deltaRegular := (rfl)

@[simp]
theorem transpose_regular (C : Coefficient) :
    C.transpose.regular = Function.swap C.regular := (rfl)

@[simp]
theorem transpose_transpose (C : Coefficient) : C.transpose.transpose = C := (rfl)

@[simp]
theorem transpose_zero : (0 : Coefficient).transpose = 0 := (rfl)

/-! ### The double convolution -/

/-- The double convolution of a coefficient function `C` with a density `f` in the first variable
and a density `D` in the second:
`c f (x) D (z) + f (x) (a ⊗ D) (z) + (b ⊗ f) (x) D (z) + (f ⊗ R ⊗ D) (x, z)`, with `⊗` the Mellin
convolution `Convolution.mellinConv`. Each delta function acts as the unit of the Mellin
convolution, the restriction of the density to `(0,1]`. -/
def doubleConv (C : Coefficient) (f D : ℝ → ℝ) (x z : ℝ) : ℝ :=
  C.deltaDelta * (Ioc (0 : ℝ) 1).indicator f x * (Ioc (0 : ℝ) 1).indicator D z +
    (Ioc (0 : ℝ) 1).indicator f x * mellinConv C.deltaRegular D z +
    mellinConv C.regularDelta f x * (Ioc (0 : ℝ) 1).indicator D z +
    doubleMellinConv C.regular f D x z

/-- Unfolding lemma for `Coefficient.doubleConv`. -/
theorem doubleConv_def (C : Coefficient) (f D : ℝ → ℝ) (x z : ℝ) :
    C.doubleConv f D x z =
      C.deltaDelta * (Ioc (0 : ℝ) 1).indicator f x * (Ioc (0 : ℝ) 1).indicator D z +
        (Ioc (0 : ℝ) 1).indicator f x * mellinConv C.deltaRegular D z +
        mellinConv C.regularDelta f x * (Ioc (0 : ℝ) 1).indicator D z +
        doubleMellinConv C.regular f D x z :=
  (rfl)

/-- The double convolution on `(0,1]²`. -/
theorem doubleConv_apply_of_mem (C : Coefficient) (f D : ℝ → ℝ) {x z : ℝ}
    (hx : x ∈ Ioc (0 : ℝ) 1) (hz : z ∈ Ioc (0 : ℝ) 1) :
    C.doubleConv f D x z =
      C.deltaDelta * f x * D z + f x * mellinConv C.deltaRegular D z +
        mellinConv C.regularDelta f x * D z + doubleMellinConv C.regular f D x z := by
  rw [doubleConv_def, indicator_of_mem hx, indicator_of_mem hz]

/-- The double convolution vanishes when the first momentum fraction lies outside `(0,1]`. -/
theorem doubleConv_of_notMem_left (C : Coefficient) (f D : ℝ → ℝ) {x : ℝ}
    (hx : x ∉ Ioc (0 : ℝ) 1) (z : ℝ) : C.doubleConv f D x z = 0 := by
  rw [doubleConv_def, indicator_of_notMem hx, mellinConv_apply_eq_zero_of_notMem _ _ hx,
    doubleMellinConv_of_notMem_left _ _ _ hx]
  ring

/-- The double convolution vanishes when the second momentum fraction lies outside `(0,1]`. -/
theorem doubleConv_of_notMem_right (C : Coefficient) (f D : ℝ → ℝ) (x : ℝ) {z : ℝ}
    (hz : z ∉ Ioc (0 : ℝ) 1) : C.doubleConv f D x z = 0 := by
  rw [doubleConv_def, indicator_of_notMem hz, mellinConv_apply_eq_zero_of_notMem _ _ hz,
    doubleMellinConv_of_notMem_right _ _ _ _ hz]
  ring

/-- The double convolution with the zero coefficient function vanishes. -/
@[simp]
theorem zero_doubleConv (f D : ℝ → ℝ) : (0 : Coefficient).doubleConv f D = 0 := by
  funext x z
  simp [doubleConv_def]

/-- **Exchanging the densities transposes the coefficient function.** The double convolution of
`C` with `f` in `x` and `D` in `z` equals that of the transposed coefficient function with `D` in
the first variable and `f` in the second, at `(z, x)`, provided the integrand of the regular part
is jointly integrable on `[x, 1] × [z, 1]`. -/
theorem doubleConv_transpose (C : Coefficient) (f D : ℝ → ℝ) {x z : ℝ}
    (h : x ∈ Ioc (0 : ℝ) 1 → z ∈ Ioc (0 : ℝ) 1 →
      IntegrableOn
        (fun p : ℝ × ℝ => C.regular p.1 p.2 * (f (x / p.1) / p.1) * (D (z / p.2) / p.2))
        (Icc x 1 ×ˢ Icc z 1)) :
    C.transpose.doubleConv D f z x = C.doubleConv f D x z := by
  rw [doubleConv_def, doubleConv_def, transpose_regular, doubleMellinConv_swap _ _ _ h]
  simp only [transpose_deltaDelta, transpose_deltaRegular, transpose_regularDelta]
  ring

/-- **Exchanging the densities without transposing is not a symmetry**: some coefficient
function, already one with only a regular part, has a double convolution that changes when the
two densities and the two momentum fractions are exchanged. -/
theorem exists_doubleConv_ne :
    ∃ (C : Coefficient) (f D : ℝ → ℝ) (x z : ℝ), C.doubleConv D f z x ≠ C.doubleConv f D x z := by
  obtain ⟨R, f, D, x, z, h⟩ := exists_doubleMellinConv_ne
  refine ⟨⟨0, 0, 0, R⟩, f, D, x, z, ?_⟩
  simpa [doubleConv_def] using h

/-! ### The leading-order and hard-kernel coefficient functions -/

/-- The coefficient function `c δ(1 - y) δ(1 - w)`. With `c = e_i²` it is the leading-order
coefficient function of a quark flavour `i`. -/
def delta (c : ℝ) : Coefficient := ⟨c, 0, 0, 0⟩

@[simp]
theorem delta_deltaDelta (c : ℝ) : (delta c).deltaDelta = c := (rfl)

@[simp]
theorem delta_deltaRegular (c : ℝ) : (delta c).deltaRegular = 0 := (rfl)

@[simp]
theorem delta_regularDelta (c : ℝ) : (delta c).regularDelta = 0 := (rfl)

@[simp]
theorem delta_regular (c : ℝ) : (delta c).regular = 0 := (rfl)

/-- The coefficient function `c δ(1 - y) δ(1 - w)` is symmetric. -/
@[simp]
theorem transpose_delta (c : ℝ) : (delta c).transpose = delta c := (rfl)

/-- **The leading-order double convolution.** The coefficient function `c δ(1 - y) δ(1 - w)`
multiplies the two densities at the same momentum fractions: `c f (x) D (z)` on `(0,1]²`. -/
theorem delta_doubleConv (c : ℝ) (f D : ℝ → ℝ) {x z : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1)
    (hz : z ∈ Ioc (0 : ℝ) 1) : (delta c).doubleConv f D x z = c * f x * D z := by
  simp [doubleConv_apply_of_mem _ _ _ hx hz]

/-- The coefficient function `b (y) δ(1 - w)`: a coefficient function `b` in the momentum fraction
conjugate to the parton density, concentrated at `w = 1` in the fragmentation variable. -/
def ofRegularDelta (b : ℝ → ℝ) : Coefficient := ⟨0, 0, b, 0⟩

@[simp]
theorem ofRegularDelta_deltaDelta (b : ℝ → ℝ) : (ofRegularDelta b).deltaDelta = 0 := (rfl)

@[simp]
theorem ofRegularDelta_deltaRegular (b : ℝ → ℝ) : (ofRegularDelta b).deltaRegular = 0 := (rfl)

@[simp]
theorem ofRegularDelta_regularDelta (b : ℝ → ℝ) : (ofRegularDelta b).regularDelta = b := (rfl)

@[simp]
theorem ofRegularDelta_regular (b : ℝ → ℝ) : (ofRegularDelta b).regular = 0 := (rfl)

/-- The double convolution with `b (y) δ(1 - w)` is the Mellin convolution of `b` with the
density in `x`, times the fragmentation density at `z`, on `(0,1]²`. -/
theorem ofRegularDelta_doubleConv (b f D : ℝ → ℝ) {x z : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1)
    (hz : z ∈ Ioc (0 : ℝ) 1) : (ofRegularDelta b).doubleConv f D x z = mellinConv b f x * D z := by
  simp [doubleConv_apply_of_mem _ _ _ hx hz]

end Coefficient

/-! ### The flavour-summed structure function -/

variable {Flavor Hadron : Type}

/-- The semi-inclusive structure function in collinear factorization: the flavour sum
`∑_{i, j} (f_i ⊗ C_{ij} ⊗ D_j) (x, z)` of the double convolutions of the parton densities `f_i` at
the scale `Q2`, the coefficient functions `C_{ij}` at that scale, and the fragmentation functions
`D_j` of the fragmenting parton `j` into the hadron `h`. -/
def structureFunction [Fintype Flavor] (C : Flavor → Flavor → ℝ → Coefficient)
    (f : Particles.Parton.PDF.Pdf Flavor) (D : Particles.Fragmentation.Frag Hadron Flavor)
    (h : Hadron) (x z Q2 : ℝ) : ℝ :=
  ∑ i, ∑ j, (C i j Q2).doubleConv (fun y => f i y Q2) (fun y => D h j y Q2) x z

/-- Unfolding lemma for `SIDIS.structureFunction`. -/
theorem structureFunction_def [Fintype Flavor] (C : Flavor → Flavor → ℝ → Coefficient)
    (f : Particles.Parton.PDF.Pdf Flavor) (D : Particles.Fragmentation.Frag Hadron Flavor)
    (h : Hadron) (x z Q2 : ℝ) :
    structureFunction C f D h x z Q2 =
      ∑ i, ∑ j, (C i j Q2).doubleConv (fun y => f i y Q2) (fun y => D h j y Q2) x z :=
  (rfl)

/-- For a coefficient function diagonal in flavour, the structure function is a single flavour
sum. -/
theorem structureFunction_diagonal [Fintype Flavor] [DecidableEq Flavor]
    (c : Flavor → ℝ → Coefficient) (f : Particles.Parton.PDF.Pdf Flavor)
    (D : Particles.Fragmentation.Frag Hadron Flavor) (h : Hadron) (x z Q2 : ℝ) :
    structureFunction (fun i j Q2 => if i = j then c i Q2 else 0) f D h x z Q2 =
      ∑ i, (c i Q2).doubleConv (fun y => f i y Q2) (fun y => D h i y Q2) x z := by
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i (fun j _ hji => by simp [Ne.symm hji])
    (fun hi => absurd (Finset.mem_univ i) hi)]
  simp only [↓reduceIte]

/-- **The leading-order structure function.** For the coefficient functions
`e_i δ_{ij} δ(1 - y) δ(1 - w)`, with `e_i` the squared charge of flavour `i`, the double
convolution reduces to `∑ᵢ e_i f_i (x) D_i (z)` on `(0,1]²`. -/
theorem structureFunction_delta [Fintype Flavor] [DecidableEq Flavor] (e : Flavor → ℝ)
    (f : Particles.Parton.PDF.Pdf Flavor) (D : Particles.Fragmentation.Frag Hadron Flavor)
    (h : Hadron) {x z : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1) (hz : z ∈ Ioc (0 : ℝ) 1) (Q2 : ℝ) :
    structureFunction (fun i j _ => if i = j then Coefficient.delta (e i) else 0) f D h x z Q2 =
      ∑ i, e i * f i x Q2 * D h i z Q2 := by
  rw [structureFunction_diagonal (fun i _ => Coefficient.delta (e i))]
  exact Finset.sum_congr rfl fun i _ => Coefficient.delta_doubleConv _ _ _ hx hz

/-- **Compatibility with `sidisStructureFunction`.** If the hard kernel `C'` of
`EpsilonEridani.QFT.Scattering.DIS.SIDIS.sidisStructureFunction` is, at the scale `Q2`, the
collinear kernel of the coefficient function `c i` for every flavour `i`, then
`sidisStructureFunction` is the double convolution with the coefficient functions
`δ_{ij} c_i (y) δ(1 - w)` on `(0,1]²`. -/
theorem structureFunction_ofRegularDelta [Fintype Flavor] [DecidableEq Flavor]
    (C' : DIS.HardKernel Flavor) (c : Flavor → ℝ → ℝ) {Q2 : ℝ}
    (hc : ∀ i, Convolution.IsCollinearKernel (fun x' z => C' i x' z Q2) (c i))
    (f : Particles.Parton.PDF.Pdf Flavor) (D : Particles.Fragmentation.Frag Hadron Flavor)
    (h : Hadron) {x z : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1) (hz : z ∈ Ioc (0 : ℝ) 1) :
    structureFunction (fun i j _ => if i = j then Coefficient.ofRegularDelta (c i) else 0)
        f D h x z Q2 =
      Scattering.DIS.SIDIS.sidisStructureFunction C' f D h x z Q2 := by
  rw [structureFunction_diagonal (fun i _ => Coefficient.ofRegularDelta (c i))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Coefficient.ofRegularDelta_doubleConv _ _ _ hx hz, Scattering.DIS.SIDIS.sidisChannel,
    DIS.loChannel, (hc i).convolveAt_eq, ← mellinConv_apply_eq_convolveAt_of_mem _ _ hx,
    mellinConv_comm]

end SIDIS
end Factorization
end QFT
end EpsilonEridani
