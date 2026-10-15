/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.Mathematics.DataStructures.Matrix.PosSemidef
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Analysis.Bochner.Gaussian.Basic
public import TauCeti.Analysis.Matrix.PosSemidef

/-!
# Admissible dipole amplitudes and the unitarity bound

The forward scattering amplitude `N x y` of a colour dipole with its quark at transverse
position `x` and its antiquark at `y`, at a fixed rapidity, is the target average of
`1 - S U x y`, where `S U x y = (1 / N_c) Re Tr(U(x) U(y)†)` is the dipole operator of a
light-cone Wilson-line configuration `U` with values in `U(N_c)`. Its dipole S-matrix is
`S = 1 - N`. This file records the conditions that every such average
satisfies and derives the unitarity bound `0 ≤ N x y ≤ 1` from them.

An amplitude `N` is *admissible* (`SmallX.IsAdmissible`) when

* it is colour transparent, `N x x = 0`: a dipole of zero size does not scatter;
* its S-matrix `1 - N` is a positive-semidefinite kernel on the transverse plane;
* its S-matrix is non-negative, `N x y ≤ 1`.

The first two conditions hold configuration by configuration and are preserved by averaging, so
they hold for every target ensemble: `S U x x = 1` by unitarity, and `S U` is the Gram kernel of
the vectors `U(x)` for the real inner product `(A, B) ↦ (1 / N_c) Re Tr(A B†)`. The third does
not hold configuration by configuration: for `N_c = 1` the dipole
operator is `cos (θ x - θ y)` for a phase `θ`, which takes negative values. In the
McLerran-Venugopalan model the averaged S-matrix is an exponential and hence positive; in general
non-negativity is carried as part of admissibility.

Positive semidefiniteness is the source of the lower half of the unitarity bound: the principal
`2 × 2` minors of the S-matrix kernel give `|1 - N x y| ≤ 1` once the diagonal is `1`, so
`N x y ∈ [0, 2]` for every amplitude obeying the first two conditions, and `N x y ∈ [0, 1]` for
an admissible one. The bound holds pointwise in the two endpoints, hence at every fixed impact
parameter; it says nothing about the growth of the total cross section, so no Froissart-type
bound follows from it.

Two admissible amplitudes are exhibited:

* the black disc `SmallX.blackDisc`, `N x y = 1` for `x ≠ y`, whose S-matrix is the identity
  kernel;
* the Golec-Biernat-Wüsthoff amplitude `SmallX.golecBiernatWusthoff` at saturation scale `Q_s`,
  `N x y = 1 - exp (-‖x - y‖² Q_s² / 4)`, whose S-matrix is a Gaussian kernel
  (K. Golec-Biernat and M. Wüsthoff, *Phys. Rev.* **D59** (1998) 014017).

See Kovchegov and Levin, *Quantum Chromodynamics at High Energy*, CUP 2012, ch. 4, for the
dipole amplitude and its unitarity bound.

## Main definitions

- `SmallX.IsAdmissible`: admissibility of a dipole amplitude at fixed rapidity.
- `SmallX.blackDisc`: the black disc amplitude.
- `SmallX.golecBiernatWusthoff`: the Golec-Biernat-Wüsthoff amplitude at a saturation scale.

## Main results

- `SmallX.mem_Icc_of_posSemidef_one_sub`: colour transparency and a positive-semidefinite
  S-matrix give `N x y ∈ [0, 2]`, for a kernel on an arbitrary index type.
- `SmallX.IsAdmissible.symm`: an admissible amplitude is symmetric in its endpoints.
- `SmallX.IsAdmissible.mem_Icc`: the unitarity bound `N x y ∈ [0, 1]`.
- `SmallX.isAdmissible_blackDisc` and `SmallX.isAdmissible_golecBiernatWusthoff`: the black disc
  and the Golec-Biernat-Wüsthoff amplitude are admissible.
-/

@[expose] public section

namespace EpsilonEridani
namespace QFT
namespace SmallX

open Matrix
open scoped ComplexOrder

/-- A dipole amplitude `N x y` at fixed rapidity, for a quark at `x` and an antiquark at `y`, is
*admissible* when it is colour transparent, its S-matrix `1 - N` is a positive-semidefinite
kernel on the transverse plane, and its S-matrix is non-negative. -/
structure IsAdmissible (N : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) → ℝ) : Prop where
  /-- Colour transparency: a dipole of zero size does not scatter. -/
  apply_self (x : EuclideanSpace ℝ (Fin 2)) : N x x = 0
  /-- The dipole S-matrix `1 - N` is a positive-semidefinite kernel. -/
  posSemidef_one_sub : (Matrix.of fun x y => 1 - N x y).PosSemidef
  /-- The dipole S-matrix `1 - N` is non-negative. -/
  le_one (x y : EuclideanSpace ℝ (Fin 2)) : N x y ≤ 1

/-- A colour-transparent amplitude whose S-matrix `1 - N` is a positive-semidefinite kernel lies
in `[0, 2]`: the S-matrix has unit diagonal, so every entry has modulus at most one. The kernel
may live on an arbitrary index type; no structure of the transverse plane enters. -/
theorem mem_Icc_of_posSemidef_one_sub {α : Type*} {N : α → α → ℝ} (hN : ∀ x, N x x = 0)
    (hS : (Matrix.of fun x y => 1 - N x y).PosSemidef) (x y : α) :
    N x y ∈ Set.Icc (0 : ℝ) 2 := by
  have h := hS.norm_le_one_of_apply_self_eq_one (a := x) (b := y) (by simp [hN])
    (by simp [hN])
  rw [of_apply, Real.norm_eq_abs, abs_le] at h
  constructor <;> linarith [h.1, h.2]

variable {N : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) → ℝ}

namespace IsAdmissible

/-- An admissible amplitude is symmetric under exchange of the quark and antiquark positions. -/
theorem symm (hN : IsAdmissible N) (x y : EuclideanSpace ℝ (Fin 2)) : N x y = N y x := by
  have h := hN.posSemidef_one_sub.isHermitian.apply x y
  simp only [of_apply, star_trivial] at h
  linarith

/-- An admissible amplitude is non-negative. -/
theorem nonneg (hN : IsAdmissible N) (x y : EuclideanSpace ℝ (Fin 2)) : 0 ≤ N x y :=
  (mem_Icc_of_posSemidef_one_sub hN.apply_self hN.posSemidef_one_sub x y).1

/-- **Unitarity bound**: an admissible amplitude lies in the unit interval, `0 ≤ N x y ≤ 1`. -/
theorem mem_Icc (hN : IsAdmissible N) (x y : EuclideanSpace ℝ (Fin 2)) :
    N x y ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨hN.nonneg x y, hN.le_one x y⟩

end IsAdmissible

/-- The **black disc** dipole amplitude: the dipole scatters maximally, `N x y = 1`, for every
nonzero dipole size, and is colour transparent. Its S-matrix is the identity kernel.

It is `noncomputable` because it branches on equality of transverse positions, which is not
decidable computably. -/
noncomputable def blackDisc (x y : EuclideanSpace ℝ (Fin 2)) : ℝ := if x = y then 0 else 1

/-- The black disc amplitude at a quark position `x` and an antiquark position `y`. -/
lemma blackDisc_apply (x y : EuclideanSpace ℝ (Fin 2)) :
    blackDisc x y = if x = y then 0 else 1 := rfl

/-- The black disc is colour transparent: a dipole of zero size does not scatter. -/
lemma blackDisc_apply_self (x : EuclideanSpace ℝ (Fin 2)) : blackDisc x x = 0 := by
  simp [blackDisc]

/-- The black disc scatters maximally for every nonzero dipole size. -/
lemma blackDisc_apply_ne {x y : EuclideanSpace ℝ (Fin 2)} (h : x ≠ y) : blackDisc x y = 1 := by
  simp [blackDisc, h]

/-- The **black disc** is admissible: its S-matrix is the identity kernel. -/
theorem isAdmissible_blackDisc : IsAdmissible blackDisc := by
  refine ⟨fun x => blackDisc_apply_self x, ?_, fun x y => ?_⟩
  · have e : (1 : Matrix (EuclideanSpace ℝ (Fin 2)) _ ℝ) =
        Matrix.of fun x y => 1 - blackDisc x y := by
      ext x y
      by_cases h : x = y <;> simp [h, Matrix.one_apply, blackDisc]
    exact e ▸ PosSemidef.one
  · by_cases h : x = y <;> simp [blackDisc, h]

/-- The **Golec-Biernat-Wüsthoff amplitude** `N x y = 1 - exp (-Q_s² ‖x - y‖² / 4)` at
saturation scale `Q_s`: it saturates at one for a large dipole and is colour transparent, with
exactly quadratic behaviour at small dipole size. Its S-matrix is a Gaussian kernel in the
dipole size `‖x - y‖`. -/
noncomputable def golecBiernatWusthoff (Qs : ℝ) (x y : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  1 - Real.exp (-(Qs ^ 2 / 4 * ‖x - y‖ ^ 2))

/-- The Golec-Biernat-Wüsthoff amplitude at a quark position `x` and an antiquark position
`y`. -/
lemma golecBiernatWusthoff_apply (Qs : ℝ) (x y : EuclideanSpace ℝ (Fin 2)) :
    golecBiernatWusthoff Qs x y = 1 - Real.exp (-(Qs ^ 2 / 4 * ‖x - y‖ ^ 2)) := rfl

/-- The Golec-Biernat-Wüsthoff amplitude is colour transparent, with exactly quadratic
behaviour at small dipole size. -/
lemma golecBiernatWusthoff_apply_self (Qs : ℝ) (x : EuclideanSpace ℝ (Fin 2)) :
    golecBiernatWusthoff Qs x x = 0 := by
  simp [golecBiernatWusthoff]

/-- The **Golec-Biernat-Wüsthoff amplitude** is admissible for every saturation scale `Q_s`:
its S-matrix is a Gaussian kernel in the dipole size `‖x - y‖`, hence positive semidefinite,
and takes values in `(0, 1]`. -/
theorem isAdmissible_golecBiernatWusthoff (Qs : ℝ) :
    IsAdmissible (golecBiernatWusthoff Qs) := by
  refine ⟨fun x => golecBiernatWusthoff_apply_self Qs x, ?_, fun x y => ?_⟩
  · -- TauCeti's Gaussian kernel over `ℂ`; `Matrix.of` is the identity on the underlying
    -- function, so its positive semidefiniteness is that of this matrix.
    have hG : (Matrix.of fun x y : EuclideanSpace ℝ (Fin 2) =>
        Complex.exp (-(Qs ^ 2 / 4 * ‖x - y‖ ^ 2 : ℝ))).PosSemidef :=
      TauCeti.posSemidef_cexp_neg_mul_sq_norm (by positivity)
    have e : (Matrix.of fun x y : EuclideanSpace ℝ (Fin 2) =>
        Complex.exp (-(Qs ^ 2 / 4 * ‖x - y‖ ^ 2 : ℝ))).map RCLike.re =
        Matrix.of fun x y => 1 - golecBiernatWusthoff Qs x y := by
      ext x y
      simp only [map_apply, of_apply, ← Complex.ofReal_neg, ← Complex.ofReal_exp,
        RCLike.re_to_complex, Complex.ofReal_re, sub_sub_cancel, golecBiernatWusthoff]
    exact e ▸ hG.map_re
  · rw [golecBiernatWusthoff_apply]
    linarith [Real.exp_pos (-(Qs ^ 2 / 4 * ‖x - y‖ ^ 2))]

end SmallX
end QFT
end EpsilonEridani
