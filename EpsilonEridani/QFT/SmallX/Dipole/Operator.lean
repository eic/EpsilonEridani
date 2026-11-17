/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.Mathematics.DataStructures.Matrix.UnitaryTrace
public import EpsilonEridani.QFT.SmallX.Dipole.WilsonLine

/-!
# The colour-dipole operator

A colour-singlet quark-antiquark pair with the quark at transverse position `x` and the
antiquark at `y` crosses a target described by the Wilson-line configuration `U`. Its eikonal
S-matrix in the target field is the dipole operator

```
S U x y = (1 / N_c) Re Tr(U(x) U(y)†),
```

and `1 - S U x y` is its scattering amplitude in that field. Averaging over the target ensemble
turns these into the dipole S-matrix and the dipole amplitude `N = 1 - S` of the colour-dipole
picture (Nikolaev and Zakharov, *Z. Phys.* **C49** (1991) 607; Mueller, *Nucl. Phys.* **B415**
(1994) 373; Kovchegov and Levin, *Quantum Chromodynamics at High Energy*, CUP 2012, ch. 4).
The properties proved here hold configuration by configuration, before any averaging, and use
only unitarity of the Wilson lines:

* a point-like dipole does not scatter, `S U x x = 1` (colour transparency of a single
  configuration);
* `S` is symmetric in its two endpoints;
* `|S U x y| ≤ 1`, so the unaveraged amplitude `1 - S` lies in `[0, 2]`;
* `S` is invariant under a gauge transformation whose values at `x⁺ = +∞` and at `x⁺ = -∞`
  each agree at the two endpoints of the dipole, in particular under every gauge
  transformation that is constant in the transverse plane at both ends of the light cone. For
  a gauge transformation that differs between `x` and `y` there, the two light-like lines would
  have to be joined by transverse gauge links at `x⁺ = ±∞`, which this operator omits.

## Main results

- `SmallX.dipoleS`: the dipole operator of a Wilson-line configuration.
- `SmallX.dipoleS_self`: colour transparency, `S U x x = 1`.
- `SmallX.dipoleS_comm`: endpoint symmetry.
- `SmallX.abs_dipoleS_le_one` and `SmallX.one_sub_dipoleS_mem_Icc`: the unitarity bounds.
- `SmallX.dipoleS_gaugeTransform`: gauge invariance.
-/

public section

noncomputable section

namespace EpsilonEridani
namespace QFT
namespace SmallX

open Matrix

variable {Nc : ℕ}

/-- The dipole operator `S U x y = (1 / N_c) Re Tr(U(x) U(y)†)` of a Wilson-line configuration
`U`, for a quark at `x` and an antiquark at `y`: the eikonal S-matrix of a colour-singlet dipole
in the target field `U`. -/
def dipoleS (U : WilsonConfiguration Nc) (x y : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  (Nc : ℝ)⁻¹ * (trace ((U x : Matrix (Fin Nc) (Fin Nc) ℂ) * star (U y).1)).re

lemma dipoleS_def (U : WilsonConfiguration Nc) (x y : EuclideanSpace ℝ (Fin 2)) :
    dipoleS U x y = (Nc : ℝ)⁻¹ * (trace ((U x : Matrix (Fin Nc) (Fin Nc) ℂ) * star (U y).1)).re :=
  (rfl)

/-- **Colour transparency** of a single configuration: a dipole of zero size does not
scatter, `S U x x = 1`. -/
@[simp]
theorem dipoleS_self [NeZero Nc] (U : WilsonConfiguration Nc) (x : EuclideanSpace ℝ (Fin 2)) :
    dipoleS U x x = 1 := by
  simp [dipoleS_def, Unitary.mul_star_self_of_mem (U x).2, NeZero.ne Nc]

/-- The dipole operator is symmetric under exchange of the quark and antiquark positions. -/
theorem dipoleS_comm (U : WilsonConfiguration Nc) (x y : EuclideanSpace ℝ (Fin 2)) :
    dipoleS U x y = dipoleS U y x := by
  have h : ((U y).1 * star (U x).1 : Matrix (Fin Nc) (Fin Nc) ℂ) =
      ((U x).1 * star (U y).1)ᴴ := by
    simp only [← star_eq_conjTranspose, star_mul, star_star]
  simp only [dipoleS_def, h, trace_conjTranspose, Complex.star_def, Complex.conj_re]

/-- **Unitarity bound** on the dipole operator of a single configuration: `|S U x y| ≤ 1`. -/
theorem abs_dipoleS_le_one (U : WilsonConfiguration Nc) (x y : EuclideanSpace ℝ (Fin 2)) :
    |dipoleS U x y| ≤ 1 := by
  have hmem : (U x : Matrix (Fin Nc) (Fin Nc) ℂ) * star (U y).1 ∈ unitaryGroup (Fin Nc) ℂ :=
    mul_mem (U x).2 (Unitary.star_mem (U y).2)
  have htr := (Complex.abs_re_le_norm _).trans (Matrix.norm_trace_le_card_of_mem_unitaryGroup hmem)
  rw [Fintype.card_fin] at htr
  simp only [dipoleS_def, abs_mul, abs_inv, Nat.abs_cast]
  rcases Nat.eq_zero_or_pos Nc with h | h
  · simp [h]
  · rw [inv_mul_le_iff₀ (by exact_mod_cast h), mul_one]
    exact htr

/-- The scattering amplitude `1 - S U x y` of a dipole in a single configuration lies in
`[0, 2]`. The sharper bound `[0, 1]` holds only after averaging over a target ensemble whose
averaged S-matrix is non-negative. -/
theorem one_sub_dipoleS_mem_Icc (U : WilsonConfiguration Nc) (x y : EuclideanSpace ℝ (Fin 2)) :
    1 - dipoleS U x y ∈ Set.Icc (0 : ℝ) 2 := by
  obtain ⟨h₁, h₂⟩ := abs_le.mp (abs_dipoleS_le_one U x y)
  constructor <;> linarith

/-- **Gauge invariance** of the dipole operator: under `U(z) ↦ Ω₊(z) U(z) Ω₋(z)†`, the dipole
operator at `x, y` is unchanged as soon as `Ω₊` and `Ω₋` each take the same value at `x` and
at `y`. In particular it is invariant under every global colour rotation `U ↦ V U W†`. -/
theorem dipoleS_gaugeTransform (Ωp Ωm : EuclideanSpace ℝ (Fin 2) → unitaryGroup (Fin Nc) ℂ)
    (U : WilsonConfiguration Nc) {x y : EuclideanSpace ℝ (Fin 2)} (hp : Ωp x = Ωp y)
    (hm : Ωm x = Ωm y) :
    dipoleS (WilsonConfiguration.gaugeTransform Ωp Ωm U) x y = dipoleS U x y := by
  have key : ((Ωp x * U x * star (Ωm x) : unitaryGroup (Fin Nc) ℂ) : Matrix (Fin Nc) (Fin Nc) ℂ) *
      star (Ωp y * U y * star (Ωm y) : unitaryGroup (Fin Nc) ℂ).1 =
      (Ωp y).1 * ((U x).1 * star (U y).1) * star (Ωp y).1 := by
    rw [hp, hm]
    simp only [Submonoid.coe_mul, Unitary.coe_star, star_mul, star_star, mul_assoc]
    simp only [← mul_assoc (star (Ωm y).1), Unitary.star_mul_self_of_mem (Ωm y).2, one_mul]
  simp only [dipoleS_def, WilsonConfiguration.gaugeTransform_apply, key, trace_unitary_conj]

end SmallX
end QFT
end EpsilonEridani
