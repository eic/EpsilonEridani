/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.QFT.SmallX.Dipole.Multipole

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
The dipole operator is the two-point member `n = 1` of the `2n`-point Wilson-line correlators
`SmallX.multipoleS`, and its properties are specialisations of theirs. They hold configuration
by configuration, before any averaging, and use only unitarity of the Wilson lines:

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
- `SmallX.multipoleS_fin_one`: the two-point correlator is the dipole operator.
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
in the target field `U`. It is the two-point Wilson-line correlator. -/
def dipoleS (U : WilsonConfiguration Nc) (x y : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  multipoleS U ![x] ![y]

/-- The dipole operator as an explicit normalised trace. -/
lemma dipoleS_def (U : WilsonConfiguration Nc) (x y : EuclideanSpace ℝ (Fin 2)) :
    dipoleS U x y =
      (Nc : ℝ)⁻¹ * (trace ((U x : Matrix (Fin Nc) (Fin Nc) ℂ) * star (U y).1)).re := by
  simp [dipoleS, multipoleS_def]

/-- The two-point correlator is the dipole operator. -/
@[simp]
theorem multipoleS_fin_one (U : WilsonConfiguration Nc) (x y : Fin 1 → EuclideanSpace ℝ (Fin 2)) :
    multipoleS U x y = dipoleS U (x 0) (y 0) := by
  rw [dipoleS]
  congr 1 <;> funext i <;> rw [Subsingleton.elim i 0] <;> rfl

/-- **Colour transparency** of a single configuration: a dipole of zero size does not
scatter, `S U x x = 1`. -/
@[simp]
theorem dipoleS_self [NeZero Nc] (U : WilsonConfiguration Nc) (x : EuclideanSpace ℝ (Fin 2)) :
    dipoleS U x x = 1 :=
  multipoleS_self U _

/-- The dipole operator is symmetric under exchange of the quark and antiquark positions. -/
theorem dipoleS_comm (U : WilsonConfiguration Nc) (x y : EuclideanSpace ℝ (Fin 2)) :
    dipoleS U x y = dipoleS U y x := by
  rw [dipoleS, multipoleS_reverse, multipoleS_fin_one]
  rfl

/-- **Unitarity bound** on the dipole operator of a single configuration: `|S U x y| ≤ 1`. -/
theorem abs_dipoleS_le_one (U : WilsonConfiguration Nc) (x y : EuclideanSpace ℝ (Fin 2)) :
    |dipoleS U x y| ≤ 1 :=
  abs_multipoleS_le_one U _ _

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
    dipoleS (WilsonConfiguration.gaugeTransform Ωp Ωm U) x y = dipoleS U x y :=
  multipoleS_gaugeTransform Ωp Ωm U (fun _ => by simpa using hm) fun _ => by simpa using hp.symm

end SmallX
end QFT
end EpsilonEridani
