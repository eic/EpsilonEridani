/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith, Wouter Deconinck
-/
module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
/-!

# The boundary of diffractive DIS in `t`

This module defines the kinematic boundary of the momentum transfer `t` of a diffractive event at
fixed light-cone momentum fraction `ξ = Δ⁺/P⁺` lost by the target: `tMin M M_Y ξ` for a target of
mass `M` emerging as a system of mass `M_Y`, and its target-elastic case `tMinElastic M ξ`
(`M_Y = M`). It records their defining expressions, the boundary condition in terms of the
magnitude `|t| = -t` (`le_tMin_iff`, `le_tMinElastic_iff`) and their sign (`tMin_nonpos`,
`tMinElastic_nonpos`). The light-cone fraction is not the invariant `ξ = Δ·q / P·q` of
`Invariants.xi`: the two agree only in the Bjorken limit.

That these are the boundaries of the target-side kinematics is proved in
`Diffractive.Kinematics.MomentumTransferBound`, from the on-shell conditions in light-cone
components.

## References

* G. Wolf, *Review of high energy diffraction in real and virtual photon proton scattering at
  HERA*, Rept. Prog. Phys. **73** (2010) 116202, §2, for the target-elastic boundary in `t`.
* V. Barone and E. Predazzi, *High-Energy Particle Diffraction*, Springer, 2002, ch. 1–2, for
  the kinematics of the diffractive final state.
-/

public section

noncomputable section

namespace EpsilonEridani
namespace QFT
namespace Scattering
namespace DIS
namespace Diffractive

/-! ## The boundary in `t` for a target-side system of mass `M_Y` -/

/-- The kinematic boundary in `t` at fixed light-cone momentum fraction `ξ` lost by a target of
mass `M` that emerges as a system of mass `M_Y`:
`tMin M M_Y ξ = -ξ (M_Y² - (1 - ξ) M²) / (1 - ξ)`.

The argument `xiLC` is the light-cone fraction `ξ = Δ⁺/P⁺`, not the
invariant `Invariants.xi`. For a reflexive form, non-vanishing plus momentum and `ξ ≠ 1`, the
on-shell conditions `P² = M²`, `P'² = M_Y²` give `t = tMin M M_Y ξ + w²/(1-ξ)`
(`Kinematics.tMom_eq_tMin_add`), where `w = Δ_T - ξ P_T` is the transverse momentum transfer
relative to the target direction (`w = Δ_T` for a target with no transverse momentum), so that
`t ≤ tMin M M_Y ξ` for `ξ < 1` when `w² ≤ 0`, the boundary being attained when `w² = 0`. For a
metric that is negative semidefinite on transverse vectors and admits a space-like transverse
vector, the momentum transfers compatible with the target-side constraints (`P`, `P'² = M_Y²`,
`ξ < 1`) are exactly `t ≤ tMin M M_Y ξ` (`Kinematics.setOf_tMom_eq_Iic_tMin`); the photon-side
mass `M_X² ≥ 0` is not imposed there, so this is not yet the diffractive physical region. In the
target-elastic case `M_Y = M` it reduces to `tMinElastic M ξ` (`tMin_self`), which is the boundary
`Particles.Parton.GPD.tZero M η` of the off-forward kinematics at skewness `η = ξ/(2-ξ)`, i.e.
`ξ = 2η/(1+η)` (`tMinElastic_eq_tZero`). At the pole `ξ = 1` the value is the division junk
`0`. -/
def tMin (M MY xiLC : ℝ) : ℝ := -(xiLC * (MY ^ 2 - (1 - xiLC) * M ^ 2)) / (1 - xiLC)

/-- Defining expression for `tMin`. -/
theorem tMin_def (M MY xiLC : ℝ) :
    tMin M MY xiLC = -(xiLC * (MY ^ 2 - (1 - xiLC) * M ^ 2)) / (1 - xiLC) := (rfl)

/-- The negated boundary, `-tMin M M_Y ξ = ξ (M_Y² - (1 - ξ) M²)/(1-ξ)`. The identity is
unconditional; it is a (non-negative) magnitude only under the hypotheses of `tMin_nonpos`. -/
theorem neg_tMin (M MY xiLC : ℝ) :
    -tMin M MY xiLC = xiLC * (MY ^ 2 - (1 - xiLC) * M ^ 2) / (1 - xiLC) := by
  rw [tMin_def, neg_div, neg_neg]

/-- The boundary condition `t ≤ tMin M M_Y ξ` for a real momentum transfer `t`, in terms of its
magnitude: `-t ≥ ξ (M_Y² - (1 - ξ) M²)/(1-ξ)`, for any choice of the parameters. -/
theorem le_tMin_iff (M MY xiLC t : ℝ) :
    t ≤ tMin M MY xiLC ↔ xiLC * (MY ^ 2 - (1 - xiLC) * M ^ 2) / (1 - xiLC) ≤ -t := by
  rw [← neg_tMin, neg_le_neg_iff]

/-- At vanishing momentum loss `ξ = 0` the boundary degenerates to `t = 0` for every final mass. -/
@[simp]
theorem tMin_xiLC_zero (M MY : ℝ) : tMin M MY 0 = 0 := by
  rw [tMin_def]
  norm_num

/-- The boundary `tMin` is non-positive for `ξ ≤ 1` whenever the numerator
`ξ (M_Y² - (1 - ξ) M²)` is non-negative. This holds unconditionally in the target-elastic case,
where the numerator is `ξ²M²` (`tMinElastic_nonpos`). -/
theorem tMin_nonpos {M MY xiLC : ℝ} (h1 : xiLC ≤ 1)
    (hnum : 0 ≤ xiLC * (MY ^ 2 - (1 - xiLC) * M ^ 2)) : tMin M MY xiLC ≤ 0 := by
  rw [tMin_def, neg_div, neg_nonpos]
  exact div_nonneg hnum (sub_nonneg.mpr h1)

/-- The boundary `tMin` is non-positive for `0 ≤ ξ ≤ 1` above the threshold
`(1 - ξ) M² ≤ M_Y²`, in particular whenever `M² ≤ M_Y²`. -/
theorem tMin_nonpos_of_one_sub_mul_sq_le_sq {M MY xiLC : ℝ} (h0 : 0 ≤ xiLC) (h1 : xiLC ≤ 1)
    (hM : (1 - xiLC) * M ^ 2 ≤ MY ^ 2) : tMin M MY xiLC ≤ 0 :=
  tMin_nonpos h1 (mul_nonneg h0 (sub_nonneg.mpr hM))

/-! ## The target-elastic boundary in `t` -/

/-- The kinematic boundary in `t` at fixed light-cone momentum fraction in the target-elastic
case (`M_Y = M`), with `M` the target mass: `tMinElastic M ξ = -ξ²M²/(1-ξ)`.

The argument `xiLC` is the light-cone momentum fraction `ξ = Δ⁺/P⁺` lost by the target, named
apart from the invariant `Invariants.xi = Δ·q / P·q`, with which it agrees only up to relative
corrections of order `Q²M²/(P·q)²`, so exactly only in the Bjorken limit; at finite energy the
target-elastic boundary is not exactly `tMinElastic M (Invariants.xi i)`. Nor is `xiLC` the
skewness `ExclKinematics.xiSkew` (Belitsky-Müller-Kirchner's `η`), a different variable that also
carries a `ξ` in the exclusive kinematics and for which the target-elastic boundary is a different
function.

For a reflexive form, a target with no transverse momentum and non-vanishing plus momentum, a
light-cone fraction `ξ < 1` and the target-side constraints `P² = M²`, `P'² = M²`, a transverse
momentum transfer with `Δ_T² ≤ 0` gives `t ≤ tMinElastic M ξ` (for a target with transverse
momentum `P_T`, `Δ_T` is replaced by `Δ_T - ξ P_T`), equivalently
`|t| ≥ ξ²M²/(1-ξ)` (`le_tMinElastic_iff`), by
`Kinematics.tMom_le_tMin` with `tMin_self`; the bound is saturated exactly when `Δ_T² = 0`
(`Kinematics.tMom_eq_tMin_iff`), i.e. in the forward configuration `Δ_T = 0` for a metric
definite on transverse vectors. If moreover the metric is
negative semidefinite on transverse vectors and admits a space-like transverse vector, these
momentum transfers are exactly `t ≤ tMinElastic M ξ` (`Kinematics.setOf_tMom_eq_Iic_tMin`).
These statements constrain only the target side and make no claim about the full diffractive
physical region. At the pole `ξ = 1` the true boundary diverges, whereas, like any
real division in Lean, `tMinElastic M 1` is `0`; the characterisation is therefore stated only
for `ξ < 1`.

The boundary is obtained from the two-body threshold condition at fixed `(ξ, M, M_Y)` as
`tMin M M_Y ξ`, and in the target-elastic case `M_Y = M` it reduces to `-ξ²M²/(1-ξ)`
(`tMin_self`); see Wolf, *Rept. Prog. Phys.* **73** (2010) 116202, §2.

See `tMinElastic_def` for the defining expression, `le_tMinElastic_iff` for the boundary
condition in terms of `|t|`, and `tMinElastic_nonpos` for the sign property. -/
def tMinElastic (M xiLC : ℝ) : ℝ := tMin M M xiLC

/-- In the target-elastic case `M_Y = M` the boundary `tMin` is `tMinElastic`. -/
@[simp]
theorem tMin_self (M xiLC : ℝ) : tMin M M xiLC = tMinElastic M xiLC := (rfl)

/-- Defining expression for `tMinElastic`. -/
theorem tMinElastic_def (M xiLC : ℝ) :
    tMinElastic M xiLC = -(xiLC ^ 2 * M ^ 2) / (1 - xiLC) := by
  rw [← tMin_self, tMin_def]
  ring

/-- The negated target-elastic boundary, `-tMinElastic M ξ = ξ²M²/(1-ξ)`. The identity is
unconditional; `-tMinElastic M ξ` is a (non-negative) magnitude only for `ξ ≤ 1`
(`tMinElastic_nonpos`). -/
theorem neg_tMinElastic (M xiLC : ℝ) : -tMinElastic M xiLC = xiLC ^ 2 * M ^ 2 / (1 - xiLC) := by
  rw [tMinElastic_def, neg_div, neg_neg]

/-- The boundary condition `t ≤ tMinElastic M ξ` for a real momentum transfer `t`, in terms of its
magnitude: `-t ≥ ξ²M²/(1-ξ)`, for any choice of the parameters. This is `le_tMin_iff` at
`M_Y = M`, with the numerator `ξ (M² - (1 - ξ) M²)` simplified to `ξ²M²`. -/
theorem le_tMinElastic_iff (M xiLC t : ℝ) :
    t ≤ tMinElastic M xiLC ↔ xiLC ^ 2 * M ^ 2 / (1 - xiLC) ≤ -t := by
  rw [← neg_tMinElastic, neg_le_neg_iff]

/-- At vanishing momentum loss `ξ = 0` the target-elastic boundary degenerates to `t = 0`. -/
@[simp]
theorem tMinElastic_xiLC_zero (M : ℝ) : tMinElastic M 0 = 0 := by
  rw [← tMin_self, tMin_xiLC_zero]

/-- The target-elastic boundary lies on the non-positive side of zero whenever `xiLC ≤ 1`, in
particular throughout the physical range `ξ ∈ [0, 1)`: the boundary of the physical region is on
the same side of zero as the region it bounds. At `xiLC = 1` the value is the division junk `0`. -/
theorem tMinElastic_nonpos (M xiLC : ℝ) (h : xiLC ≤ 1) : tMinElastic M xiLC ≤ 0 := by
  rw [← tMin_self]
  refine tMin_nonpos h ?_
  have hnum : xiLC * (M ^ 2 - (1 - xiLC) * M ^ 2) = xiLC ^ 2 * M ^ 2 := by ring
  rw [hnum]
  positivity

end Diffractive
end DIS
end Scattering
end QFT
end EpsilonEridani
