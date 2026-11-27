/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.Particles.Meson.Basic
public import EpsilonEridani.QFT.Scattering.Elastic.FormFactor.Basic

/-!
# The electromagnetic form factor of the positive pion

The elastic electromagnetic form factor of a spin-zero state, its charge normalisation, the
quantity `6 dF/dt (0)` (the squared charge radius `⟨r²⟩` of a form factor normalised to unit
charge) and the single-pole form factor `F(t) = e Λ² / (Λ² - t)` are developed for an arbitrary
spin-zero state in `EpsilonEridani.QFT.Scattering.Elastic.FormFactor.Basic`. This file
instantiates the single-pole form factor at the charge `1` of the positive pion, so that
`6 dF/dt (0)` is its squared charge radius, `6 / Λ²`
(`FormFactor.chargeRadiusSq_singlePole_piPlus`).

## References

* S. R. Amendolia et al. (NA7), *A measurement of the space-like pion electromagnetic form
  factor*, Nucl. Phys. B 277 (1986) 168: the charge radius as `6 dF/dt (0)` and the single-pole
  fit.
-/

public section

namespace EpsilonEridani.Particles.Meson.FormFactor

open EpsilonEridani.QFT.Scattering.Elastic.FormFactor (chargeRadiusSq singlePole
  chargeRadiusSq_singlePole)

/-- The single-pole form factor of the positive pion, normalised to the pion's unit charge, has
squared charge radius `6 / Λ²`, six times the reciprocal of the squared pole mass. -/
theorem chargeRadiusSq_singlePole_piPlus {Λsq : ℝ} (hΛ : Λsq ≠ 0) :
    chargeRadiusSq (singlePole piPlus.charge Λsq) = 6 / Λsq := by
  rw [chargeRadiusSq_singlePole _ hΛ, piPlus_charge, mul_one]

end EpsilonEridani.Particles.Meson.FormFactor
