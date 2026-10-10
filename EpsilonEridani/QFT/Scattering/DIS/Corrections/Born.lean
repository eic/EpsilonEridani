/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.QFT.Scattering.DIS.Kinematics.Domain

/-!
# The Born cross section as data on the kinematic domain

The QED radiative corrections to inclusive lepton-nucleon scattering relate an observed cross
section to the Born cross section `d²σ_Born / dx dQ²` of one-photon exchange without radiation.
For the corrections the Born cross section is *data*: no parton content of the target is assumed.
A `BornCrossSection S` is a nonnegative function of `z = (x, Q²)`, supported in the interior of
the kinematic domain `Kinematics.kinematicDomain S` and locally integrable there with respect to
the Lebesgue measure `dx dQ²` on `ℝ × ℝ`.

Local integrability is required only on the open interior, not up to the boundary: the photon
propagator makes a physical cross section grow like `1 / Q⁴` as `Q² → 0`, so it need not be
integrable over the whole domain. Since a Born cross section vanishes off the interior, it is
determined by its values there (`BornCrossSection.ext_of_eqOn_interior`).

## Main definitions

* `BornCrossSection S`: a Born cross section on the kinematic domain at `S = 2 P·k`.
* `BornCrossSection.ofLocallyIntegrableOn`: the Born cross section given by a function that is
  nonnegative and locally integrable on the interior of the domain, extended by zero.

## References

* L. W. Mo and Y. S. Tsai, *Radiative corrections to elastic and inelastic ep and μp scattering*,
  Rev. Mod. Phys. **41** (1969) 205.
-/

public section

noncomputable section

namespace EpsilonEridani
namespace QFT
namespace Scattering
namespace DIS
namespace Corrections

open Set MeasureTheory Kinematics

/-- A Born cross section `d²σ_Born / dx dQ²` on the kinematic domain at `S = 2 P·k`: a
nonnegative function of `z = (x, Q²)` that vanishes off the interior of `kinematicDomain S` and is
locally integrable on that interior with respect to `dx dQ²`. -/
structure BornCrossSection (S : ℝ) where
  /-- The value of the cross section at `z = (x, Q²)`. -/
  toFun : ℝ × ℝ → ℝ
  nonneg' : ∀ z, 0 ≤ toFun z
  support_subset' : Function.support toFun ⊆ interior (kinematicDomain S)
  locallyIntegrableOn' : LocallyIntegrableOn toFun (interior (kinematicDomain S))

namespace BornCrossSection

variable {S : ℝ}

instance : FunLike (BornCrossSection S) (ℝ × ℝ) ℝ where
  coe σ := σ.toFun
  coe_injective σ τ h := by
    cases σ
    cases τ
    congr

@[simp] lemma toFun_eq_coe (σ : BornCrossSection S) : σ.toFun = ⇑σ := (rfl)

@[simp] lemma coe_mk (f : ℝ × ℝ → ℝ) (h₀ hs hi) :
    ⇑(⟨f, h₀, hs, hi⟩ : BornCrossSection S) = f := (rfl)

@[ext] lemma ext {σ τ : BornCrossSection S} (h : ∀ z, σ z = τ z) : σ = τ :=
  DFunLike.ext σ τ h

lemma nonneg (σ : BornCrossSection S) (z : ℝ × ℝ) : 0 ≤ σ z :=
  σ.nonneg' z

lemma support_subset (σ : BornCrossSection S) :
    Function.support σ ⊆ interior (kinematicDomain S) :=
  σ.support_subset'

lemma locallyIntegrableOn (σ : BornCrossSection S) :
    LocallyIntegrableOn σ (interior (kinematicDomain S)) :=
  σ.locallyIntegrableOn'

lemma eq_zero_of_notMem_interior (σ : BornCrossSection S) {z : ℝ × ℝ}
    (hz : z ∉ interior (kinematicDomain S)) : σ z = 0 :=
  Function.notMem_support.1 fun h => hz (σ.support_subset h)

/-- A Born cross section is determined by its values on the interior of the kinematic domain. -/
theorem ext_of_eqOn_interior {σ τ : BornCrossSection S}
    (h : EqOn σ τ (interior (kinematicDomain S))) : σ = τ := by
  ext z
  by_cases hz : z ∈ interior (kinematicDomain S)
  · exact h hz
  · rw [σ.eq_zero_of_notMem_interior hz, τ.eq_zero_of_notMem_interior hz]

/-- The Born cross section given by a function `f` that is nonnegative and locally integrable on
the interior of the kinematic domain, extended by zero off it. -/
def ofLocallyIntegrableOn (f : ℝ × ℝ → ℝ)
    (hf : LocallyIntegrableOn f (interior (kinematicDomain S)))
    (hf₀ : ∀ z ∈ interior (kinematicDomain S), 0 ≤ f z) : BornCrossSection S where
  toFun := (interior (kinematicDomain S)).indicator f
  nonneg' := indicator_nonneg hf₀
  support_subset' := support_indicator_subset
  locallyIntegrableOn' :=
    hf.congr (indicator_ae_eq_restrict isOpen_interior.measurableSet).symm

@[simp] lemma coe_ofLocallyIntegrableOn (f : ℝ × ℝ → ℝ)
    (hf : LocallyIntegrableOn f (interior (kinematicDomain S)))
    (hf₀ : ∀ z ∈ interior (kinematicDomain S), 0 ≤ f z) :
    ⇑(ofLocallyIntegrableOn f hf hf₀) = (interior (kinematicDomain S)).indicator f := (rfl)

lemma ofLocallyIntegrableOn_apply_of_mem {f : ℝ × ℝ → ℝ}
    {hf : LocallyIntegrableOn f (interior (kinematicDomain S))}
    {hf₀ : ∀ z ∈ interior (kinematicDomain S), 0 ≤ f z} {z : ℝ × ℝ}
    (hz : z ∈ interior (kinematicDomain S)) : ofLocallyIntegrableOn f hf hf₀ z = f z := by
  rw [coe_ofLocallyIntegrableOn, indicator_of_mem hz]

/-- Every Born cross section is the one built from its own values by `ofLocallyIntegrableOn`. -/
@[simp] lemma ofLocallyIntegrableOn_coe (σ : BornCrossSection S) :
    ofLocallyIntegrableOn σ σ.locallyIntegrableOn (fun z _ => σ.nonneg z) = σ :=
  ext_of_eqOn_interior fun _ hz => ofLocallyIntegrableOn_apply_of_mem hz

/-- The Rutherford-like profile `1 / (x Q⁴)` of one-photon exchange is a Born cross section on
every kinematic domain, although it is not integrable up to the boundary `Q² = 0`. -/
example (S : ℝ) : BornCrossSection S :=
  ofLocallyIntegrableOn (fun z => (z.1 * z.2 ^ 2)⁻¹)
    (((continuous_fst.mul (continuous_snd.pow 2)).continuousOn.inv₀ fun z hz => by
      rw [interior_kinematicDomain] at hz
      exact mul_ne_zero hz.1.ne' (pow_ne_zero 2 hz.2.2.1.ne')).locallyIntegrableOn
        isOpen_interior.measurableSet)
    fun z hz => by
      rw [interior_kinematicDomain] at hz
      have := hz.1
      have := hz.2.2.1
      positivity

end BornCrossSection

end Corrections
end DIS
end Scattering
end QFT
end EpsilonEridani
