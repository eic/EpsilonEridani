/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.Particles.Meson.Basic
public import EpsilonEridani.Particles.Parton.PDF.Basic
public import EpsilonEridani.QFT.Scattering.DIS.CrossSection

/-!
# Isospin, the neutron, and the proton-neutron difference of `F₂`

In the quark-parton model the neutral-current structure function of a target is
`F₂ = x Σ_f e_f² (q_f + qbar_f)` (`DIS.f2LO`), where `q_f + qbar_f` is the target's quark plus
antiquark density of flavour `f`. Exact isospin symmetry relates the neutron to the proton: the
neutron's densities are the proton's with up and down exchanged, `q^n_f = q^p_{τ f}` with
`τ = Equiv.swap u d` the isospin involution, which fixes every other flavour. The neutron density
is therefore the pullback `PDF.comap τ q^p`; that the two nucleons are related this way is the
assumption of exact isospin symmetry, and its violation is not modelled here. Since `F₂` sees only
the combination `q_f + qbar_f`, relabelling the flavours of that combination is all the neutron
needs.

Relabelling the flavours of a density is the same as relabelling the charges the other way
(`f2LO_comap`), so the neutron is the proton with the up and down charges exchanged. Every flavour
other than up and down then drops out of the difference:

  `F₂^p - F₂^n = x (e_u² - e_d²) ((u + ubar) - (d + dbar))`  (`f2LO_sub_f2LO_comap_swap`),

which for the light flavours, `e_u = 2/3` and `e_d = e_s = -1/3`, is the identity
`F₂^p - F₂^n = (x / 3) (u + ubar - d - dbar)` (`f2LO_charge_sub_f2LO_charge_comap_swap`) whose
`dx / x` integral is the Gottfried sum.

The ratio `F₂^p / F₂^n` at large `x` is not fixed by isospin. It is fixed by the limits of the
density ratios: if, along a filter on which `x` and a common reference function are eventually
non-zero, every `q_f + qbar_f` is asymptotically `ρ_f` times that reference function, then `F₂`
with charges `e` over `F₂` with charges `e'` tends to `Σ e_f² ρ_f / Σ e'_f² ρ_f` whenever the
limiting denominator is non-zero (`tendsto_f2LO_div_f2LO`); the neutron is the case
`e' = e ∘ τ`. When every density other than up is negligible against the up density this limit
is `e_u² / e_d²` (`tendsto_f2LO_div_f2LO_comap_swap_of_tendsto_zero`). For the light flavours
with `d/u → r` and `s/u → t` the ratio tends to `(4 + r + t) / (1 + 4 r + t)` provided
`1 + 4 r + t ≠ 0` (`tendsto_f2LO_charge_div_f2LO_charge_comap_swap`), and the familiar value `4`
as `x → 1` is the conditional statement that the down and strange densities are negligible
against the up density there (`tendsto_f2LO_charge_div_f2LO_charge_comap_swap_nhdsLT_one`).
Whether they are is an open experimental question, which is why the hypothesis is stated rather
than assumed.

## Main results

* `f2LO_comap`: `F₂` of a density with relabelled flavours is `F₂` with the inverse relabelling
  of the charges.
* `f2LO_sub_f2LO_comap_swap`: the proton-neutron difference `x (e_u² - e_d²) (q_u - q_d)`.
* `f2LO_charge_sub_f2LO_charge_comap_swap`: the light-flavour difference `(x / 3) (q_u - q_d)`.
* `tendsto_f2LO_div_f2LO`: the limit of a ratio of two charge-weightings of `F₂` in terms of the
  limits of the density ratios.
* `tendsto_f2LO_div_f2LO_comap_swap_of_tendsto_zero`: `F₂^p / F₂^n → e_u² / e_d²` when every
  other density is negligible against the up density.
* `tendsto_f2LO_charge_div_f2LO_charge_comap_swap_nhdsLT_one`: `F₂^p / F₂^n → 4` as `x → 1⁻`
  when the down and strange densities are negligible against the up density.

## References

* K. Gottfried, *Sum rule for high-energy electron-proton scattering*,
  Phys. Rev. Lett. **18** (1967) 1174.
* R. Devenish and A. Cooper-Sarkar, *Deep Inelastic Scattering*, Oxford University Press (2004),
  ch. 5.
* F. Halzen and A. D. Martin, *Quarks and Leptons*, Wiley (1984), ch. 9.
-/

public section

namespace EpsilonEridani
namespace QFT
namespace Scattering
namespace DIS
namespace Inclusive

open Filter Topology
open Particles.Parton.PDF (Pdf comap comap_apply)
open Particles.Meson (LightFlavor)

/-!
## Relabelling flavours, and the proton-neutron difference
-/

section General

variable {ι κ : Type} [Fintype ι] [Fintype κ]

/-- **Relabelling the flavours of a density is relabelling the charges the other way.** For a
bijection `σ` of flavour types, the leading-order `F₂` of the density `q ∘ σ` with charges `e` is
the `F₂` of `q` with charges `e ∘ σ⁻¹`. -/
@[simp]
theorem f2LO_comap (σ : κ ≃ ι) (e : κ → ℝ) (q : Pdf ι) (x Q2 : ℝ) :
    f2LO e (comap σ q) x Q2 = f2LO (e ∘ σ.symm) q x Q2 := by
  simp only [f2LO_def, comap_apply, Function.comp_apply]
  rw [← σ.sum_comp fun i => e (σ.symm i) ^ 2 * q i x Q2]
  simp

/-- **The limiting ratio of `F₂` under two charge assignments.** If, along a filter `l` on which
`x` and a reference function `w` are eventually non-zero, every density `q i` is asymptotically
`ρ i` times `w`, then `F₂` with charges `e` over `F₂` with charges `e'` tends to
`Σ e_i² ρ_i / Σ e'_i² ρ_i`, provided the limiting denominator does not vanish. With
`e' = e ∘ swap u d` this is the limit of `F₂^p / F₂^n`, by `f2LO_comap`. -/
theorem tendsto_f2LO_div_f2LO {e e' : ι → ℝ} {q : Pdf ι} {Q2 : ℝ} {l : Filter ℝ} {w : ℝ → ℝ}
    {ρ : ι → ℝ} (hx : ∀ᶠ x in l, x ≠ 0) (hw : ∀ᶠ x in l, w x ≠ 0)
    (hq : ∀ i, Tendsto (fun x => q i x Q2 / w x) l (𝓝 (ρ i)))
    (hρ : ∑ i, e' i ^ 2 * ρ i ≠ 0) :
    Tendsto (fun x => f2LO e q x Q2 / f2LO e' q x Q2) l
      (𝓝 ((∑ i, e i ^ 2 * ρ i) / ∑ i, e' i ^ 2 * ρ i)) := by
  have hlim (c : ι → ℝ) :
      Tendsto (fun x => ∑ i, c i ^ 2 * (q i x Q2 / w x)) l (𝓝 (∑ i, c i ^ 2 * ρ i)) :=
    tendsto_finsetSum _ fun i _ => (hq i).const_mul (c i ^ 2)
  refine ((hlim e).div (hlim e') hρ).congr' ?_
  filter_upwards [hx, hw] with x hx hw
  have h (c : ι → ℝ) : f2LO c q x Q2 = x * w x * ∑ i, c i ^ 2 * (q i x Q2 / w x) := by
    rw [f2LO_def, mul_assoc, Finset.mul_sum (a := w x)]
    refine congrArg (x * ·) (Finset.sum_congr rfl fun i _ => ?_)
    field_simp
  rw [Pi.div_apply, h, h, mul_div_mul_left _ _ (mul_ne_zero hx hw)]

variable [DecidableEq ι]

/-- **The proton-neutron difference of `F₂`.** Under the isospin involution `τ = swap u d` every
flavour other than `u` and `d` drops out of `F₂^p - F₂^n`, which is
`x (e_u² - e_d²) (q_u - q_d)`. -/
theorem f2LO_sub_f2LO_comap_swap (e : ι → ℝ) (q : Pdf ι) (u d : ι) (x Q2 : ℝ) :
    f2LO e q x Q2 - f2LO e (comap (Equiv.swap u d) q) x Q2
      = x * (e u ^ 2 - e d ^ 2) * (q u x Q2 - q d x Q2) := by
  rw [f2LO_comap, Equiv.symm_swap, f2LO_def, f2LO_def]
  simp only [Function.comp_apply]
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  rcases eq_or_ne u d with rfl | hud
  · simp
  rw [Fintype.sum_eq_add u d hud fun i hi => by
    rw [Equiv.swap_apply_of_ne_of_ne hi.1 hi.2, sub_self]]
  rw [Equiv.swap_apply_left, Equiv.swap_apply_right]
  ring

/-- **`F₂^p / F₂^n → e_u² / e_d²` when the up density dominates.** If, along a filter `l` on which
`x` and the density `q u` are eventually non-zero, every other density is negligible against
`q u`, then `F₂^p / F₂^n` tends to `e_u² / e_d²`, where the neutron is the proton under the
isospin involution `swap u d`, provided `e_d ≠ 0`. -/
theorem tendsto_f2LO_div_f2LO_comap_swap_of_tendsto_zero {e : ι → ℝ} {q : Pdf ι} {u d : ι}
    {Q2 : ℝ} {l : Filter ℝ} (hx : ∀ᶠ x in l, x ≠ 0) (hu : ∀ᶠ x in l, q u x Q2 ≠ 0)
    (hd : e d ≠ 0) (h : ∀ i, i ≠ u → Tendsto (fun x => q i x Q2 / q u x Q2) l (𝓝 0)) :
    Tendsto (fun x => f2LO e q x Q2 / f2LO e (comap (Equiv.swap u d) q) x Q2) l
      (𝓝 (e u ^ 2 / e d ^ 2)) := by
  have hq : ∀ i, Tendsto (fun x => q i x Q2 / q u x Q2) l (𝓝 (if i = u then 1 else 0)) := by
    intro i
    rcases eq_or_ne i u with rfl | hi
    · simpa using tendsto_const_nhds.congr' (hu.mono fun x hx => (div_self hx).symm)
    · simpa [hi] using h i hi
  have hρ : ∑ i, (e ∘ Equiv.swap u d) i ^ 2 * (if i = u then 1 else 0) ≠ 0 := by
    simpa using hd
  simpa using tendsto_f2LO_div_f2LO hx hu hq hρ

end General

/-!
## The light flavours
-/

section LightFlavor

open EpsilonEridani.Particles.Meson.LightFlavor

/-- **The light-flavour proton-neutron difference of `F₂`.** With the light-quark charges,
`F₂^p - F₂^n = (x / 3) (q_u - q_d)`: for `q_f` the quark plus antiquark density this is
`(x / 3) (u + ubar - d - dbar)`, the integrand of the Gottfried sum after division by `x`. -/
theorem f2LO_charge_sub_f2LO_charge_comap_swap (q : Pdf LightFlavor) (x Q2 : ℝ) :
    f2LO charge q x Q2 - f2LO charge (comap (Equiv.swap u d) q) x Q2
      = x / 3 * (q u x Q2 - q d x Q2) := by
  rw [f2LO_sub_f2LO_comap_swap, charge_u, charge_d]
  ring

/-- **The light-flavour ratio `F₂^p / F₂^n` in terms of `d / u` and `s / u`.** If, along a filter
avoiding `x = 0` on which the up density is eventually non-zero, the down and strange densities
are asymptotically `r` and `t` times the up density, and `1 + 4 r + t ≠ 0`, then
`F₂^p / F₂^n → (4 + r + t) / (1 + 4 r + t)`. -/
theorem tendsto_f2LO_charge_div_f2LO_charge_comap_swap {q : Pdf LightFlavor} {Q2 : ℝ}
    {l : Filter ℝ} {r t : ℝ} (hx : ∀ᶠ x in l, x ≠ 0) (hu : ∀ᶠ x in l, q u x Q2 ≠ 0)
    (hd : Tendsto (fun x => q d x Q2 / q u x Q2) l (𝓝 r))
    (hs : Tendsto (fun x => q s x Q2 / q u x Q2) l (𝓝 t)) (hrt : 1 + 4 * r + t ≠ 0) :
    Tendsto (fun x => f2LO charge q x Q2 / f2LO charge (comap (Equiv.swap u d) q) x Q2) l
      (𝓝 ((4 + r + t) / (1 + 4 * r + t))) := by
  have hu' : Tendsto (fun x => q u x Q2 / q u x Q2) l (𝓝 1) :=
    tendsto_const_nhds.congr' <| hu.mono fun x hx => (div_self hx).symm
  let ρ : LightFlavor → ℝ := fun | .u => 1 | .d => r | .s => t
  have hq : ∀ i, Tendsto (fun x => q i x Q2 / q u x Q2) l (𝓝 (ρ i)) := by
    rintro (_ | _ | _)
    exacts [hu', hd, hs]
  have hnum : ∑ i, charge i ^ 2 * ρ i = (4 + r + t) / 9 := by
    simp only [LightFlavor.sum_univ, charge_u, charge_d, charge_s, ρ]
    ring
  have hden : ∑ i, (charge ∘ Equiv.swap u d) i ^ 2 * ρ i = (1 + 4 * r + t) / 9 := by
    simp only [LightFlavor.sum_univ, Function.comp_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne (show s ≠ u by decide)
        (show s ≠ d by decide), charge_u, charge_d, charge_s, ρ]
    ring
  have hρ : ∑ i, (charge ∘ Equiv.swap u d) i ^ 2 * ρ i ≠ 0 := by
    rw [hden]
    exact div_ne_zero hrt (by norm_num)
  have key := tendsto_f2LO_div_f2LO (e := charge) hx hu hq hρ
  rw [hnum, hden, div_div_div_cancel_right₀ (by norm_num : (9 : ℝ) ≠ 0)] at key
  simp only [f2LO_comap, Equiv.symm_swap]
  exact key

/-- **`F₂^p / F₂^n → 4` as `x → 1`, conditionally.** If, as `x → 1` from below, the up density is
eventually non-zero and the down and strange densities are negligible against it, the
proton-neutron ratio of `F₂` tends to `e_u² / e_d² = 4`. -/
theorem tendsto_f2LO_charge_div_f2LO_charge_comap_swap_nhdsLT_one {q : Pdf LightFlavor}
    {Q2 : ℝ} (hu : ∀ᶠ x in 𝓝[<] 1, q u x Q2 ≠ 0)
    (hd : Tendsto (fun x => q d x Q2 / q u x Q2) (𝓝[<] 1) (𝓝 0))
    (hs : Tendsto (fun x => q s x Q2 / q u x Q2) (𝓝[<] 1) (𝓝 0)) :
    Tendsto (fun x => f2LO charge q x Q2 / f2LO charge (comap (Equiv.swap u d) q) x Q2)
      (𝓝[<] 1) (𝓝 4) := by
  have hx : ∀ᶠ x in 𝓝[<] (1 : ℝ), x ≠ 0 :=
    eventually_nhdsWithin_of_eventually_nhds (eventually_ne_nhds one_ne_zero)
  have h : ∀ i, i ≠ u → Tendsto (fun x => q i x Q2 / q u x Q2) (𝓝[<] 1) (𝓝 0) := by
    rintro (_ | _ | _) hi
    exacts [absurd rfl hi, hd, hs]
  convert tendsto_f2LO_div_f2LO_comap_swap_of_tendsto_zero (e := charge) (d := d) hx hu
    (by norm_num) h using 2
  norm_num

end LightFlavor

end Inclusive
end DIS
end Scattering
end QFT
end EpsilonEridani
