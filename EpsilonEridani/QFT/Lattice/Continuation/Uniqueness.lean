/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.Mathematics.Analysis.Analytic.Uniqueness
public import EpsilonEridani.QFT.Lattice.Continuation.Basic

/-!
# Uniqueness of the continuation from the Euclidean section

A matrix element computed in Euclidean space is a function on the Euclidean section
`euclideanSection d` of the complexified separation space. Its Minkowski counterpart is the
holomorphic function on an open connected *analyticity domain* `U ⊆ ComplexSeparation d` that
restricts to it there. This file proves that this counterpart is unique: two functions holomorphic
on `U` that agree at the Euclidean points of `U` agree on all of `U`. When `U` contains every
spacelike Minkowski separation, as the analyticity domain of a matrix element does, the two
functions therefore agree at every spacelike separation.

Holomorphy on `U` is a hypothesis of every statement here (`AnalyticOnNhd ℂ f U`). It is what a
Wightman-axiomatic or reflection-positive construction supplies, and nothing in this file
constructs it.

The analyticity domain is not required to contain the origin. An open set containing the origin
contains nonzero null separations close to it, so a domain whose boundary contains every nonzero
null separation does not contain the origin. All that the uniqueness needs is a single point of
the Euclidean section in `U`.

## Main results

* `eqOn_of_eventuallyEq_continuation`: two functions holomorphic on a preconnected set `U` that
  agree at the continuations of the Euclidean separations near one point `x₀` with
  `continuation x₀ ∈ U` agree on all of `U`.
* `eqOn_of_eqOn_euclideanSection`: two functions holomorphic on an open preconnected set `U` that
  meets the Euclidean section, and that agree on `U ∩ euclideanSection d`, agree on `U`.
* `eq_of_eqOn_euclideanSection_of_spaceLike`: if `U` also contains every spacelike Minkowski
  separation, the two functions agree at every spacelike separation. The equal-time projection of a
  spacelike separation is a point of `U` on the Euclidean section, so no separate hypothesis that
  `U` meets the Euclidean section is needed.

## References

* K. Osterwalder and R. Schrader, *Axioms for Euclidean Green's functions*, Commun. Math. Phys.
  31 (1973) 83.
* R. F. Streater and A. S. Wightman, *PCT, Spin and Statistics, and All That*, Chapter 3.

## Implementation notes

The Euclidean section is not an open subset of `ComplexSeparation d`, so Mathlib's identity
theorem does not apply to it directly. It is, however, the image of the real slice `ℝ^{1+d}` under
the Wick rotation `wickRotation` (`wickRotation_ofReal`, `preimage_wickRotation_euclideanSection`),
which makes it a maximal totally real subspace. The uniqueness therefore reduces to
`AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq_ofReal`, whose hypothesis is agreement at the
real points near one real point.
-/

public section

namespace EpsilonEridani
namespace QFT
namespace Lattice
namespace Continuation

open Complex Filter Lorentz Lorentz.Vector Set Topology

variable {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- **Uniqueness of the continuation, local form.** Two functions holomorphic on a preconnected
set `U` that agree at the continuations of all Euclidean separations near a point `x₀` with
`continuation x₀ ∈ U` agree on all of `U`. -/
theorem eqOn_of_eventuallyEq_continuation {f g : ComplexSeparation d → F}
    {U : Set (ComplexSeparation d)} (hf : AnalyticOnNhd ℂ f U) (hg : AnalyticOnNhd ℂ g U)
    (hU : IsPreconnected U) {x₀ : EuclideanSeparation d} (h₀ : continuation x₀ ∈ U)
    (hfg : (fun x => f (continuation x)) =ᶠ[𝓝 x₀] fun x => g (continuation x)) :
    EqOn f g U := by
  -- Pull everything back along the Wick rotation, which turns the Euclidean section into the
  -- real slice.
  set e : ComplexSeparation d ≃L[ℂ] ComplexSeparation d := wickRotation
  have he : AnalyticOnNhd ℂ e (e ⁻¹' U) := e.toContinuousLinearMap.analyticOnNhd _
  have hU' : IsPreconnected (e ⁻¹' U) := e.toHomeomorph.isPreconnected_preimage.2 hU
  have hT : Tendsto (WithLp.toLp 2) (𝓝 (WithLp.ofLp x₀)) (𝓝 x₀) := by
    simpa using (PiLp.continuous_toLp 2 _).tendsto (WithLp.ofLp x₀)
  have key : EqOn (f ∘ e) (g ∘ e) (e ⁻¹' U) :=
    (hf.comp he fun _ hz => hz).eqOn_of_preconnected_of_eventuallyEq_ofReal
      (hg.comp he fun _ hz => hz) hU' (x₀ := WithLp.ofLp x₀)
      (by simpa [e] using h₀)
      ((hT.eventually hfg).mono fun y hy => by simpa [e] using hy)
  intro z hz
  simpa using key (x := e.symm z) (by simpa using hz)

/-- **Uniqueness of the continuation.** Two functions holomorphic on an open preconnected set `U`
that meets the Euclidean section, and that agree at every point of `U` on the Euclidean section,
agree on all of `U`. -/
theorem eqOn_of_eqOn_euclideanSection {f g : ComplexSeparation d → F}
    {U : Set (ComplexSeparation d)} (hf : AnalyticOnNhd ℂ f U) (hg : AnalyticOnNhd ℂ g U)
    (hUo : IsOpen U) (hU : IsPreconnected U)
    (hne : (U ∩ (euclideanSection d : Set (ComplexSeparation d))).Nonempty)
    (hfg : EqOn f g (U ∩ (euclideanSection d : Set (ComplexSeparation d)))) :
    EqOn f g U := by
  obtain ⟨_, hzU, hzE⟩ := hne
  rw [SetLike.mem_coe, euclideanSection_def] at hzE
  obtain ⟨x₀, rfl⟩ := hzE
  have hc : Continuous (continuation (d := d)) := LinearMap.continuous_of_finiteDimensional _
  refine eqOn_of_eventuallyEq_continuation hf hg hU hzU ?_
  filter_upwards [hc.continuousAt.preimage_mem_nhds (hUo.mem_nhds hzU)] with x hx
  exact hfg ⟨hx, by rw [SetLike.mem_coe, euclideanSection_def]; exact LinearMap.mem_range_self _ x⟩

/-- **The Euclidean values determine the spacelike values.** Two functions holomorphic on an
open preconnected set `U` that contains every spacelike Minkowski separation, and that agree at
every point of `U` on the Euclidean section, agree at every spacelike Minkowski separation. -/
theorem eq_of_eqOn_euclideanSection_of_spaceLike {f g : ComplexSeparation d → F}
    {U : Set (ComplexSeparation d)} (hf : AnalyticOnNhd ℂ f U) (hg : AnalyticOnNhd ℂ g U)
    (hUo : IsOpen U) (hU : IsPreconnected U)
    (hspace : ∀ v : Vector d, causalCharacter v = .spaceLike → ofMinkowski v ∈ U)
    (hfg : EqOn f g (U ∩ (euclideanSection d : Set (ComplexSeparation d))))
    {v : Vector d} (hv : causalCharacter v = .spaceLike) :
    f (ofMinkowski v) = g (ofMinkowski v) := by
  -- The equal-time projection of `v` is a spacelike point of `U` on the Euclidean section.
  have hwE := ofMinkowski_sub_timeComponent_smul_basis_mem_euclideanSection v
  have hw := causalCharacter_sub_timeComponent_smul_basis_eq_spaceLike hv
  exact eqOn_of_eqOn_euclideanSection hf hg hUo hU ⟨_, hspace _ hw, hwE⟩ hfg (hspace v hv)

end Continuation
end Lattice
end QFT
end EpsilonEridani
