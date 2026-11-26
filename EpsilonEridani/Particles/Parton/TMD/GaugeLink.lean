/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Analysis.Convex.Between
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Gauge links along piecewise-linear paths

A gauge-invariant definition of a transverse-momentum-dependent parton correlator joins the
Dirac-adjoint quark field at `0` and the quark field `q(ξ)` by a gauge link `W(0, ξ; path)`, the
path-ordered exponential `P exp(-i g ∫_path A · dz)` of the gauge field along a path from `0` to
`ξ`. Which path is used is part of the definition of the distribution, so the path is explicit
data here.

The path-ordered exponential of a gauge field is not constructed analytically. A `GaugeLink V G`
records the link `W x y` along each straight segment from `x` to `y` in a real vector space `V`
(spacetime), valued in a group `G` (the colour group, such as the unitary group `U(N_c)` in the
fundamental representation), together with the two properties every path-ordered exponential
has along a straight line:

* reversing the segment inverts the link, `W y x = (W x y)⁻¹`;
* the link is multiplicative under subdivision: `W x m * W m y = W x y` for `m` on the segment
  `[x, y]`.

The structural results below follow from these two properties alone, so any later analytic
construction of the link from a gauge potential only has to supply them. Multiplicativity
extends from the segment to every point of the line through `x` and `y`
(`GaugeLink.apply_mul_apply_of_mem_line`); reducing a path whose legs run along the same line in
opposite senses, as the staple's do, needs this off-segment form. The concrete link
`GaugeLink.ofBilin` of a linear abelian gauge potential and its flux formula are a witness, not a
consequence of them.

A piecewise-linear path is recorded by the list of its corners, and the link along it,
`GaugeLink.pathLink`, is the ordered product of the links of its segments. The file proves the
structural properties of the link: composition under concatenation (`pathLink_append_cons`), the
reversed path giving the inverse link (`pathLink_reverse`), conjugation by the gauge
transformation at the two endpoints (`pathLink_smul`), and independence of how a segment is
subdivided (`pathLink_subdivide_of_mem_line`).

The staple path `staplePath v w x y` runs from `x` along `v` to `x + v`, along the far segment `w`
to `x + v + w`, and back to `y`. For a light-like direction `n` (`n₋`), a separation
`y - x = s • n + w` with longitudinal part `s` and transverse part `w`, and `v = L • n`, both legs
run along `n` and the far segment is the transverse displacement `w` at light-cone distance `L`:
`L > 0` gives the future-pointing staple of semi-inclusive deep-inelastic scattering, cut off at
light-cone distance `L`, and `L < 0` the past-pointing staple of the Drell-Yan process. The link
along the far segment is the transverse link, `GaugeLink.transverseLink`. The staple traversed
backwards, from `y` to `x`, gives the inverse link (`pathLink_reverse_staplePath`). When both
legs have trivial links, the whole staple link is carried by the transverse link
(`pathLink_staplePath_eq_transverseLink_of_legs_eq_one`); in axial gauge for `n`
(`IsAxialGauge`), which is light-cone gauge for the light-like `n` and where the links along `n`
are trivial, this holds for every staple of the above shape
(`pathLink_staplePath_eq_transverseLink_of_isAxialGauge`). The transverse link cannot be dropped
there: the link of a linear abelian gauge potential (`GaugeLink.ofBilin`) gives a gauge link in
axial gauge whose staple link and whose transverse link are non-trivial
(`exists_isAxialGauge_pathLink_staplePath_ne_one`), so the staple link differs from the product
of its two legs, which is trivial in that gauge.

The space `V` carries no metric here, so "light-like", "transverse" and "light-cone distance" are
the intended physical reading of the arbitrary vectors `n`, `w` and scalar `L`, not hypotheses of
any result: no statement below requires `n` to be light-like or `w` to be transverse. These
notions are expressible relative to a light-cone basis of a bilinear form, in
`EpsilonEridani.Mathematics.LinearAlgebra.BilinearForm.LightConeBasis`.

## Main definitions

* `EpsilonEridani.Particles.Parton.TMD.GaugeLink V G`: the straight-segment links of a gauge
  field on `V` with values in `G`.
* `GaugeLink.pathLink`: the link along a piecewise-linear path given by its corners.
* The action of gauge transformations `Ω : V → G` on gauge links, `(Ω • W) x y = Ω x * W x y *
  (Ω y)⁻¹`, as a `MulAction`.
* `staplePath`, `GaugeLink.transverseLink`: the staple path and the link along its far
  segment.
* `GaugeLink.IsAxialGauge`: the links along a direction `n` are trivial (light-cone gauge for
  light-like `n`).
* `GaugeLink.ofBilin`: the gauge link of the linear abelian gauge potential `A(z) · w = B z w`.

## References

* J. C. Collins, *Foundations of Perturbative QCD*, Cambridge University Press (2011), §7.6 and
  §13.4 for gauge links and their path dependence.
* X. Ji and F. Yuan, *Parton distributions in light-cone gauge: where are the final-state
  interactions?*, Phys. Lett. B 543 (2002) 66, arXiv:hep-ph/0206057.
* A. V. Belitsky, X. Ji and F. Yuan, *Final state interactions and gauge invariant parton
  distributions*, Nucl. Phys. B 656 (2003) 165, arXiv:hep-ph/0208038.
-/

public section

noncomputable section

namespace EpsilonEridani
namespace Particles
namespace Parton
namespace TMD

/-- The gauge links of a gauge field along straight segments: a family of elements `W x y` of the
gauge group `G`, to be read as the path-ordered exponential of a gauge field along the segment from
`x` to `y`. The gauge field is not part of the data. The two fields, inversion under reversing the
segment and multiplicativity under subdividing it, are properties every path-ordered exponential
has along a straight line, not a characterisation of the links that come from a gauge field. -/
structure GaugeLink (V G : Type*) [AddCommGroup V] [Module ℝ V] [Group G] where
  /-- The link along the segment from `x` to `y`. -/
  toFun : V → V → G
  /-- Reversing a segment inverts its link. -/
  toFun_swap' : ∀ x y, toFun y x = (toFun x y)⁻¹
  /-- The link is multiplicative under subdivision of a segment. -/
  toFun_mul_toFun' : ∀ x y m, m ∈ segment ℝ x y → toFun x m * toFun m y = toFun x y

namespace GaugeLink

variable {V G : Type*} [AddCommGroup V] [Module ℝ V] [Group G]

instance : FunLike (GaugeLink V G) V (V → G) where
  coe := toFun
  coe_injective W₁ W₂ h := by cases W₁; cases W₂; congr

@[simp]
theorem toFun_eq_coe (W : GaugeLink V G) : W.toFun = W := (rfl)

@[simp]
theorem coe_mk (f : V → V → G) (h₁ h₂) : ⇑(⟨f, h₁, h₂⟩ : GaugeLink V G) = f := (rfl)

@[ext]
theorem ext {W₁ W₂ : GaugeLink V G} (h : ∀ x y, W₁ x y = W₂ x y) : W₁ = W₂ :=
  DFunLike.ext _ _ fun x => funext (h x)

/-- Reversing a segment inverts its link. -/
theorem apply_swap (W : GaugeLink V G) (x y : V) : W y x = (W x y)⁻¹ :=
  W.toFun_swap' x y

/-- The link is multiplicative under subdivision of a segment at any point of the line through
its endpoints: `W x m * W m y = W x y` also when `m` lies outside the segment `[x, y]`. -/
theorem apply_mul_apply_of_mem_line (W : GaugeLink V G) {x y m : V} (hm : m ∈ line[ℝ, x, y]) :
    W x m * W m y = W x y := by
  rcases (collinear_insert_of_mem_affineSpan_pair hm).wbtw_or_wbtw_or_wbtw with h | h | h
  · -- `x` lies between `m` and `y`, so subdivide the segment from `m` to `y` at `x`.
    have hW : W m x * W x y = W m y := W.toFun_mul_toFun' m y x (mem_segment_iff_wbtw.2 h)
    rw [← hW, W.apply_swap x m, mul_inv_cancel_left]
  · -- `y` lies between `x` and `m`, so subdivide the segment from `x` to `m` at `y`.
    have hW : W x y * W y m = W x m := W.toFun_mul_toFun' x m y (mem_segment_iff_wbtw.2 h)
    rw [← hW, W.apply_swap m y, inv_mul_cancel_right]
  · -- `m` lies between `y` and `x`; reversing the order of the endpoints, this is the
    -- subdivision property itself.
    exact W.toFun_mul_toFun' x y m (mem_segment_iff_wbtw.2 h.symm)

/-- The link is multiplicative under subdivision of a segment. -/
theorem apply_mul_apply_of_mem_segment (W : GaugeLink V G) {x y m : V} (hm : m ∈ segment ℝ x y) :
    W x m * W m y = W x y :=
  W.toFun_mul_toFun' x y m hm

/-- The link along a degenerate segment is trivial. -/
@[simp]
theorem apply_self (W : GaugeLink V G) (x : V) : W x x = 1 := by
  simpa using W.apply_mul_apply_of_mem_segment (left_mem_segment ℝ x x)

/-! ### Gauge transformations -/

/-- A gauge transformation `Ω : V → G` acts on gauge links by conjugation with its values at the
two endpoints of each segment: `(Ω • W) x y = Ω x * W x y * (Ω y)⁻¹`. -/
instance : SMul (V → G) (GaugeLink V G) where
  smul Ω W :=
    { toFun x y := Ω x * W x y * (Ω y)⁻¹
      toFun_swap' x y := by simp [W.apply_swap x y, mul_assoc]
      toFun_mul_toFun' x y m hm := by
        simp only [mul_assoc, inv_mul_cancel_left, ← W.apply_mul_apply_of_mem_segment hm] }

@[simp]
theorem smul_apply (Ω : V → G) (W : GaugeLink V G) (x y : V) :
    (Ω • W) x y = Ω x * W x y * (Ω y)⁻¹ := (rfl)

/-- Gauge transformations act on gauge links: composing two gauge transformations composes
their actions. -/
instance : MulAction (V → G) (GaugeLink V G) where
  one_smul W := by ext x y; simp
  mul_smul Ω₁ Ω₂ W := by ext x y; simp [mul_assoc]

/-! ### The link along a piecewise-linear path -/

/-- The link along the piecewise-linear path with the given list of corners: the ordered product
`W x₀ x₁ * W x₁ x₂ * ⋯ * W xₙ₋₁ xₙ` of the links of its segments. A path with at most one corner
has trivial link. -/
def pathLink (W : GaugeLink V G) : List V → G
  | [] => 1
  | [_] => 1
  | x :: y :: l => W x y * pathLink W (y :: l)

@[simp]
theorem pathLink_nil (W : GaugeLink V G) : W.pathLink [] = 1 := by
  rw [pathLink]

@[simp]
theorem pathLink_singleton (W : GaugeLink V G) (x : V) : W.pathLink [x] = 1 := by
  rw [pathLink]

@[simp]
theorem pathLink_cons_cons (W : GaugeLink V G) (x y : V) (l : List V) :
    W.pathLink (x :: y :: l) = W x y * W.pathLink (y :: l) := by
  rw [pathLink]

/-- **Composition under concatenation**: the link along a path through the corner `y` is the
product of the links of the part before `y` and the part after `y`. -/
theorem pathLink_append_cons (W : GaugeLink V G) (l₁ l₂ : List V) (y : V) :
    W.pathLink (l₁ ++ y :: l₂) = W.pathLink (l₁ ++ [y]) * W.pathLink (y :: l₂) := by
  induction l₁ with
  | nil => simp
  | cons a l ih =>
    cases l with
    | nil => simp
    | cons b l =>
      simp only [List.cons_append, pathLink_cons_cons] at ih ⊢
      rw [ih, mul_assoc]

/-- **The reversed path gives the inverse link.** -/
@[simp]
theorem pathLink_reverse (W : GaugeLink V G) (l : List V) :
    W.pathLink l.reverse = (W.pathLink l)⁻¹ := by
  induction l with
  | nil => simp
  | cons a l ih =>
    cases l with
    | nil => simp
    | cons b l =>
      simp only [List.reverse_cons, List.append_assoc, List.singleton_append] at ih ⊢
      rw [pathLink_append_cons, ih]
      simp [W.apply_swap b a]

/-- **Gauge covariance**: under a gauge transformation the link along a path is conjugated by the
gauge transformation at its two endpoints. -/
theorem pathLink_smul (Ω : V → G) (W : GaugeLink V G) (x : V) (l : List V) :
    (Ω • W).pathLink (x :: l) =
      Ω x * W.pathLink (x :: l) * (Ω ((x :: l).getLast (List.cons_ne_nil x l)))⁻¹ := by
  induction l generalizing x with
  | nil => simp
  | cons y l ih =>
    rw [pathLink_cons_cons, pathLink_cons_cons, ih, List.getLast_cons (List.cons_ne_nil y l),
      smul_apply]
    group

/-- **Independence of the subdivision**: inserting a corner anywhere on the line through a
segment of a path does not change the link along it. In particular a corner followed by a later
corner may be repeated (take `m = x`). -/
theorem pathLink_subdivide_of_mem_line (W : GaugeLink V G) (l₁ l₂ : List V) {x y m : V}
    (hm : m ∈ line[ℝ, x, y]) :
    W.pathLink (l₁ ++ x :: m :: y :: l₂) = W.pathLink (l₁ ++ x :: y :: l₂) := by
  rw [pathLink_append_cons, pathLink_append_cons W l₁ (y :: l₂), pathLink_cons_cons,
    pathLink_cons_cons,
    pathLink_cons_cons, ← mul_assoc (W x m), W.apply_mul_apply_of_mem_line hm]

/-- **Independence of the subdivision of a segment**: inserting a corner on a segment of a path
does not change the link along it. -/
theorem pathLink_subdivide_of_mem_segment (W : GaugeLink V G) (l₁ l₂ : List V) {x y m : V}
    (hm : m ∈ segment ℝ x y) :
    W.pathLink (l₁ ++ x :: m :: y :: l₂) = W.pathLink (l₁ ++ x :: y :: l₂) :=
  W.pathLink_subdivide_of_mem_line l₁ l₂ ((mem_segment_iff_wbtw.1 hm).mem_affineSpan)

/-! ### Staples and the transverse link -/

end GaugeLink

section staplePath

variable {V : Type*} [AddCommGroup V]

/-- The staple path from `x` to `y` with leg `v` and far segment `w`: the path with corners `x`,
`x + v`, `x + v + w`, `y`. For a light-like direction `n`, `v = L • n` and `y - x = s • n + w` it
runs out along `n` to light-cone distance `L`, along the transverse separation `w`, and back along
`n`; `L > 0` gives the future-pointing staple and `L < 0` the past-pointing staple. -/
def staplePath (v w x y : V) : List V := [x, x + v, x + v + w, y]

theorem staplePath_def (v w x y : V) : staplePath v w x y = [x, x + v, x + v + w, y] := (rfl)

/-- The reverse of a staple path is the staple path from `y` to `x` whose first leg ends at
`x + v + w`, the end of the far segment, and whose far segment is `-w`. -/
theorem reverse_staplePath (v w x y : V) :
    (staplePath v w x y).reverse = staplePath (x + v + w - y) (-w) y x := by
  simp [staplePath_def]

end staplePath

namespace GaugeLink

variable {V G : Type*} [AddCommGroup V] [Module ℝ V] [Group G]

/-- The transverse link of the staple path with leg `v` and far segment `w` starting at `x`: the
link along its far segment, from `x + v` to `x + v + w`. It is the transverse link at light-cone
distance `L` when `v = L • n` and `w` is the transverse separation. -/
def transverseLink (W : GaugeLink V G) (v w x : V) : G := W (x + v) (x + v + w)

theorem transverseLink_def (W : GaugeLink V G) (v w x : V) :
    W.transverseLink v w x = W (x + v) (x + v + w) := (rfl)

/-- The staple link is the product of the outgoing leg, the transverse link, and the returning
leg. -/
theorem pathLink_staplePath (W : GaugeLink V G) (v w x y : V) :
    W.pathLink (staplePath v w x y) = W x (x + v) * W.transverseLink v w x * W (x + v + w) y := by
  simp [staplePath_def, transverseLink_def, mul_assoc]

/-- Under a gauge transformation the transverse link is conjugated by the gauge transformation at
the two ends of the far segment. -/
@[simp]
theorem transverseLink_smul (Ω : V → G) (W : GaugeLink V G) (v w x : V) :
    (Ω • W).transverseLink v w x =
      Ω (x + v) * W.transverseLink v w x * (Ω (x + v + w))⁻¹ := by
  rw [transverseLink_def, transverseLink_def, smul_apply]

/-- **Gauge covariance of the staple link**: under a gauge transformation the staple link is
conjugated by the gauge transformation at its two endpoints. -/
@[simp]
theorem pathLink_staplePath_smul (Ω : V → G) (W : GaugeLink V G) (v w x y : V) :
    (Ω • W).pathLink (staplePath v w x y) = Ω x * W.pathLink (staplePath v w x y) * (Ω y)⁻¹ := by
  rw [staplePath_def, pathLink_smul]
  simp only [List.getLast_cons_cons, List.getLast_singleton]

/-- The link along the reverse of a staple path, the staple from `y` back to `x` with leg
`x + v + w - y` and far segment `-w` (`reverse_staplePath`), is the inverse of the staple link. -/
theorem pathLink_reverse_staplePath (W : GaugeLink V G) (v w x y : V) :
    W.pathLink (staplePath (x + v + w - y) (-w) y x) = (W.pathLink (staplePath v w x y))⁻¹ := by
  rw [← reverse_staplePath, pathLink_reverse]

/-- **A staple with trivial legs carries its link on the far segment**: if the links of both
legs are trivial, the staple link is the transverse link. -/
theorem pathLink_staplePath_eq_transverseLink_of_legs_eq_one (W : GaugeLink V G) {v w x y : V}
    (hx : W x (x + v) = 1) (hy : W (x + v + w) y = 1) :
    W.pathLink (staplePath v w x y) = W.transverseLink v w x := by
  simp [pathLink_staplePath, hx, hy]

/-- A gauge link is in axial gauge for the direction `n` when its links along `n` are trivial,
which for the link of a gauge potential is the condition `n · A = 0`. For a light-like direction
`n` this is light-cone gauge. -/
def IsAxialGauge (W : GaugeLink V G) (n : V) : Prop :=
  ∀ x : V, ∀ t : ℝ, W x (x + t • n) = 1

theorem isAxialGauge_iff {W : GaugeLink V G} {n : V} :
    W.IsAxialGauge n ↔ ∀ (x : V) (t : ℝ), W x (x + t • n) = 1 := Iff.rfl

/-- In axial gauge for `n` the link along any segment parallel to `n` is trivial. -/
theorem IsAxialGauge.apply_eq_one_of_sub_eq_smul {W : GaugeLink V G} {n : V}
    (hW : W.IsAxialGauge n) {x y : V} {t : ℝ} (h : y - x = t • n) : W x y = 1 := by
  rw [sub_eq_iff_eq_add'] at h
  rw [h]
  exact hW x t

/-- **In axial gauge the staple link is the transverse link**: in axial gauge for `n` (light-cone
gauge for light-like `n`), for the staple from `x` to
`x + s • n + w` with legs along `n` to light-cone distance `L`, the two legs contribute nothing,
and the whole gauge link of the staple sits on the transverse segment `w` at light-cone
distance `L`. -/
theorem pathLink_staplePath_eq_transverseLink_of_isAxialGauge {W : GaugeLink V G} {n : V}
    (hW : W.IsAxialGauge n) (L s : ℝ) (x w : V) :
    W.pathLink (staplePath (L • n) w x (x + s • n + w)) = W.transverseLink (L • n) w x :=
  W.pathLink_staplePath_eq_transverseLink_of_legs_eq_one (hW x L)
    (hW.apply_eq_one_of_sub_eq_smul (t := s - L) (by module))

/-! ### The gauge link of a linear abelian gauge potential -/

/-- The phase `½ B (x + y) (x - y)` of the straight link of the linear abelian gauge potential
`A(z) · w = B z w`: minus the integral of `A` along the segment from `x` to `y`. -/
private def bilinPhase (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (x y : V) : ℝ := B (x + y) (x - y) / 2

private theorem bilinPhase_add_of_mem_segment (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) {x y m : V}
    (hm : m ∈ segment ℝ x y) :
    bilinPhase B x m + bilinPhase B m y = bilinPhase B x y := by
  obtain ⟨a, b, -, -, hab, rfl⟩ := hm
  obtain rfl : b = 1 - a := by linarith
  simp only [bilinPhase, map_add, map_sub, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul]
  ring

/-- The gauge link of the linear abelian gauge potential `A(z) · w = B z w`, valued in the circle
group `U(1)` and with the coupling absorbed into `B`: the straight link from `x` to `y` is
`exp(-i ∫ A · dz)` along the segment from `x` to `y`, whose phase is `½ B (x + y) (x - y)`.
Its field strength is `F u w = B u w - B w u`. -/
def ofBilin (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) : GaugeLink V Circle where
  toFun x y := Circle.exp (bilinPhase B x y)
  toFun_swap' x y := by
    rw [← Circle.exp_neg]
    congr 1
    simp only [bilinPhase, map_add, map_sub, LinearMap.add_apply]
    ring
  toFun_mul_toFun' x y m hm := by
    rw [← Circle.exp_add, bilinPhase_add_of_mem_segment B hm]

@[simp]
theorem ofBilin_apply (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (x y : V) :
    ofBilin B x y = Circle.exp (B (x + y) (x - y) / 2) := (rfl)

/-- The gauge link of a linear abelian potential with `B z n = 0` for every `z` is in axial gauge
for `n`. -/
theorem isAxialGauge_ofBilin {B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} {n : V} (hB : ∀ z, B z n = 0) :
    (ofBilin B).IsAxialGauge n := by
  intro x t
  simp [hB]

/-- The staple link of a linear abelian potential is the straight link times `exp(-i Φ)`, where
`Φ = ½ (F v w + F v (y - x) + F w (y - x))` is the flux of the field strength `F = B - B.flip`
through the quadrilateral with corners `x`, `x + v`, `x + v + w`, `y` enclosed by the staple path
and the straight segment. -/
theorem pathLink_staplePath_ofBilin (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (v w x y : V) :
    (ofBilin B).pathLink (staplePath v w x y) =
      ofBilin B x y * Circle.exp
        (-(((B - B.flip) v w + (B - B.flip) v (y - x) + (B - B.flip) w (y - x)) / 2)) := by
  simp only [pathLink_staplePath, transverseLink_def, ofBilin_apply, ← Circle.exp_add]
  congr 1
  simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.flip_apply]
  ring

/-- **The transverse link cannot be omitted.** There is a gauge link in axial gauge for `(1, 0)`
whose staple link and whose transverse link are non-trivial. The legs of the staple are trivial
in that gauge, so the staple link is the transverse link
(`pathLink_staplePath_eq_transverseLink_of_isAxialGauge`): dropping the transverse link from the
staple changes the result. -/
theorem exists_isAxialGauge_pathLink_staplePath_ne_one :
    ∃ W : GaugeLink (ℝ × ℝ) Circle, W.IsAxialGauge (1, 0) ∧
      W.pathLink (staplePath (1, 0) (0, 1) 0 (0, 1)) ≠ 1 ∧
      W.transverseLink (1, 0) (0, 1) 0 ≠ 1 := by
  set B : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) →ₗ[ℝ] ℝ :=
    (LinearMap.mul ℝ ℝ).compl₁₂ (LinearMap.fst ℝ ℝ ℝ) (LinearMap.snd ℝ ℝ ℝ)
  have hB (z w : ℝ × ℝ) : B z w = z.1 * w.2 := by simp [B]
  -- The flux of the field strength through the unit square is `1`, so the staple link is the
  -- trivial straight link times `exp(-1)`, and the transverse link is `exp(-1)` too.
  have hstaple : (ofBilin B).pathLink (staplePath (1, 0) (0, 1) 0 (0, 1)) = Circle.exp (-1 : ℝ) :=
    by rw [pathLink_staplePath_ofBilin, ofBilin_apply, ← Circle.exp_add]; congr 1; simp [hB]
  have htrans : (ofBilin B).transverseLink (1, 0) (0, 1) 0 = Circle.exp (-1 : ℝ) := by
    rw [transverseLink_def, ofBilin_apply]; congr 1; simp [hB]
  have hexp : Circle.exp (-1 : ℝ) ≠ 1 := by
    intro h
    have h1 : Circle.exp (-1) = Circle.exp 0 := by rw [h, Circle.exp_zero]
    have h2 := Circle.exp_injOn_Icc (a := -1) (b := 0) (by linarith [Real.two_le_pi])
      (by norm_num) (by norm_num) h1
    norm_num at h2
  refine ⟨ofBilin B, isAxialGauge_ofBilin fun z => by simp [hB], ?_, ?_⟩
  · rw [hstaple]; exact hexp
  · rw [htrans]; exact hexp

end GaugeLink

end TMD
end Parton
end Particles
end EpsilonEridani
