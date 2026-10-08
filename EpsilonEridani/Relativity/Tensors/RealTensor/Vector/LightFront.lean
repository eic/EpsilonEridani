/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Physlib.Relativity.Tensors.RealTensor.Vector.MinkowskiProduct
public import EpsilonEridani.Mathematics.InnerProductSpace.Orientation

/-!
# Light-front components and transverse boosts

For a four-vector `p` with the `z`-axis as longitudinal direction, the light-front components are

  `p⁺ = (p⁰ + p³) / √2`,  `p⁻ = (p⁰ - p³) / √2`,  `p_T = (p¹, p²)`,

with the transverse part `p_T` a genuine vector of the transverse plane
`EuclideanSpace ℝ (Fin 2)`. In these components the Minkowski product of signature `(+,-,-,-)`
reads `p · q = p⁺ q⁻ + p⁻ q⁺ - p_T · q_T`.

The transverse boost with parameter `v` in the transverse plane is the linear equivalence

  `p⁺ ↦ p⁺`,  `p_T ↦ p_T + p⁺ v`,  `p⁻ ↦ p⁻ + v · p_T + ‖v‖² p⁺ / 2`.

These maps preserve the Minkowski product, and `v ↦` (boost by `v`) turns addition in the
transverse plane into composition: the transverse boosts form a copy of the additive group of the
plane. They act on transverse momenta by a translation proportional to the plus component and do
not change any plus component, so they act like the Galilean boosts of two-dimensional
nonrelativistic mechanics with `p⁺` in the role of the mass. Consequently

* the momentum fraction `k⁺ / P⁺` of a parton in a hadron is boost invariant;
* the transverse momentum of `k` relative to `P`, `k_T - (k⁺ / P⁺) P_T`, is boost invariant, and
  equals the transverse part of `k` in the light-front frame `P_T = 0`, which is reached from any
  `P` with `P⁺ ≠ 0` by exactly one transverse boost;
* points of the light-front hyperplane `x⁺ = 0` keep their transverse position.

Transverse positions on the light front and relative transverse momenta are therefore
frame-independent variables, and so is the oriented area `ω(b_T, k_T)` between them, where `ω` is
the area form of the standard orientation of the plane (`EuclideanSpace.orientation`). The same
area is invariant under orientation-preserving isometries of the transverse plane, acting on
four-vectors through `EpsilonEridani.transverseIsometry`. This is the kinematic fact behind the
use of transverse position and transverse momentum as phase-space variables of parton Wigner
distributions, and behind `ω(b_T, k_T)` as the weight of parton orbital angular momentum.

## Main definitions

* `Lorentz.Vector.plusComponent`, `Lorentz.Vector.minusComponent`,
  `Lorentz.Vector.transversePart`: the light-front components of a four-vector.
* `EpsilonEridani.ofLightFront`: the four-vector with prescribed light-front components.
* `EpsilonEridani.transverseBoost v`: the light-front transverse boost with parameter `v`, as a
  linear equivalence.
* `EpsilonEridani.transverseIsometry R`: an isometry `R` of the transverse plane acting on
  four-vectors, as a linear equivalence.
* `Lorentz.Vector.relativeTransverse k P`: the transverse momentum of `k` relative to `P`.

## Main statements

* `Lorentz.Vector.minkowskiProduct_eq_lightFront`: `p · q = p⁺ q⁻ + p⁻ q⁺ - p_T · q_T`.
* `EpsilonEridani.minkowskiProduct_transverseBoost`: transverse boosts preserve the Minkowski
  product.
* `EpsilonEridani.transverseBoost_zero`, `EpsilonEridani.transverseBoost_add`,
  `EpsilonEridani.transverseBoost_symm`: the boosts form a representation of the additive group
  of the transverse plane.
* `EpsilonEridani.transversePart_transverseBoost_eq_zero_iff`: the unique boost to the frame with
  vanishing transverse momentum.
* `EpsilonEridani.relativeTransverse_transverseBoost`: relative transverse momenta are boost
  invariant.
* `EpsilonEridani.areaForm_relativeTransverse_transverseBoost`: the oriented area between two
  relative transverse momenta is invariant under transverse boosts; in particular
  (`EpsilonEridani.areaForm_transversePart_relativeTransverse_transverseBoost`) so is the area
  between a light-front position and a relative transverse momentum.
* `EpsilonEridani.areaForm_relativeTransverse_transverseIsometry`: the oriented area between a
  transverse position and a relative transverse momentum is invariant under
  orientation-preserving transverse isometries.

## References

* J. B. Kogut and D. E. Soper, *Quantum electrodynamics in the infinite-momentum frame*,
  Phys. Rev. D 1 (1970) 2901.
* S. J. Brodsky, H.-C. Pauli and S. S. Pinsky, *Quantum chromodynamics and other field theories on
  the light cone*, Phys. Rept. 301 (1998) 299, arXiv:hep-ph/9705477.
* M. Burkardt, *Impact parameter dependent parton distributions and off-forward parton
  distributions for ζ → 0*, Phys. Rev. D 62 (2000) 071503, arXiv:hep-ph/0005108.
-/

@[expose] public section

noncomputable section

open EuclideanSpace (orientation)
open scoped EuclideanSpace

namespace Lorentz.Vector

/-- The transverse plane. -/
local notation "E²" => EuclideanSpace ℝ (Fin 2)

/-- The plus light-front component `p⁺ = (p⁰ + p³) / √2` of a four-vector. -/
def plusComponent (p : Vector 3) : ℝ := (p (Sum.inl 0) + p (Sum.inr 2)) / √2

/-- The minus light-front component `p⁻ = (p⁰ - p³) / √2` of a four-vector. -/
def minusComponent (p : Vector 3) : ℝ := (p (Sum.inl 0) - p (Sum.inr 2)) / √2

/-- The transverse part `p_T = (p¹, p²)` of a four-vector, as a vector of the transverse
plane. -/
def transversePart (p : Vector 3) : E² := !₂[p (Sum.inr 0), p (Sum.inr 1)]

lemma plusComponent_def (p : Vector 3) :
    plusComponent p = (p (Sum.inl 0) + p (Sum.inr 2)) / √2 := (rfl)

lemma minusComponent_def (p : Vector 3) :
    minusComponent p = (p (Sum.inl 0) - p (Sum.inr 2)) / √2 := (rfl)

lemma transversePart_def (p : Vector 3) :
    transversePart p = !₂[p (Sum.inr 0), p (Sum.inr 1)] := (rfl)

@[simp]
lemma transversePart_apply_zero (p : Vector 3) : transversePart p 0 = p (Sum.inr 0) := (rfl)

@[simp]
lemma transversePart_apply_one (p : Vector 3) : transversePart p 1 = p (Sum.inr 1) := (rfl)

@[simp]
lemma plusComponent_add (p q : Vector 3) :
    plusComponent (p + q) = plusComponent p + plusComponent q := by
  simp only [plusComponent_def, apply_add]
  ring

@[simp]
lemma plusComponent_smul (c : ℝ) (p : Vector 3) :
    plusComponent (c • p) = c * plusComponent p := by
  simp only [plusComponent_def, apply_smul]
  ring

@[simp]
lemma plusComponent_zero : plusComponent 0 = 0 := by
  simpa using plusComponent_smul 0 0

@[simp]
lemma plusComponent_neg (p : Vector 3) : plusComponent (-p) = -plusComponent p := by
  simpa using plusComponent_smul (-1) p

@[simp]
lemma plusComponent_sub (p q : Vector 3) :
    plusComponent (p - q) = plusComponent p - plusComponent q := by
  simp [sub_eq_add_neg]

@[simp]
lemma minusComponent_add (p q : Vector 3) :
    minusComponent (p + q) = minusComponent p + minusComponent q := by
  simp only [minusComponent_def, apply_add]
  ring

@[simp]
lemma minusComponent_smul (c : ℝ) (p : Vector 3) :
    minusComponent (c • p) = c * minusComponent p := by
  simp only [minusComponent_def, apply_smul]
  ring

@[simp]
lemma minusComponent_zero : minusComponent 0 = 0 := by
  simpa using minusComponent_smul 0 0

@[simp]
lemma minusComponent_neg (p : Vector 3) : minusComponent (-p) = -minusComponent p := by
  simpa using minusComponent_smul (-1) p

@[simp]
lemma minusComponent_sub (p q : Vector 3) :
    minusComponent (p - q) = minusComponent p - minusComponent q := by
  simp [sub_eq_add_neg]

@[simp]
lemma transversePart_add (p q : Vector 3) :
    transversePart (p + q) = transversePart p + transversePart q := by
  ext i
  fin_cases i <;> simp

@[simp]
lemma transversePart_smul (c : ℝ) (p : Vector 3) :
    transversePart (c • p) = c • transversePart p := by
  ext i
  fin_cases i <;> simp

@[simp]
lemma transversePart_zero : transversePart 0 = 0 := by
  simpa using transversePart_smul 0 0

@[simp]
lemma transversePart_neg (p : Vector 3) : transversePart (-p) = -transversePart p := by
  simpa using transversePart_smul (-1) p

@[simp]
lemma transversePart_sub (p q : Vector 3) :
    transversePart (p - q) = transversePart p - transversePart q := by
  simp [sub_eq_add_neg]

end Lorentz.Vector

namespace EpsilonEridani

open Lorentz.Vector

/-- The transverse plane. -/
local notation "E²" => EuclideanSpace ℝ (Fin 2)

/-- The four-vector with plus component `a`, minus component `b` and transverse part `kT`. -/
def ofLightFront (a b : ℝ) (kT : E²) : Lorentz.Vector 3 :=
  Sum.elim (fun _ => (a + b) / √2) ![kT 0, kT 1, (a - b) / √2]

lemma ofLightFront_def (a b : ℝ) (kT : E²) :
    ofLightFront a b kT = Sum.elim (fun _ => (a + b) / √2) ![kT 0, kT 1, (a - b) / √2] := (rfl)

@[simp]
lemma ofLightFront_inl (a b : ℝ) (kT : E²) (i : Fin 1) :
    ofLightFront a b kT (Sum.inl i) = (a + b) / √2 := (rfl)

@[simp]
lemma ofLightFront_inr_zero (a b : ℝ) (kT : E²) : ofLightFront a b kT (Sum.inr 0) = kT 0 := (rfl)

@[simp]
lemma ofLightFront_inr_one (a b : ℝ) (kT : E²) : ofLightFront a b kT (Sum.inr 1) = kT 1 := (rfl)

@[simp]
lemma ofLightFront_inr_two (a b : ℝ) (kT : E²) :
    ofLightFront a b kT (Sum.inr 2) = (a - b) / √2 := (rfl)

/-! ### Light-front components as coordinates -/

private lemma sqrt_two_mul_self_eq_two : √2 * √2 = 2 :=
  Real.mul_self_sqrt zero_le_two

@[simp]
lemma plusComponent_ofLightFront (a b : ℝ) (kT : E²) : plusComponent (ofLightFront a b kT) = a := by
  simp only [plusComponent_def, ofLightFront_inl, ofLightFront_inr_two]
  field_simp
  linear_combination (-a) * sqrt_two_mul_self_eq_two

@[simp]
lemma minusComponent_ofLightFront (a b : ℝ) (kT : E²) :
    minusComponent (ofLightFront a b kT) = b := by
  simp only [minusComponent_def, ofLightFront_inl, ofLightFront_inr_two]
  field_simp
  linear_combination (-b) * sqrt_two_mul_self_eq_two

@[simp]
lemma transversePart_ofLightFront (a b : ℝ) (kT : E²) :
    transversePart (ofLightFront a b kT) = kT := by
  ext i
  fin_cases i <;> simp

end EpsilonEridani

namespace Lorentz.Vector

open EpsilonEridani

/-- The transverse plane. -/
local notation "E²" => EuclideanSpace ℝ (Fin 2)

@[simp]
lemma ofLightFront_plusComponent_minusComponent_transversePart (p : Vector 3) :
    ofLightFront (plusComponent p) (minusComponent p) (transversePart p) = p := by
  ext μ
  rcases μ with i | i
  · rw [Subsingleton.elim i 0, ofLightFront_inl, plusComponent_def, minusComponent_def]
    field_simp
    linear_combination (-p (Sum.inl 0)) * sqrt_two_mul_self_eq_two
  · fin_cases i
    · simp
    · simp
    · simp only [Fin.reduceFinMk, ofLightFront_inr_two, plusComponent_def, minusComponent_def]
      field_simp
      linear_combination (-p (Sum.inr 2)) * sqrt_two_mul_self_eq_two

/-- A four-vector is determined by its light-front components. -/
lemma ext_lightFront {p q : Vector 3} (hplus : plusComponent p = plusComponent q)
    (hminus : minusComponent p = minusComponent q) (hT : transversePart p = transversePart q) :
    p = q := by
  rw [← ofLightFront_plusComponent_minusComponent_transversePart p,
    ← ofLightFront_plusComponent_minusComponent_transversePart q, hplus, hminus, hT]

lemma ext_lightFront_iff {p q : Vector 3} :
    p = q ↔ plusComponent p = plusComponent q ∧ minusComponent p = minusComponent q ∧
      transversePart p = transversePart q := by
  refine ⟨fun h => by simp [h], fun ⟨h₁, h₂, h₃⟩ => ext_lightFront h₁ h₂ h₃⟩

/-- The Minkowski product in light-front components: `p · q = p⁺ q⁻ + p⁻ q⁺ - p_T · q_T`. -/
lemma minkowskiProduct_eq_lightFront (p q : Vector 3) :
    ⟪p, q⟫ₘ = plusComponent p * minusComponent q + minusComponent p * plusComponent q -
      inner ℝ (transversePart p) (transversePart q) := by
  rw [minkowskiProduct_toCoord, plusComponent_def, plusComponent_def, minusComponent_def,
    minusComponent_def, EuclideanSpace.inner_eq_star_dotProduct]
  simp only [Fin.sum_univ_three, dotProduct, Fin.sum_univ_two, star_trivial]
  field_simp
  simp only [transversePart_apply_zero, transversePart_apply_one]
  linear_combination
    (p (Sum.inl 0) * q (Sum.inl 0) - p (Sum.inr 2) * q (Sum.inr 2)) * sqrt_two_mul_self_eq_two

/-- The Minkowski square in light-front components: `p · p = 2 p⁺ p⁻ - ‖p_T‖²`. -/
lemma minkowskiProduct_self_eq_lightFront (p : Vector 3) :
    ⟪p, p⟫ₘ = 2 * plusComponent p * minusComponent p - ‖transversePart p‖ ^ 2 := by
  rw [minkowskiProduct_eq_lightFront, real_inner_self_eq_norm_sq]
  ring

/-! ### Relative transverse momentum -/

/-- The transverse momentum of `k` relative to `P`, `k_T - (k⁺ / P⁺) P_T`: the transverse part
of `k` in the light-front frame reached by the boost with parameter `-P_T / P⁺`. Requires
`P⁺ ≠ 0` for the frame interpretation; the definition covers `P⁺ = 0` only through the division
convention. -/
def relativeTransverse (k P : Vector 3) : E² :=
  transversePart k - (plusComponent k / plusComponent P) • transversePart P

lemma relativeTransverse_def (k P : Vector 3) :
    relativeTransverse k P =
      transversePart k - (plusComponent k / plusComponent P) • transversePart P := (rfl)

lemma relativeTransverse_of_transversePart_eq_zero (k : Vector 3) {P : Vector 3}
    (hP : transversePart P = 0) : relativeTransverse k P = transversePart k := by
  simp [relativeTransverse_def, hP]

/-- Relative to any `P`, the transverse momentum of a point of the light-front hyperplane
`x⁺ = 0` is its transverse part. -/
lemma relativeTransverse_of_plusComponent_eq_zero {b : Vector 3} (hb : plusComponent b = 0)
    (P : Vector 3) : relativeTransverse b P = transversePart b := by
  simp [relativeTransverse_def, hb]

@[simp]
lemma relativeTransverse_self {P : Vector 3} (hP : plusComponent P ≠ 0) :
    relativeTransverse P P = 0 := by
  simp [relativeTransverse_def, div_self hP]

end Lorentz.Vector

namespace EpsilonEridani

open Lorentz.Vector

/-- The transverse plane. -/
local notation "E²" => EuclideanSpace ℝ (Fin 2)

/-! ### Transverse boosts -/

/-- The light-front transverse boost with parameter `v`: it fixes `p⁺`, shifts the transverse
part by `p⁺ v`, and shifts `p⁻` by `v · p_T + ‖v‖² p⁺ / 2`. Its inverse is the boost with
parameter `-v` (`transverseBoost_symm`). -/
def transverseBoost (v : E²) : Lorentz.Vector 3 ≃ₗ[ℝ] Lorentz.Vector 3 where
  toFun p := ofLightFront (plusComponent p)
    (minusComponent p + inner ℝ v (transversePart p) + ‖v‖ ^ 2 / 2 * plusComponent p)
    (transversePart p + plusComponent p • v)
  map_add' p q := by
    apply ext_lightFront
    · simp
    · simp only [minusComponent_add, minusComponent_ofLightFront, plusComponent_add,
        transversePart_add, inner_add_right]
      ring
    · simp only [transversePart_add, transversePart_ofLightFront, plusComponent_add, add_smul]
      abel
  map_smul' c p := by
    apply ext_lightFront
    · simp
    · simp only [minusComponent_smul, minusComponent_ofLightFront, plusComponent_smul,
        transversePart_smul, inner_smul_right, RingHom.id_apply]
      ring
    · simp [_root_.smul_add, _root_.smul_smul]
  invFun p := ofLightFront (plusComponent p)
    (minusComponent p - inner ℝ v (transversePart p) + ‖v‖ ^ 2 / 2 * plusComponent p)
    (transversePart p - plusComponent p • v)
  left_inv p := by
    apply ext_lightFront
    · simp
    · simp only [minusComponent_ofLightFront, plusComponent_ofLightFront,
        transversePart_ofLightFront, inner_add_right, inner_smul_right,
        real_inner_self_eq_norm_sq]
      ring
    · simp
  right_inv p := by
    apply ext_lightFront
    · simp
    · simp only [minusComponent_ofLightFront, plusComponent_ofLightFront,
        transversePart_ofLightFront, inner_sub_right, inner_smul_right,
        real_inner_self_eq_norm_sq]
      ring
    · simp

@[simp]
lemma plusComponent_transverseBoost (v : E²) (p : Lorentz.Vector 3) :
    plusComponent (transverseBoost v p) = plusComponent p := by
  simp [transverseBoost]

@[simp]
lemma minusComponent_transverseBoost (v : E²) (p : Lorentz.Vector 3) :
    minusComponent (transverseBoost v p) =
      minusComponent p + inner ℝ v (transversePart p) + ‖v‖ ^ 2 / 2 * plusComponent p := by
  simp [transverseBoost]

@[simp]
lemma transversePart_transverseBoost (v : E²) (p : Lorentz.Vector 3) :
    transversePart (transverseBoost v p) = transversePart p + plusComponent p • v := by
  simp [transverseBoost]

/-- Transverse boosts preserve the Minkowski product. -/
@[simp]
lemma minkowskiProduct_transverseBoost (v : E²) (p q : Lorentz.Vector 3) :
    ⟪transverseBoost v p, transverseBoost v q⟫ₘ = ⟪p, q⟫ₘ := by
  simp only [minkowskiProduct_eq_lightFront, plusComponent_transverseBoost,
    minusComponent_transverseBoost, transversePart_transverseBoost, inner_add_left,
    inner_add_right, inner_smul_left, inner_smul_right, real_inner_self_eq_norm_sq,
    real_inner_comm v, RCLike.conj_to_real]
  ring

@[simp]
lemma transverseBoost_zero : transverseBoost 0 = LinearEquiv.refl ℝ (Lorentz.Vector 3) := by
  ext1 p
  apply ext_lightFront <;> simp

/-- Composition of transverse boosts adds their parameters. -/
lemma transverseBoost_add (u v : E²) :
    transverseBoost (u + v) = (transverseBoost v).trans (transverseBoost u) := by
  ext1 p
  apply ext_lightFront
  · simp
  · simp only [minusComponent_transverseBoost, LinearEquiv.trans_apply,
      transversePart_transverseBoost, plusComponent_transverseBoost, inner_add_left,
      inner_add_right, inner_smul_right, norm_add_sq_real]
    ring
  · simp only [transversePart_transverseBoost, LinearEquiv.trans_apply,
      plusComponent_transverseBoost, _root_.smul_add]
    abel

/-- The inverse of the transverse boost with parameter `v` is the boost with parameter `-v`. -/
@[simp]
lemma transverseBoost_symm (v : E²) : (transverseBoost v).symm = transverseBoost (-v) := by
  ext1 p
  rw [LinearEquiv.symm_apply_eq, ← LinearEquiv.trans_apply, ← transverseBoost_add,
    add_neg_cancel, transverseBoost_zero, LinearEquiv.refl_apply]

lemma transverseBoost_sub (u v : EuclideanSpace ℝ (Fin 2)) :
    transverseBoost (u - v) =
      (transverseBoost v).symm.trans (transverseBoost u) := by
  rw [transverseBoost_symm, sub_eq_add_neg, transverseBoost_add]

/-- For `P⁺ ≠ 0`, exactly one transverse boost removes the transverse part of `P`: the one with
parameter `-P_T / P⁺`. -/
lemma transversePart_transverseBoost_eq_zero_iff (v : EuclideanSpace ℝ (Fin 2))
    {P : Lorentz.Vector 3} (hP : plusComponent P ≠ 0) :
    transversePart (transverseBoost v P) = 0 ↔
      v = -((plusComponent P)⁻¹ • transversePart P) := by
  rw [transversePart_transverseBoost, ← _root_.smul_neg, eq_inv_smul_iff₀ hP,
    eq_neg_iff_add_eq_zero, add_comm]
/-- Relative transverse momenta are invariant under transverse boosts. -/
@[simp]
lemma relativeTransverse_transverseBoost (v : E²) (k : Lorentz.Vector 3) {P : Lorentz.Vector 3}
    (hP : plusComponent P ≠ 0) :
    relativeTransverse (transverseBoost v k) (transverseBoost v P) = relativeTransverse k P := by
  simp only [relativeTransverse_def, transversePart_transverseBoost,
    plusComponent_transverseBoost, _root_.smul_add, _root_.smul_smul, div_mul_cancel₀ _ hP]
  abel

/-- The oriented area between the transverse position of a point of the light-front hyperplane
`x⁺ = 0` and a relative transverse momentum is invariant under transverse boosts. -/
lemma areaForm_transversePart_relativeTransverse_transverseBoost (v : EuclideanSpace ℝ (Fin 2))
    {b : Lorentz.Vector 3} (hb : plusComponent b = 0) (k : Lorentz.Vector 3) {P : Lorentz.Vector 3}
    (hP : plusComponent P ≠ 0) :
    (orientation (Fin 2)).areaForm (transversePart (transverseBoost v b))
        (relativeTransverse (transverseBoost v k) (transverseBoost v P)) =
      (orientation (Fin 2)).areaForm (transversePart b) (relativeTransverse k P) := by
  have hb' : plusComponent (transverseBoost v b) = 0 := by rwa [plusComponent_transverseBoost]
  simp [transversePart_transverseBoost v b, hb, add_zero,
    relativeTransverse_transverseBoost v k hP]

/-! ### Isometries of the transverse plane -/

/-- An isometry `R` of the transverse plane acting on four-vectors: it fixes `p⁺` and `p⁻` and
maps the transverse part by `R`. For `R` a rotation this is a rotation about the longitudinal
axis. -/
def transverseIsometry (R : E² ≃ₗᵢ[ℝ] E²) : Lorentz.Vector 3 ≃ₗ[ℝ] Lorentz.Vector 3 where
  toFun p := ofLightFront (plusComponent p) (minusComponent p) (R (transversePart p))
  map_add' p q := by apply ext_lightFront <;> simp
  map_smul' c p := by apply ext_lightFront <;> simp
  invFun p := ofLightFront (plusComponent p) (minusComponent p) (R.symm (transversePart p))
  left_inv p := by apply ext_lightFront <;> simp
  right_inv p := by apply ext_lightFront <;> simp

@[simp]
lemma plusComponent_transverseIsometry (R : E² ≃ₗᵢ[ℝ] E²) (p : Lorentz.Vector 3) :
    plusComponent (transverseIsometry R p) = plusComponent p := by
  simp [transverseIsometry]

@[simp]
lemma minusComponent_transverseIsometry (R : E² ≃ₗᵢ[ℝ] E²) (p : Lorentz.Vector 3) :
    minusComponent (transverseIsometry R p) = minusComponent p := by
  simp [transverseIsometry]

@[simp]
lemma transversePart_transverseIsometry (R : E² ≃ₗᵢ[ℝ] E²) (p : Lorentz.Vector 3) :
    transversePart (transverseIsometry R p) = R (transversePart p) := by
  simp [transverseIsometry]

@[simp]
lemma transverseIsometry_symm (R : E² ≃ₗᵢ[ℝ] E²) :
    (transverseIsometry R).symm = transverseIsometry R.symm := by
  ext1 p
  rw [LinearEquiv.symm_apply_eq]
  apply ext_lightFront <;> simp

/-- Isometries of the transverse plane preserve the Minkowski product. -/
@[simp]
lemma minkowskiProduct_transverseIsometry (R : E² ≃ₗᵢ[ℝ] E²) (p q : Lorentz.Vector 3) :
    ⟪transverseIsometry R p, transverseIsometry R q⟫ₘ = ⟪p, q⟫ₘ := by
  simp [minkowskiProduct_eq_lightFront]

/-- Conjugating a transverse boost by a transverse isometry `R` maps its parameter by `R`. -/
lemma transverseBoost_trans_transverseIsometry (R : E² ≃ₗᵢ[ℝ] E²) (v : E²) :
    (transverseBoost v).trans (transverseIsometry R) =
      (transverseIsometry R).trans (transverseBoost (R v)) := by
  ext1 p
  apply ext_lightFront <;> simp

@[simp]
lemma relativeTransverse_transverseIsometry (R : E² ≃ₗᵢ[ℝ] E²) (k P : Lorentz.Vector 3) :
    relativeTransverse (transverseIsometry R k) (transverseIsometry R P) =
      R (relativeTransverse k P) := by
  simp [relativeTransverse_def]

/-- The oriented area between transverse position and relative transverse momentum is invariant
under orientation-preserving isometries of the transverse plane. -/
lemma areaForm_relativeTransverse_transverseIsometry (R : E² ≃ₗᵢ[ℝ] E²)
    (hR : 0 < LinearMap.det (R.toLinearEquiv : E² →ₗ[ℝ] E²)) (b k P : Lorentz.Vector 3) :
    (orientation (Fin 2)).areaForm (transversePart (transverseIsometry R b))
        (relativeTransverse (transverseIsometry R k) (transverseIsometry R P)) =
      (orientation (Fin 2)).areaForm (transversePart b) (relativeTransverse k P) := by
  rw [transversePart_transverseIsometry, relativeTransverse_transverseIsometry,
    Orientation.areaForm_comp_linearIsometryEquiv _ R hR]

/-- The oriented area between two relative transverse momenta is invariant under
orientation-preserving isometries of the transverse plane. -/
lemma areaForm_relativeTransverse_transverseIsometry' (R : E² ≃ₗᵢ[ℝ] E²)
    (hR : 0 < LinearMap.det (R.toLinearEquiv : E² →ₗ[ℝ] E²)) (b k P : Lorentz.Vector 3) :
    (orientation (Fin 2)).areaForm
      (relativeTransverse (transverseIsometry R b) (transverseIsometry R P))
      (relativeTransverse (transverseIsometry R k) (transverseIsometry R P)) =
      (orientation (Fin 2)).areaForm (relativeTransverse b P) (relativeTransverse k P) := by
  rw [relativeTransverse_transverseIsometry, relativeTransverse_transverseIsometry,
    Orientation.areaForm_comp_linearIsometryEquiv _ R hR]

end EpsilonEridani

namespace Lorentz.Vector

open EpsilonEridani

/-- The transverse plane. -/
local notation "E²" => EuclideanSpace ℝ (Fin 2)

/-- In the light-front frame of `P`, reached by the boost with parameter `-P_T / P⁺`, the
transverse part of `k` is its transverse momentum relative to `P`. This holds as a
consequence of the definition for all `P`; the "frame reached by the boost with parameter
`-P_T / P⁺`" interpretation requires `P⁺ ≠ 0`. -/
lemma transversePart_transverseBoost_eq_relativeTransverse (k P : Vector 3) :
    transversePart (transverseBoost (-((plusComponent P)⁻¹ • transversePart P)) k) =
      relativeTransverse k P := by
  rw [transversePart_transverseBoost, relativeTransverse_def, _root_.smul_neg, _root_.smul_smul,
    div_eq_mul_inv, sub_eq_add_neg]

end Lorentz.Vector
