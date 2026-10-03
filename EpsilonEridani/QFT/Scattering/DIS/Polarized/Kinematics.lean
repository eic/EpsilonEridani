/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.QFT.Scattering.DIS.Kinematics.TargetMass
public import EpsilonEridani.QFT.Scattering.DIS.Tensors.Basic

/-!
# Polarised DIS kinematics

A polarised inclusive scattering event is described by the unpolarised kinematics `p`, `k`, `q`
of `DisKinematics` together with the covariant spin four-vector `S` of the target, normalised by

  `S·p = 0`,  `S·S = -1`

against the metric `g`. `PolarizedKinematics g` is that record. The spin vector is data, not a
typeclass, so a longitudinally and a transversely polarised target are two terms of the same
type and can appear in a single statement; reversing the target spin (`PolarizedKinematics.reverse`)
is what a measured cross-section difference compares.

For a massless lepton (`k·k = 0`) and a massive target (`M² := p·p > 0`) the two standard spin
configurations are built from the kinematics:

* the **longitudinal** spin vector `S_L := (M / (p·k)) k - p / M` (`longitudinalSpin`), which in
  the target rest frame is the unit vector along the lepton beam;
* the **transverse** spin vector `S_T(n)` (`transverseSpin`), the normalised component of a
  reference direction `n` orthogonal to both `p` and `k` (`transverseComponent`). The reference
  direction fixes the azimuth of the target spin, which is a choice of the experiment and not
  determined by `p` and `k`.

Each satisfies both normalisation conditions (`PolarizedKinematics.longitudinal`,
`PolarizedKinematics.transverse`), the transverse one is orthogonal to the lepton beam while
the longitudinal one is not (`apply_transverseSpin_k_eq_zero`, `apply_longitudinalSpin_k`), and
the two are mutually orthogonal (`apply_longitudinalSpin_transverseSpin_eq_zero`).

## References

* M. Anselmino, A. Efremov and E. Leader, *The theory and phenomenology of polarized deep
  inelastic scattering*, Phys. Rept. **261** (1995) 1; arXiv:hep-ph/9501369, §2.
* A. V. Manohar, *An introduction to spin dependent deep inelastic scattering*,
  arXiv:hep-ph/9204208, §2.
-/

@[expose] public section

noncomputable section

namespace EpsilonEridani
namespace QFT
namespace Scattering
namespace DIS
namespace Polarized

open EpsilonEridani.QFT.Scattering.DIS.Kinematics (Bilin DisKinematics)

variable {V : Type} [AddCommGroup V] [Module ℝ V]

/-- Polarised inclusive DIS kinematics: the unpolarised process data of `DisKinematics`
together with the covariant spin four-vector `S` of the target, orthogonal to the hadron
momentum and normalised to `S·S = -1` against the metric `g`. -/
@[ext]
structure PolarizedKinematics (g : Bilin V) extends DisKinematics V where
  /-- The covariant spin four-vector of the target. -/
  S : V
  /-- The spin vector is orthogonal to the hadron momentum, `S·p = 0`. -/
  spin_orthogonal : g S p = 0
  /-- The spin vector is spacelike and normalised, `S·S = -1`. -/
  spin_normalized : g S S = -1

namespace PolarizedKinematics

variable {g : Bilin V}

/-- The same event with the target spin reversed, `S ↦ -S`. -/
def reverse (K : PolarizedKinematics g) : PolarizedKinematics g where
  toDisKinematics := K.toDisKinematics
  S := -K.S
  spin_orthogonal := by simp [K.spin_orthogonal]
  spin_normalized := by simp [K.spin_normalized]

@[simp]
lemma reverse_toDisKinematics (K : PolarizedKinematics g) :
    K.reverse.toDisKinematics = K.toDisKinematics := (rfl)

@[simp]
lemma reverse_S (K : PolarizedKinematics g) : K.reverse.S = -K.S := (rfl)

@[simp]
lemma reverse_reverse (K : PolarizedKinematics g) : K.reverse.reverse = K := by
  ext <;> simp

/-- The spin vector of a polarised target is non-zero. -/
lemma S_ne_zero (K : PolarizedKinematics g) : K.S ≠ 0 := by
  intro h
  have := K.spin_normalized
  simp [h] at this

/-- Reversing the spin of a target never leaves the configuration unchanged. -/
lemma reverse_ne (K : PolarizedKinematics g) : K.reverse ≠ K := by
  intro h
  have := congrArg (fun K' : PolarizedKinematics g => g K'.S K.S) h
  norm_num [K.spin_normalized] at this

end PolarizedKinematics

/-! ### The longitudinal spin vector -/

/-- The longitudinal spin vector `S_L := (M / (p·k)) k - p / M` with `M := √(p·p)`. For a
massless lepton, in the target rest frame it is the unit vector along the lepton beam. -/
def longitudinalSpin (g : Bilin V) (K : DisKinematics V) : V :=
  (Real.sqrt (K.M2 g) / g K.p K.k) • K.k - (Real.sqrt (K.M2 g))⁻¹ • K.p

lemma longitudinalSpin_def (g : Bilin V) (K : DisKinematics V) :
    longitudinalSpin g K
      = (Real.sqrt (K.M2 g) / g K.p K.k) • K.k - (Real.sqrt (K.M2 g))⁻¹ • K.p := (rfl)

section Longitudinal

variable {g : Bilin V} {K : DisKinematics V}

/-- The longitudinal spin vector is orthogonal to the hadron momentum. -/
theorem apply_longitudinalSpin_p_eq_zero (hSymm : g.IsSymm) (hpk : g K.p K.k ≠ 0)
    (hM : 0 < K.M2 g) : g (longitudinalSpin g K) K.p = 0 := by
  have hMs : Real.sqrt (K.M2 g) ^ 2 = g K.p K.p := by rw [Real.sq_sqrt hM.le, K.M2_def]
  have hM0 : Real.sqrt (K.M2 g) ≠ 0 := (Real.sqrt_pos.mpr hM).ne'
  simp only [longitudinalSpin, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
    smul_eq_mul, hSymm.eq K.k K.p, ← hMs]
  field_simp
  ring

/-- The longitudinal spin vector of a massless lepton is normalised, `S_L·S_L = -1`. -/
theorem apply_longitudinalSpin_self_eq_neg_one (hSymm : g.IsSymm) (hk : g K.k K.k = 0)
    (hpk : g K.p K.k ≠ 0) (hM : 0 < K.M2 g) :
    g (longitudinalSpin g K) (longitudinalSpin g K) = -1 := by
  have hMs : Real.sqrt (K.M2 g) ^ 2 = g K.p K.p := by rw [Real.sq_sqrt hM.le, K.M2_def]
  have hM0 : Real.sqrt (K.M2 g) ≠ 0 := (Real.sqrt_pos.mpr hM).ne'
  simp only [longitudinalSpin, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
    smul_eq_mul, hSymm.eq K.k K.p, hk, ← hMs]
  field_simp
  ring

/-- The longitudinal spin vector is not orthogonal to the lepton beam:
`S_L·k = -(p·k) / M`. -/
theorem apply_longitudinalSpin_k (hk : g K.k K.k = 0) :
    g (longitudinalSpin g K) K.k = -(g K.p K.k / Real.sqrt (K.M2 g)) := by
  simp only [longitudinalSpin, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
    smul_eq_mul, hk]
  ring

end Longitudinal

/-! ### The transverse spin vectors -/

/-- The component of a reference direction `n` orthogonal to both the hadron momentum `p` and
a massless lepton momentum `k`:
`n_⊥ := n - ((k·n) / (p·k)) p - (((p·n)(p·k) - M² (k·n)) / (p·k)²) k`. -/
def transverseComponent (g : Bilin V) (K : DisKinematics V) (n : V) : V :=
  n - (g K.k n / g K.p K.k) • K.p
    - ((g K.p n * g K.p K.k - K.M2 g * g K.k n) / g K.p K.k ^ 2) • K.k

lemma transverseComponent_def (g : Bilin V) (K : DisKinematics V) (n : V) :
    transverseComponent g K n = n - (g K.k n / g K.p K.k) • K.p
      - ((g K.p n * g K.p K.k - K.M2 g * g K.k n) / g K.p K.k ^ 2) • K.k := (rfl)

/-- The transverse spin vector with reference direction `n`: the component `n_⊥` of `n`
orthogonal to `p` and `k`, normalised to `S_T·S_T = -1`. -/
def transverseSpin (g : Bilin V) (K : DisKinematics V) (n : V) : V :=
  (Real.sqrt (-g (transverseComponent g K n) (transverseComponent g K n)))⁻¹ •
    transverseComponent g K n

lemma transverseSpin_def (g : Bilin V) (K : DisKinematics V) (n : V) :
    transverseSpin g K n
      = (Real.sqrt (-g (transverseComponent g K n) (transverseComponent g K n)))⁻¹ •
        transverseComponent g K n := (rfl)

section Transverse

variable {g : Bilin V} {K : DisKinematics V}

/-- The transverse component is orthogonal to the hadron momentum. -/
theorem apply_p_transverseComponent_eq_zero (hpk : g K.p K.k ≠ 0) (n : V) :
    g K.p (transverseComponent g K n) = 0 := by
  simp only [transverseComponent, DisKinematics.M2_def, map_sub, map_smul, smul_eq_mul]
  field_simp
  ring

/-- The transverse component is orthogonal to a massless lepton momentum. -/
theorem apply_k_transverseComponent_eq_zero (hSymm : g.IsSymm) (hk : g K.k K.k = 0)
    (hpk : g K.p K.k ≠ 0) (n : V) : g K.k (transverseComponent g K n) = 0 := by
  simp only [transverseComponent, map_sub, map_smul, smul_eq_mul, hSymm.eq K.k K.p, hk]
  field_simp
  ring

/-- The transverse spin vector is orthogonal to the hadron momentum. -/
theorem apply_transverseSpin_p_eq_zero (hSymm : g.IsSymm) (hpk : g K.p K.k ≠ 0) (n : V) :
    g (transverseSpin g K n) K.p = 0 := by
  rw [hSymm.eq, transverseSpin, map_smul, apply_p_transverseComponent_eq_zero hpk, smul_zero]

/-- The transverse spin vector is orthogonal to a massless lepton momentum: it is transverse
to the beam. -/
theorem apply_transverseSpin_k_eq_zero (hSymm : g.IsSymm) (hk : g K.k K.k = 0)
    (hpk : g K.p K.k ≠ 0) (n : V) : g (transverseSpin g K n) K.k = 0 := by
  rw [hSymm.eq, transverseSpin, map_smul, apply_k_transverseComponent_eq_zero hSymm hk hpk,
    smul_zero]

/-- The transverse spin vector is normalised, `S_T·S_T = -1`, whenever the transverse
component of the reference direction is spacelike. -/
theorem apply_transverseSpin_self_eq_neg_one (n : V)
    (hn : g (transverseComponent g K n) (transverseComponent g K n) < 0) :
    g (transverseSpin g K n) (transverseSpin g K n) = -1 := by
  rw [transverseSpin]
  set u := transverseComponent g K n
  have hs : Real.sqrt (-g u u) ^ 2 = -g u u := Real.sq_sqrt (neg_nonneg.mpr hn.le)
  have hs0 : Real.sqrt (-g u u) ≠ 0 := (Real.sqrt_pos.mpr (neg_pos.mpr hn)).ne'
  set s := Real.sqrt (-g u u)
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [show g u u = -s ^ 2 by linarith]
  field_simp

/-- **The longitudinal and transverse spin vectors are orthogonal.** -/
theorem apply_longitudinalSpin_transverseSpin_eq_zero (hSymm : g.IsSymm) (hk : g K.k K.k = 0)
    (hpk : g K.p K.k ≠ 0) (n : V) : g (longitudinalSpin g K) (transverseSpin g K n) = 0 := by
  rw [hSymm.eq]
  simp only [longitudinalSpin, map_sub, map_smul, smul_eq_mul,
    apply_transverseSpin_k_eq_zero hSymm hk hpk, apply_transverseSpin_p_eq_zero hSymm hpk]
  ring

end Transverse

/-! ### The two spin configurations -/

namespace PolarizedKinematics

variable {g : Bilin V}

/-- The longitudinally polarised configuration: the kinematics `K` of a massless lepton on a
massive target, with the longitudinal spin vector `longitudinalSpin g K`. -/
def longitudinal (K : DisKinematics V) (hSymm : g.IsSymm) (hk : g K.k K.k = 0)
    (hpk : g K.p K.k ≠ 0) (hM : 0 < K.M2 g) : PolarizedKinematics g where
  toDisKinematics := K
  S := longitudinalSpin g K
  spin_orthogonal := apply_longitudinalSpin_p_eq_zero hSymm hpk hM
  spin_normalized := apply_longitudinalSpin_self_eq_neg_one hSymm hk hpk hM

/-- The transversely polarised configuration with reference direction `n`: the kinematics `K`
with the transverse spin vector `transverseSpin g K n`. For a massless lepton (`k·k = 0`) this
spin vector is transverse to the beam (`apply_transverseSpin_k_eq_zero`). -/
def transverse (K : DisKinematics V) (n : V) (hSymm : g.IsSymm) (hpk : g K.p K.k ≠ 0)
    (hn : g (transverseComponent g K n) (transverseComponent g K n) < 0) :
    PolarizedKinematics g where
  toDisKinematics := K
  S := transverseSpin g K n
  spin_orthogonal := apply_transverseSpin_p_eq_zero hSymm hpk n
  spin_normalized := apply_transverseSpin_self_eq_neg_one n hn

variable {K : DisKinematics V} {n : V} {hSymm : g.IsSymm} {hk : g K.k K.k = 0}
  {hpk : g K.p K.k ≠ 0} {hM : 0 < K.M2 g}
  {hn : g (transverseComponent g K n) (transverseComponent g K n) < 0}

@[simp]
lemma longitudinal_toDisKinematics :
    (longitudinal K hSymm hk hpk hM).toDisKinematics = K := (rfl)

@[simp]
lemma longitudinal_S : (longitudinal K hSymm hk hpk hM).S = longitudinalSpin g K := (rfl)

@[simp]
lemma transverse_toDisKinematics : (transverse K n hSymm hpk hn).toDisKinematics = K := (rfl)

@[simp]
lemma transverse_S : (transverse K n hSymm hpk hn).S = transverseSpin g K n := (rfl)

end PolarizedKinematics

/-! ### A witness in three-dimensional Minkowski space -/

namespace Witness

open Tensors.Hadronic.Witness (gWit gWit_apply gWit_isSymm)

/-- Witness kinematics in `ℝ¹'²` with the metric `gWit`: a target of unit mass at rest,
`p = (1, 0, 0)`, struck by a massless lepton moving along the first spatial axis,
`k = (1, 1, 0)`, which scatters to the massless `k' = (1/4, 0, 1/4)`. The momentum transfer
`q = (3/4, 1, -1/4)` gives `Q² = 1/2`, `p·q = 3/4` and `x = 1/3`. -/
def kPol : DisKinematics (ℝ × ℝ × ℝ) where
  p := (1, 0, 0)
  pPrime := 0
  k := (1, 1, 0)
  kPrime := (1 / 4, 0, 1 / 4)
  q := (3 / 4, 1, -1 / 4)
  hq := by ext <;> norm_num

lemma kPol_k_self : gWit kPol.k kPol.k = 0 := by simp [kPol]

lemma kPol_p_k : gWit kPol.p kPol.k = 1 := by simp [kPol]

lemma kPol_M2 : kPol.M2 gWit = 1 := by simp [DisKinematics.M2_def, kPol]

/-- The witness is a genuine DIS event: it lies in the physical region of
`BasicAssumptions`. -/
lemma basicAssumptions_kPol : DisKinematics.BasicAssumptions gWit kPol where
  q2_pos := by norm_num [DisKinematics.Q2, kPol]
  p_dot_q_pos := by norm_num [kPol]
  p_dot_k_pos := by norm_num [kPol]
  q2_le_two_p_dot_q := by norm_num [DisKinematics.Q2, kPol]
  p_dot_q_le_p_dot_k := by norm_num [kPol]

/-- The witness target mass factor is `γ² = 4 · 1 · (1/3)² / (1/2) = 8/9`. -/
lemma kPol_gammaSq : kPol.gammaSq gWit = 8 / 9 := by
  rw [DisKinematics.gammaSq_def, kPol_M2]
  norm_num [DisKinematics.xBj, DisKinematics.Q2, kPol]

/-- In the rest frame the longitudinal spin vector is the unit vector along the beam. -/
lemma longitudinalSpin_kPol : longitudinalSpin gWit kPol = (0, 1, 0) := by
  rw [longitudinalSpin_def, kPol_M2, kPol_p_k]
  simp [kPol]

/-- The direction `(0, 0, 1)` is already orthogonal to `p` and `k`, so it is its own
transverse component. -/
lemma transverseComponent_kPol : transverseComponent gWit kPol (0, 0, 1) = (0, 0, 1) := by
  rw [transverseComponent_def, kPol_M2, kPol_p_k]
  simp [kPol]

/-- The transverse spin vector with reference direction `(0, 0, 1)` is that direction. -/
lemma transverseSpin_kPol : transverseSpin gWit kPol (0, 0, 1) = (0, 0, 1) := by
  simp [transverseSpin_def, transverseComponent_kPol]

/-- The longitudinally polarised witness configuration. -/
def longitudinalPol : PolarizedKinematics gWit :=
  .longitudinal kPol gWit_isSymm kPol_k_self (by rw [kPol_p_k]; exact one_ne_zero)
    (by rw [kPol_M2]; exact one_pos)

/-- The transversely polarised witness configuration, with reference direction `(0, 0, 1)`. -/
def transversePol : PolarizedKinematics gWit :=
  .transverse kPol (0, 0, 1) gWit_isSymm (by rw [kPol_p_k]; exact one_ne_zero)
    (by simp [transverseComponent_kPol])

end Witness

end Polarized
end DIS
end Scattering
end QFT
end EpsilonEridani
