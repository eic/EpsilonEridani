/-
Copyright (c) 2026 The EpsilonEridani contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The EpsilonEridani contributors
-/
module

import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Ring

/-!
# Representation Content of One Generation

This module defines the electroweak representation content of one fermion generation.
The generation consists of a left-handed quark doublet, two right-handed quark singlets,
a left-handed lepton doublet, and a right-handed charged-lepton singlet.

The central result is that the Standard Model hypercharge assignments are the unique
assignments (up to overall scale and swapping the two right-handed quark singlets)
for which the sum of the cubes and the sum of the hypercharges over a generation
both vanish — the anomaly cancellation conditions.
-/

public section

namespace EpsilonEridani.QFT.Scattering.DIS.PVES.Electroweak

/-- The chirality of a fermion representation. -/
inductive Chirality where
  | L
  | R
  deriving DecidableEq, Repr

/-- An electroweak multiplet presented by its representation labels. -/
structure ElectroweakMultiplet where
  /-- Weak isospin representation dimension (2 for doublet, 1 for singlet). -/
  isospin : ℕ
  /-- Hypercharge Y. -/
  Y : ℚ
  /-- Chirality. -/
  chirality : Chirality
  deriving DecidableEq, Repr

/-- A hypercharge assignment for the five multiplets of one generation.
The fields correspond to the left-handed quark doublet (`YQ`), the two right-handed
quark singlets (`Yu`, `Yd`), the left-handed lepton doublet (`YL`), and the
right-handed charged-lepton singlet (`Ye`). -/
structure GenerationAssignments where
  /-- Hypercharge of the left-handed quark doublet. -/
  YQ : ℚ
  /-- Hypercharge of the right-handed up-type quark singlet. -/
  Yu : ℚ
  /-- Hypercharge of the right-handed down-type quark singlet. -/
  Yd : ℚ
  /-- Hypercharge of the left-handed lepton doublet. -/
  YL : ℚ
  /-- Hypercharge of the right-handed charged-lepton singlet. -/
  Ye : ℚ

/-- The linear anomaly cancellation condition for the assignments.
This incorporates the gravitational, SU(2)²×U(1), and SU(3)²×U(1) anomalies,
which are linear in the hypercharges. -/
def linearAnomaly (a : GenerationAssignments) : ℚ × ℚ × ℚ :=
  (6 * a.YQ + 2 * a.YL - 3 * a.Yu - 3 * a.Yd - a.Ye,
   3 * a.YQ + a.YL,
   2 * a.YQ - a.Yu - a.Yd)

/-- The cubic anomaly cancellation condition for the assignments (U(1)³). -/
def cubicAnomaly (a : GenerationAssignments) : ℚ :=
  6 * a.YQ^3 + 2 * a.YL^3 - 3 * a.Yu^3 - 3 * a.Yd^3 - a.Ye^3

/-- The hypercharge assignments of one generation are the unique assignments, up to overall
scale, for which the anomaly cancellation conditions vanish. The non-trivial assignments
(`YQ ≠ 0`) fix all other hypercharges in terms of `YQ`, up to a permutation of the two
identical right-handed quark singlets. -/
theorem hypercharge_unique (a : GenerationAssignments) (hYQ : a.YQ ≠ 0)
    (h_lin : linearAnomaly a = (0, 0, 0))
    (h_cub : cubicAnomaly a = 0) :
    ∃ q : ℚ,
      a.YQ = (1/3) * q ∧
      a.YL = -1 * q ∧
      a.Ye = -2 * q ∧
      ((a.Yu = (4/3) * q ∧ a.Yd = -(2/3) * q) ∨
       (a.Yu = -(2/3) * q ∧ a.Yd = (4/3) * q)) := by
  use 3 * a.YQ
  have eq1 : 6 * a.YQ + 2 * a.YL - 3 * a.Yu - 3 * a.Yd - a.Ye = 0 := congrArg (fun x => x.1) h_lin
  have eq2 : 3 * a.YQ + a.YL = 0 := congrArg (fun x => x.2.1) h_lin
  have eq3 : 2 * a.YQ - a.Yu - a.Yd = 0 := congrArg (fun x => x.2.2) h_lin
  have hYL : a.YL = -3 * a.YQ := by
    calc a.YL = (3 * a.YQ + a.YL) - 3 * a.YQ := by ring
      _ = 0 - 3 * a.YQ := by rw [eq2]
      _ = -3 * a.YQ := by ring
  have hYd : a.Yd = 2 * a.YQ - a.Yu := by
    calc a.Yd = (2 * a.YQ - a.Yu - a.Yd) + a.Yd - (2 * a.YQ - a.Yu - a.Yd) := by ring
      _ = 0 + a.Yd - 0 := by rw [eq3]
      _ = a.Yd := by ring
      _ = 2 * a.YQ - a.Yu - (2 * a.YQ - a.Yu - a.Yd) := by ring
      _ = 2 * a.YQ - a.Yu - 0 := by rw [eq3]
      _ = 2 * a.YQ - a.Yu := by ring
  have hYe : a.Ye = -6 * a.YQ := by
    calc a.Ye = (6 * a.YQ + 2 * a.YL - 3 * a.Yu - 3 * a.Yd - a.Ye) * (-1)
              + 6 * a.YQ + 2 * a.YL - 3 * a.Yu - 3 * a.Yd := by ring
      _ = 0 * (-1) + 6 * a.YQ + 2 * a.YL - 3 * a.Yu - 3 * a.Yd := by rw [eq1]
      _ = 6 * a.YQ + 2 * (-3 * a.YQ) - 3 * a.Yu - 3 * (2 * a.YQ - a.Yu) := by rw [hYL, hYd]; ring
      _ = -6 * a.YQ := by ring
  unfold cubicAnomaly at h_cub
  have h_cub' : 18 * a.YQ * (a.Yu^2 - 2 * a.YQ * a.Yu - 8 * a.YQ^2) = 0 := by
    calc 18 * a.YQ * (a.Yu^2 - 2 * a.YQ * a.Yu - 8 * a.YQ^2)
      _ = - (6 * a.YQ^3 + 2 * (-3 * a.YQ)^3 - 3 * a.Yu^3
            - 3 * (2 * a.YQ - a.Yu)^3 - (-6 * a.YQ)^3) := by ring
      _ = - (6 * a.YQ^3 + 2 * a.YL^3 - 3 * a.Yu^3 - 3 * a.Yd^3 - a.Ye^3) := by
        rw [hYL, hYd, hYe]
      _ = - 0 := by rw [h_cub]
      _ = 0 := by ring
  have h_cub'' : a.Yu^2 - 2 * a.YQ * a.Yu - 8 * a.YQ^2 = 0 := by
    cases mul_eq_zero.mp h_cub' with
    | inl h =>
      exfalso
      cases mul_eq_zero.mp h with
      | inl h18 => norm_num at h18
      | inr hYQ' => exact hYQ hYQ'
    | inr h => exact h
  have h_factor : (a.Yu - 4 * a.YQ) * (a.Yu + 2 * a.YQ) = 0 := by
    calc (a.Yu - 4 * a.YQ) * (a.Yu + 2 * a.YQ)
      _ = a.Yu^2 - 2 * a.YQ * a.Yu - 8 * a.YQ^2 := by ring
      _ = 0 := h_cub''
  rcases mul_eq_zero.mp h_factor with h4 | h2
  · have hYu : a.Yu = 4 * a.YQ := by
      calc a.Yu = (a.Yu - 4 * a.YQ) + 4 * a.YQ := by ring
        _ = 0 + 4 * a.YQ := by rw [h4]
        _ = 4 * a.YQ := by ring
    have hYd2 : a.Yd = -2 * a.YQ := by
      calc a.Yd = 2 * a.YQ - a.Yu := hYd
        _ = 2 * a.YQ - (4 * a.YQ) := by rw [hYu]
        _ = -2 * a.YQ := by ring
    refine ⟨by ring, by rw [hYL]; ring, by rw [hYe]; ring, Or.inl ⟨?_, ?_⟩⟩
    · rw [hYu]; ring
    · rw [hYd2]; ring
  · have hYu : a.Yu = -2 * a.YQ := by
      calc a.Yu = (a.Yu + 2 * a.YQ) - 2 * a.YQ := by ring
        _ = 0 - 2 * a.YQ := by rw [h2]
        _ = -2 * a.YQ := by ring
    have hYd2 : a.Yd = 4 * a.YQ := by
      calc a.Yd = 2 * a.YQ - a.Yu := hYd
        _ = 2 * a.YQ - (-2 * a.YQ) := by rw [hYu]
        _ = 4 * a.YQ := by ring
    refine ⟨by ring, by rw [hYL]; ring, by rw [hYe]; ring, Or.inr ⟨?_, ?_⟩⟩
    · rw [hYu]; ring
    · rw [hYd2]; ring

end EpsilonEridani.QFT.Scattering.DIS.PVES.Electroweak

end
