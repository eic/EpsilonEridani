/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import EpsilonEridani.Algebra.AlgebraicGroup.DiagonalizableGroup.SmoothConnected
public import EpsilonEridani.Algebra.AlgebraicGroup.Smooth.GeometricallyReduced
public import EpsilonEridani.Algebra.AlgebraicGroup.Torus.Basic
import EpsilonEridani.Algebra.AlgebraicGroup.Connected.BaseChange
import EpsilonEridani.Algebra.AlgebraicGroup.GeometricallyReduced.BaseChange

/-!
# Smoothness and connectedness of tori

A torus becomes split over an algebraic closure. The base-change descent theorems transport both
geometric properties back to the ground field. Finally, geometric reducedness of a finite-type
affine group over a field implies smoothness, so every torus is smooth.

## Main declarations

* `EpsilonEridani.torusCommHopfAlgProperty.geometricallyConnected`: every torus is geometrically
  connected.
* `EpsilonEridani.torusCommHopfAlgProperty.geometricallyReduced`: every torus is geometrically reduced.
* `EpsilonEridani.torusCommHopfAlgProperty.smooth`: every torus is smooth.

## References

* J. S. Milne, *Algebraic Groups* (2017), Definitions 12.14 and 12.17.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Chapter 2.

This completes the smoothness and geometric-connectedness part of Layer 4, "Tori: split and
non-split", of the ReductiveGroups roadmap. The character lattice of a non-split torus with its
Galois action remains to be constructed.
-/

public section

open CategoryTheory
namespace EpsilonEridani

universe u

/-- **Every torus over a field is geometrically connected.** -/
@[grind →]
theorem torusCommHopfAlgProperty.geometricallyConnected
    (k : Type u) [Field k] (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (hH : torusCommHopfAlgProperty k H) :
    geometricallyConnectedCommHopfAlgProperty k H.obj := by
  rw [torusCommHopfAlgProperty_iff] at hH
  obtain ⟨n, ⟨i⟩⟩ := hH
  apply geometricallyConnectedCommHopfAlgProperty.of_baseChange
    k (AlgebraicClosure k) H.obj
  exact (geometricallyConnectedCommHopfAlgProperty (AlgebraicClosure k)).prop_of_iso
    ((forget₂ (FiniteTypeCommHopfAlgCat.{u, u} (AlgebraicClosure k))
      (CommHopfAlgCat.{u} (AlgebraicClosure k))).mapIso i)
    (DiagonalizableGroup.geometricallyConnected_coordinateRing
      (AlgebraicClosure k) (SplitTorus.characterGroup (ULift.{u} (Fin n))))

/-- **Every torus over a field is geometrically reduced.** -/
@[grind →]
theorem torusCommHopfAlgProperty.geometricallyReduced
    (k : Type u) [Field k] (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (hH : torusCommHopfAlgProperty k H) :
    geometricallyReducedCommHopfAlgProperty k H.obj := by
  rw [torusCommHopfAlgProperty_iff] at hH
  obtain ⟨n, ⟨i⟩⟩ := hH
  apply geometricallyReducedCommHopfAlgProperty.of_baseChange
    (AlgebraicClosure k) H.obj
  exact (geometricallyReducedCommHopfAlgProperty (AlgebraicClosure k)).prop_of_iso
    ((forget₂ (FiniteTypeCommHopfAlgCat.{u, u} (AlgebraicClosure k))
      (CommHopfAlgCat.{u} (AlgebraicClosure k))).mapIso i)
    (DiagonalizableGroup.geometricallyReduced_coordinateRing
      (AlgebraicClosure k) (SplitTorus.characterGroup (ULift.{u} (Fin n))))

/-- **Every torus over a field is smooth.** -/
@[grind →]
theorem torusCommHopfAlgProperty.smooth
    (k : Type u) [Field k] (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (hH : torusCommHopfAlgProperty k H) :
    smoothCommHopfAlgProperty k H.obj :=
  smoothCommHopfAlgProperty_of_geometricallyReduced k H.obj hH.geometricallyReduced

end EpsilonEridani
