/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import EpsilonEridani.Algebra.Lie.Presentation.Serre.Automorphism
public import EpsilonEridani.Algebra.Lie.Presentation.Serre.Basis
public import EpsilonEridani.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Basic

/-!
# The Serre presentation of the pinned split Lie algebra of a Dynkin type

`EpsilonEridani.DynkinType.lieAlgebra` is the concrete matrix Lie algebra that Geck's construction
attaches to the pinned root datum of a valid Dynkin type, and `EpsilonEridani.DynkinType.lieBasis` is its
Chevalley generators numbered by Bourbaki node. `Matrix.ToLieAlgebra ℚ t.cartanMatrixᵀ` is the
abstract Lie algebra presented by Serre's relations for the same numbered Cartan matrix. This file
names the homomorphism between them, `EpsilonEridani.DynkinType.serreLift`, and proves it surjective.

The two carriers are the two ways a Chevalley--Demazure construction can name its Lie algebra: the
presentation carries the generators and relations that the Kostant `ℤ`-form is written against,
while Geck's matrices carry the root system and the nilpotency of the raising generators. The
named comparison map here specialises the universal map induced by a Lie algebra basis to the
pinned Dynkin type, without invoking `Classical.choose`.

The matrix is transposed on the way. `EpsilonEridani.IsSerreSystem` follows Serre's convention
`⁅Hᵢ, Eⱼ⁆ = CMᵢⱼ Eⱼ`, whereas `LieAlgebra.Basis.lie_h_e` reads `⁅hⱼ, eᵢ⁆ = Aᵢⱼ eᵢ`, so the Cartan
matrix presenting `EpsilonEridani.DynkinType.lieAlgebra` is `t.cartanMatrixᵀ`. Since `t.cartanMatrixᵀ i j`
is `t.cartanMatrix j i` definitionally, no reindexing of `Fin t.rank` is involved and the Bourbaki
numbering is the same on both sides.

Two things the presentation does not know on its own are read off the comparison map. The pinned
Serre generators are nonzero, and the Cartan generators are even linearly independent, because
their images are; nothing in Serre's relations says so, and for a matrix that is not a Cartan
matrix the presented algebra can collapse. And the Chevalley involution of the presentation,
`EpsilonEridani.serreChevalleyInvolution`, is carried to the concrete signed involution
`EpsilonEridani.geckChevalleyInvolution` of Geck's algebra.

No claim is made that `EpsilonEridani.DynkinType.serreLift` is injective. That is Serre's theorem, and it
is not needed by a construction that starts from the concrete algebra and only wants to write its
generators and relations down.

## Main definitions

* `EpsilonEridani.DynkinType.SerreLieAlgebra`: the Lie algebra presented by Serre's relations for the
  pinned Cartan matrix of a Dynkin type.
* `EpsilonEridani.DynkinType.serreLift`: the homomorphism from it onto the pinned split Lie algebra.

## Main results

* `EpsilonEridani.DynkinType.isSerreSystem_lieBasis`: the pinned Chevalley generators satisfy Serre's
  relations for `t.cartanMatrixᵀ`.
* `EpsilonEridani.DynkinType.serreLift_surjective`: the pinned split Lie algebra is a quotient of the
  presentation.
* `EpsilonEridani.DynkinType.eq_serreLift`: the comparison map is the only homomorphism sending the Serre
  generators to the pinned Chevalley generators.
* `EpsilonEridani.DynkinType.serreE_ne_zero`, `EpsilonEridani.DynkinType.serreF_ne_zero`,
  `EpsilonEridani.DynkinType.serreH_ne_zero` and `EpsilonEridani.DynkinType.linearIndependent_serreH`: the
  pinned Serre generators do not collapse.
* `EpsilonEridani.DynkinType.nontrivial_serreLieAlgebra`: the presented algebra is nontrivial.
* `EpsilonEridani.DynkinType.serreLift_serreChevalleyInvolution`: the comparison map intertwines the
  two Chevalley involutions.

## References

* [J.P. Serre, *Complex Semisimple Lie Algebras*][serre1965], chapter VI
* M. Geck, *On the construction of semisimple Lie algebras and Chevalley groups*,
  Proc. Amer. Math. Soc. **145** (2017), 3233--3247.

## Roadmap

Layer 9 of `EpsilonEridaniRoadmap/ReductiveGroups/README.md` asks for the split reductive group scheme
over `ℤ` to be constructed "via a Chevalley basis and the Kostant `ℤ`-form of the enveloping
algebra", and insists on constructions rather than existence theorems.
`EpsilonEridani.serreKostantForm` of `EpsilonEridani/Algebra/Lie/UniversalEnveloping/Kostant/Serre.lean` is that
Kostant form, written against `Matrix.ToLieAlgebra ℚ CM`; this file pins `CM` to the numbered
Cartan matrix of a Dynkin type and identifies the presented algebra's image with the concrete
carrier `EpsilonEridani.DynkinType.lieAlgebra`. Milestone L0 of
`EpsilonEridaniRoadmap/CFSGStatement/README.md` is the downstream consumer, reaching a Dynkin type
through `EpsilonEridani.ValidLieTypeIndex.dynkinType` and `EpsilonEridani.ValidLieTypeIndex.dynkinType_valid`.

The higher Serre relations come from `EpsilonEridani/Algebra/Lie/Presentation/Serre/Basis.lean`, which
proves them for any `LieAlgebra.Basis` on a Noetherian Lie algebra. The root-string form in
`EpsilonEridani/Algebra/Lie/Presentation/Serre/Killing.lean` does not apply here: the pinned algebra is
built over `ℚ`, and Mathlib establishes a trivial radical for Geck's construction only over an
algebraically closed field.
-/

public section

open scoped Matrix

namespace EpsilonEridani.DynkinType

open RootPairing.GeckConstruction

noncomputable section

-- Matrices form a Lie ring through their commutator, which is how Geck's construction reads
-- them; the module defining `EpsilonEridani.DynkinType.lieAlgebra` activates the same instance locally.
attribute [local instance 100] LieRing.ofAssociativeRing

variable (t : DynkinType) (ht : t.Valid)

/-! ## The presented algebra and the comparison map -/

/-- **The Lie algebra presented by Serre's relations for a Dynkin type**, for the pinned Cartan
matrix in the Bourbaki numbering.

The matrix is transposed because `EpsilonEridani.IsSerreSystem` follows Serre's convention
`⁅Hᵢ, Eⱼ⁆ = CMᵢⱼ Eⱼ`; see the module docstring. Validity of the type is not needed to write the
presentation down, only to compare it with `EpsilonEridani.DynkinType.lieAlgebra`. -/
abbrev SerreLieAlgebra : Type := Matrix.ToLieAlgebra ℚ t.cartanMatrixᵀ

/-- **The pinned Chevalley generators satisfy Serre's relations** for the transposed pinned Cartan
matrix. -/
theorem isSerreSystem_lieBasis :
    IsSerreSystem ℚ t.cartanMatrixᵀ (t.lieBasis ht).h (t.lieBasis ht).e (t.lieBasis ht).f := by
  rw [← t.lieBasis_A_eq ht]
  exact _root_.EpsilonEridani.isSerreSystem_lieBasis (t.lieBasis ht)

/-- **The comparison map from the Serre presentation of a Dynkin type to its pinned split Lie
algebra**, sending each Serre generator to the Chevalley generator with the same Bourbaki
number. -/
def serreLift : t.SerreLieAlgebra →ₗ⁅ℚ⁆ t.lieAlgebra ht :=
  _root_.EpsilonEridani.serreLift (t.isSerreSystem_lieBasis ht)

@[simp] theorem serreLift_serreH (i : Fin t.rank) :
    t.serreLift ht (serreH ℚ t.cartanMatrixᵀ i) = (t.lieBasis ht).h i :=
  _root_.EpsilonEridani.serreLift_serreH _ i

@[simp] theorem serreLift_serreE (i : Fin t.rank) :
    t.serreLift ht (serreE ℚ t.cartanMatrixᵀ i) = (t.lieBasis ht).e i :=
  _root_.EpsilonEridani.serreLift_serreE _ i

@[simp] theorem serreLift_serreF (i : Fin t.rank) :
    t.serreLift ht (serreF ℚ t.cartanMatrixᵀ i) = (t.lieBasis ht).f i :=
  _root_.EpsilonEridani.serreLift_serreF _ i

/-- **The comparison map is the unique homomorphism sending the Serre generators to the pinned
Chevalley generators.** -/
theorem eq_serreLift {g : t.SerreLieAlgebra →ₗ⁅ℚ⁆ t.lieAlgebra ht}
    (hH : ∀ i, g (serreH ℚ t.cartanMatrixᵀ i) = (t.lieBasis ht).h i)
    (hE : ∀ i, g (serreE ℚ t.cartanMatrixᵀ i) = (t.lieBasis ht).e i)
    (hF : ∀ i, g (serreF ℚ t.cartanMatrixᵀ i) = (t.lieBasis ht).f i) :
    g = t.serreLift ht :=
  _root_.EpsilonEridani.eq_serreLift hH hE hF

/-- **The pinned split Lie algebra is a quotient of its Serre presentation.** The raising and
lowering generators generate it, which is what makes the comparison map surjective. -/
theorem serreLift_surjective : Function.Surjective (t.serreLift ht) :=
  _root_.EpsilonEridani.serreLift_surjective (t.isSerreSystem_lieBasis ht) (t.lieBasis ht).span_ef

/-! ## The generators do not collapse

Serre's relations alone do not forbid a generator from being zero in the presented algebra: for a
matrix that is not a Cartan matrix the presentation can degenerate. Here the concrete realization
rules it out, since a generator with a nonzero image is nonzero. -/

include ht in
/-- The pinned Serre raising generators are nonzero. -/
theorem serreE_ne_zero (i : Fin t.rank) : serreE ℚ t.cartanMatrixᵀ i ≠ 0 := fun hi =>
  _root_.EpsilonEridani.serreE_ne_zero (t.isSerreSystem_lieBasis ht)
    ((t.lieBasis ht).sl2 i).e_ne_zero hi

include ht in
/-- The pinned Serre lowering generators are nonzero. -/
theorem serreF_ne_zero (i : Fin t.rank) : serreF ℚ t.cartanMatrixᵀ i ≠ 0 := fun hi =>
  _root_.EpsilonEridani.serreF_ne_zero (t.isSerreSystem_lieBasis ht)
    ((t.lieBasis ht).sl2 i).f_ne_zero hi

include ht in
/-- **The pinned Serre Cartan generators are linearly independent**, since the Cartan generators of
a `LieAlgebra.Basis` are. -/
theorem linearIndependent_serreH : LinearIndependent ℚ (serreH ℚ t.cartanMatrixᵀ) := by
  exact _root_.EpsilonEridani.linearIndependent_serreH (t.isSerreSystem_lieBasis ht)
    (t.lieBasis ht).linInd

include ht in
/-- The pinned Serre Cartan generators are nonzero. -/
theorem serreH_ne_zero (i : Fin t.rank) : serreH ℚ t.cartanMatrixᵀ i ≠ 0 :=
  (t.linearIndependent_serreH ht).ne_zero i

include ht in
/-- The Serre presentation of a valid Dynkin type is nontrivial. -/
theorem nontrivial_serreLieAlgebra : Nontrivial t.SerreLieAlgebra :=
  ⟨serreE ℚ t.cartanMatrixᵀ ⟨0, rank_pos ht⟩, 0, t.serreE_ne_zero ht _⟩

/-- **The comparison map intertwines the two Chevalley involutions**: the signed exchange of the
Serre generators is carried to the signed exchange of the pinned Chevalley generators. -/
@[simp]
theorem serreLift_serreChevalleyInvolution (x : t.SerreLieAlgebra) :
    t.serreLift ht (serreChevalleyInvolution ℚ t.cartanMatrixᵀ x) =
      t.chevalleyInvolution ht (t.serreLift ht x) := by
  have hcomp :
      (t.serreLift ht).comp
          (serreChevalleyInvolution ℚ t.cartanMatrixᵀ :
            t.SerreLieAlgebra →ₗ⁅ℚ⁆ t.SerreLieAlgebra) =
        (t.chevalleyInvolution ht : t.lieAlgebra ht →ₗ⁅ℚ⁆ t.lieAlgebra ht).comp
          (t.serreLift ht) :=
    serre_hom_ext
      (fun i => by
        simp only [LieHom.comp_apply, LieEquiv.coe_coe, serreChevalleyInvolution_serreH, map_neg,
          t.serreLift_serreH ht]
        exact (t.chevalleyInvolution_lieBasis_h ht i).symm)
      (fun i => by
        simp only [LieHom.comp_apply, LieEquiv.coe_coe, serreChevalleyInvolution_serreE, map_neg,
          t.serreLift_serreE ht, t.serreLift_serreF ht]
        exact (t.chevalleyInvolution_lieBasis_e ht i).symm)
      fun i => by
        simp only [LieHom.comp_apply, LieEquiv.coe_coe, serreChevalleyInvolution_serreF, map_neg,
          t.serreLift_serreE ht, t.serreLift_serreF ht]
        exact (t.chevalleyInvolution_lieBasis_f ht i).symm
  exact DFunLike.congr_fun hcomp x

end

end EpsilonEridani.DynkinType
