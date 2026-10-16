/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.Particles.Parton.Species
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The singlet and non-singlet decomposition of flavour space

A vector `v : Species Flavor → R` assigns a value to each quark, antiquark and the gluon: the
parton densities of a hadron at fixed momentum fraction and scale, their Mellin moments, or the
fragmentation functions of the parton species into a fixed hadron. This file decomposes that
flavour space into the two sectors that collinear evolution keeps apart.

* The *quark singlet* `Σ v = ∑ᵢ (v (quark i) + v (antiquark i))` (`singlet`) and the gluon
  component together describe the two-dimensional *singlet sector* `singletSector`, spanned by
  `singletVector` (one on every quark and antiquark, zero on the gluon) and the gluon basis
  vector.
* The *non-singlet sector* `nonSinglet` consists of the vectors with vanishing quark singlet and
  vanishing gluon component. It contains the valence combinations `q_i - q̄_i` and the flavour
  differences `(q_i + q̄_i) - (q_j + q̄_j)`.

A splitting-kernel or anomalous-dimension matrix whose quark lines conserve flavour, and whose
four channels `q ← q`, `q ← g`, `g ← q` and `g ← g` depend neither on the flavour nor on the
distinction between quark and antiquark, is `flavorBlindMatrix qq qg gq gg`. The leading-order
QCD kernels have this shape. For such a matrix `P`:

* the quark singlet and the gluon component of `P *ᵥ v` depend on `v` only through its quark
  singlet and gluon component, through the `2 × 2` matrix `singletGluonMatrix` whose
  quark-from-gluon entry is `2 n_f qg`;
* every non-singlet vector is an eigenvector of `P` with eigenvalue `qq`, and every non-singlet
  combination `w ⬝ᵥ f` of an arbitrary vector `f` is multiplied by `qq`: the quark-gluon mixing
  acts only on the singlet;
* both sectors are invariant, and when `2 n_f` is invertible they are complementary, of
  dimensions `2` and `2 n_f - 1` over a field.

The transpose of `flavorBlindMatrix qq qg gq gg` is `flavorBlindMatrix qq gq qg gg`
(`transpose_flavorBlindMatrix`). The evolution of the fragmentation functions into a fixed hadron
is governed by the transposed (timelike) kernel matrix, which therefore has the same shape, so
every statement here applies to it as well.

## Main definitions

* `Species.singlet`: the quark singlet, as a linear functional on flavour space.
* `Species.singletVector`: the vector that is one on every quark and antiquark.
* `Species.singletGluon`: the pair `(Σ v, v gluon)`, as a linear map to `Fin 2 → R`.
* `Species.singletSector`, `Species.nonSinglet`: the two sectors, as submodules.
* `Species.flavorBlindMatrix`: the flavour structure of a leading-order kernel matrix.
* `Species.singletGluonMatrix`: its action on the pair `(Σ, g)`.

## Main statements

* `Species.singletGluon_flavorBlindMatrix_mulVec`: the singlet-gluon pair is mapped in closed
  form.
* `Species.flavorBlindMatrix_mulVec_of_mem_nonSinglet` and
  `Species.dotProduct_flavorBlindMatrix_mulVec_of_mem_nonSinglet`: non-singlet vectors and
  combinations are eigenvectors with eigenvalue `qq`.
* `Species.flavorBlindMatrix_mulVec_mem_singletSector`: the singlet sector is invariant.
* `Species.isCompl_singletSector_nonSinglet`: the two sectors are complementary.
* `Species.finrank_singletSector`, `Species.finrank_nonSinglet`: their dimensions `2` and
  `2 n_f - 1`.

## References

* G. Altarelli, *Partons in quantum chromodynamics*, Phys. Rep. **81** (1982) 1, §4.
* R. K. Ellis, W. J. Stirling and B. R. Webber, *QCD and Collider Physics*, Cambridge University
  Press (1996), §4.3.
-/

public section

noncomputable section

open Matrix Module

namespace EpsilonEridani
namespace Particles
namespace Parton
namespace Species

variable {Flavor : Type}

/-! ### The singlet sector -/

section Semiring

variable {R : Type*} [CommSemiring R]

/-- The vector that is one on every quark and antiquark and zero on the gluon. Together with the
gluon basis vector it spans the singlet sector. -/
def singletVector : Species Flavor → R
  | quark _ => 1
  | antiquark _ => 1
  | gluon => 0

@[simp]
theorem singletVector_quark (i : Flavor) : (singletVector (quark i) : R) = 1 := (rfl)

@[simp]
theorem singletVector_antiquark (i : Flavor) : (singletVector (antiquark i) : R) = 1 := (rfl)

@[simp]
theorem singletVector_gluon : (singletVector (gluon : Species Flavor) : R) = 0 := (rfl)

/-- The singlet sector: the span of `singletVector` and the gluon basis vector. -/
def singletSector [DecidableEq Flavor] : Submodule R (Species Flavor → R) :=
  Submodule.span R {singletVector, Pi.single gluon 1}

theorem mem_singletSector [DecidableEq Flavor] {v : Species Flavor → R} :
    v ∈ singletSector ↔ ∃ a b : R, a • singletVector + b • Pi.single gluon 1 = v :=
  Submodule.mem_span_pair

/-! ### The quark singlet and the non-singlet sector -/

variable [Fintype Flavor]

/-- The quark singlet `Σ v = ∑ᵢ (v (quark i) + v (antiquark i))` of a vector on the parton
species, as a linear functional. -/
def singlet : (Species Flavor → R) →ₗ[R] R where
  toFun v := ∑ i, (v (quark i) + v (antiquark i))
  map_add' v w := by
    simp only [Pi.add_apply, add_add_add_comm, Finset.sum_add_distrib]
  map_smul' c v := by
    simp only [Pi.smul_apply, smul_eq_mul, ← mul_add, ← Finset.mul_sum, RingHom.id_apply]

@[simp]
theorem singlet_apply (v : Species Flavor → R) :
    singlet v = ∑ i, (v (quark i) + v (antiquark i)) := (rfl)

/-- The quark singlet is the pairing with `singletVector`. -/
theorem singletVector_dotProduct (v : Species Flavor → R) : singletVector ⬝ᵥ v = singlet v := by
  simp [dotProduct, sum_univ, Finset.sum_add_distrib]

/-- The quark singlet of `singletVector` is the number `2 n_f` of quark and antiquark species. -/
@[simp]
theorem singlet_singletVector :
    singlet (singletVector : Species Flavor → R) = 2 * Fintype.card Flavor := by
  simp [one_add_one_eq_two, Finset.card_univ, mul_comm]

/-- The gluon basis vector has no quark singlet. -/
@[simp]
theorem singlet_single_gluon [DecidableEq Flavor] (b : R) :
    singlet (Pi.single (gluon : Species Flavor) b) = 0 := by
  simp

/-- The pair `(Σ v, v gluon)` of the quark singlet and the gluon component, as a linear map. -/
def singletGluon : (Species Flavor → R) →ₗ[R] Fin 2 → R :=
  LinearMap.pi ![singlet, LinearMap.proj gluon]

@[simp]
theorem singletGluon_apply (v : Species Flavor → R) :
    singletGluon v = ![singlet v, v gluon] := by
  ext k
  fin_cases k <;> simp [singletGluon]

/-- The non-singlet sector: the vectors with vanishing quark singlet and vanishing gluon
component, the kernel of `singletGluon`. -/
def nonSinglet : Submodule R (Species Flavor → R) :=
  LinearMap.ker singletGluon

@[simp]
theorem mem_nonSinglet {v : Species Flavor → R} :
    v ∈ nonSinglet ↔ singlet v = 0 ∧ v gluon = 0 := by
  simp [nonSinglet, funext_iff, Fin.forall_fin_two]

end Semiring

section Ring

variable {R : Type*} [CommRing R] [DecidableEq Flavor]

/-- The valence combination `q_i - q̄_i` is non-singlet. -/
theorem single_quark_sub_single_antiquark_mem_nonSinglet [Fintype Flavor] (i : Flavor) :
    (Pi.single (quark i) 1 - Pi.single (antiquark i) 1 : Species Flavor → R) ∈ nonSinglet := by
  simp [Pi.single_apply]

/-- The flavour difference `(q_i + q̄_i) - (q_j + q̄_j)` is non-singlet. -/
theorem single_quark_add_single_antiquark_sub_mem_nonSinglet [Fintype Flavor] (i j : Flavor) :
    (Pi.single (quark i) 1 + Pi.single (antiquark i) 1 -
      (Pi.single (quark j) 1 + Pi.single (antiquark j) 1) : Species Flavor → R) ∈ nonSinglet := by
  simp [Pi.single_apply, Finset.sum_add_distrib]

/-- When the number `2 n_f` of quark and antiquark species is invertible, flavour space is the
direct sum of the singlet sector and the non-singlet sector. -/
theorem isCompl_singletSector_nonSinglet [Fintype Flavor]
    (h : IsUnit (2 * Fintype.card Flavor : R)) :
    IsCompl (singletSector : Submodule R (Species Flavor → R)) nonSinglet := by
  constructor
  · rw [Submodule.disjoint_def]
    intro v hv hv'
    obtain ⟨a, b, rfl⟩ := mem_singletSector.1 hv
    simp only [mem_nonSinglet, map_add, map_smul, singlet_singletVector, singlet_single_gluon,
      smul_eq_mul, mul_zero, add_zero] at hv'
    obtain ⟨ha, hb⟩ := hv'
    simp_all [h.mul_left_eq_zero.1 ha]
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    -- Split off the singlet-sector part `a • singletVector + v gluon • Pi.single gluon 1`, where
    -- `a = Σ v / (2 n_f)`; the remainder has no quark singlet and no gluon component.
    let w : Species Flavor → R :=
      (↑h.unit⁻¹ * singlet v) • singletVector + v gluon • Pi.single gluon 1
    rw [← add_sub_cancel w v]
    refine Submodule.add_mem_sup (mem_singletSector.2 ⟨_, _, rfl⟩)
      (mem_nonSinglet.2 ⟨?_, by simp [w]⟩)
    simp only [w, map_sub, map_add, map_smul, singlet_singletVector, singlet_single_gluon,
      smul_eq_mul, mul_zero, add_zero]
    rw [mul_right_comm, h.val_inv_mul, one_mul, sub_self]

/-- The singlet sector is two-dimensional as soon as there is a quark flavour. -/
theorem finrank_singletSector [Nontrivial R] [Nonempty Flavor] :
    finrank R (singletSector : Submodule R (Species Flavor → R)) = 2 := by
  obtain ⟨i⟩ := ‹Nonempty Flavor›
  have hli : LinearIndependent R ![(singletVector : Species Flavor → R), Pi.single gluon 1] := by
    rw [LinearIndependent.pair_iff]
    intro a b hab
    exact ⟨by simpa using congrFun hab (quark i), by simpa using congrFun hab gluon⟩
  rw [singletSector, ← Matrix.range_cons_cons_empty, finrank_span_eq_card hli, Fintype.card_fin]

end Ring

section Field

variable {K : Type*} [Field K]

/-- When `2 n_f` is non-zero, the non-singlet sector has dimension `2 n_f - 1`: the
`2 n_f + 1` parton species less the two dimensions of the singlet sector. -/
theorem finrank_nonSinglet [Fintype Flavor] (h : (2 * Fintype.card Flavor : K) ≠ 0) :
    finrank K (nonSinglet : Submodule K (Species Flavor → K)) = 2 * Fintype.card Flavor - 1 := by
  classical
  have : Nonempty Flavor := by
    rw [← Fintype.card_pos_iff]
    by_contra hc
    simp_all
  have hsum := Submodule.finrank_add_eq_of_isCompl
    (isCompl_singletSector_nonSinglet (isUnit_iff_ne_zero.2 h))
  rw [finrank_singletSector, finrank_fintype_fun_eq_card, card] at hsum
  omega

end Field

/-! ### The flavour structure of a leading-order kernel -/

section Matrix

variable {R : Type*} [CommSemiring R] [DecidableEq Flavor]

/-- The flavour structure of a kernel matrix on the parton species whose quark lines conserve
flavour and whose four channels are blind to the flavour and to the distinction between quark and
antiquark: the entry in row `s` and column `t` is the kernel for `t → s`, namely `qq` on the
diagonal of the quark and antiquark block and `0` off it, `qg` from the gluon to each quark and
antiquark, `gq` from each quark and antiquark to the gluon, and `gg` from the gluon to itself.
The leading-order splitting kernels and anomalous dimensions of QCD have this shape. -/
def flavorBlindMatrix (qq qg gq gg : R) : Matrix (Species Flavor) (Species Flavor) R :=
  Matrix.of fun
    | quark i, quark j => if i = j then qq else 0
    | antiquark i, antiquark j => if i = j then qq else 0
    | quark _, antiquark _ => 0
    | antiquark _, quark _ => 0
    | quark _, gluon => qg
    | antiquark _, gluon => qg
    | gluon, quark _ => gq
    | gluon, antiquark _ => gq
    | gluon, gluon => gg

variable (qq qg gq gg : R)

@[simp]
theorem flavorBlindMatrix_quark_quark (i j : Flavor) :
    flavorBlindMatrix qq qg gq gg (quark i) (quark j) = if i = j then qq else 0 := (rfl)

@[simp]
theorem flavorBlindMatrix_antiquark_antiquark (i j : Flavor) :
    flavorBlindMatrix qq qg gq gg (antiquark i) (antiquark j) = if i = j then qq else 0 := (rfl)

@[simp]
theorem flavorBlindMatrix_quark_antiquark (i j : Flavor) :
    flavorBlindMatrix qq qg gq gg (quark i) (antiquark j) = 0 := (rfl)

@[simp]
theorem flavorBlindMatrix_antiquark_quark (i j : Flavor) :
    flavorBlindMatrix qq qg gq gg (antiquark i) (quark j) = 0 := (rfl)

@[simp]
theorem flavorBlindMatrix_quark_gluon (i : Flavor) :
    flavorBlindMatrix qq qg gq gg (quark i) gluon = qg := (rfl)

@[simp]
theorem flavorBlindMatrix_antiquark_gluon (i : Flavor) :
    flavorBlindMatrix qq qg gq gg (antiquark i) gluon = qg := (rfl)

@[simp]
theorem flavorBlindMatrix_gluon_quark (i : Flavor) :
    flavorBlindMatrix qq qg gq gg gluon (quark i) = gq := (rfl)

@[simp]
theorem flavorBlindMatrix_gluon_antiquark (i : Flavor) :
    flavorBlindMatrix qq qg gq gg gluon (antiquark i) = gq := (rfl)

@[simp]
theorem flavorBlindMatrix_gluon_gluon :
    flavorBlindMatrix qq qg gq gg (gluon : Species Flavor) gluon = gg := (rfl)

/-- Transposing the flavour structure exchanges the quark-from-gluon and gluon-from-quark
channels. -/
@[simp]
theorem transpose_flavorBlindMatrix :
    (flavorBlindMatrix qq qg gq gg : Matrix (Species Flavor) (Species Flavor) R)ᵀ =
      flavorBlindMatrix qq gq qg gg := by
  ext s t
  cases s <;> cases t <;> simp [eq_comm]

/-- The `2 × 2` matrix by which a flavour-blind kernel acts on the pair `(Σ, g)` of the quark
singlet and the gluon, for `n_f` quark flavours: its quark-from-gluon entry is the singlet
combination `2 n_f qg`. -/
def singletGluonMatrix (nf : ℕ) : Matrix (Fin 2) (Fin 2) R :=
  !![qq, 2 * nf * qg; gq, gg]

variable [Fintype Flavor]

@[simp]
theorem flavorBlindMatrix_mulVec_quark (v : Species Flavor → R) (i : Flavor) :
    (flavorBlindMatrix qq qg gq gg *ᵥ v) (quark i) = qq * v (quark i) + qg * v gluon := by
  simp [mulVec, dotProduct, sum_univ]

@[simp]
theorem flavorBlindMatrix_mulVec_antiquark (v : Species Flavor → R) (i : Flavor) :
    (flavorBlindMatrix qq qg gq gg *ᵥ v) (antiquark i) = qq * v (antiquark i) + qg * v gluon := by
  simp [mulVec, dotProduct, sum_univ]

/-- The gluon component of `P *ᵥ v` sees the quarks and antiquarks only through the quark
singlet. -/
@[simp]
theorem flavorBlindMatrix_mulVec_gluon (v : Species Flavor → R) :
    (flavorBlindMatrix qq qg gq gg *ᵥ v) gluon = gq * singlet v + gg * v gluon := by
  simp [mulVec, dotProduct, sum_univ, Finset.mul_sum, mul_add, Finset.sum_add_distrib]

/-- The quark singlet of `P *ᵥ v` sees `v` only through its quark singlet and its gluon
component, the gluon entering with the singlet weight `2 n_f qg`. -/
@[simp]
theorem singlet_flavorBlindMatrix_mulVec (v : Species Flavor → R) :
    singlet (flavorBlindMatrix qq qg gq gg *ᵥ v) =
      qq * singlet v + 2 * Fintype.card Flavor * qg * v gluon := by
  simp only [singlet_apply, flavorBlindMatrix_mulVec_quark, flavorBlindMatrix_mulVec_antiquark,
    Finset.mul_sum, Finset.sum_add_distrib, mul_add, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  ring

/-- **The singlet-gluon pair evolves in closed form.** The quark singlet and the gluon component
of `P *ᵥ v` are obtained from those of `v` by `singletGluonMatrix`; no non-singlet information
enters. -/
theorem singletGluon_flavorBlindMatrix_mulVec (v : Species Flavor → R) :
    singletGluon (flavorBlindMatrix qq qg gq gg *ᵥ v) =
      singletGluonMatrix qq qg gq gg (Fintype.card Flavor) *ᵥ singletGluon v := by
  rw [singletGluon_apply, singletGluon_apply, singlet_flavorBlindMatrix_mulVec,
    flavorBlindMatrix_mulVec_gluon]
  ext k
  fin_cases k <;> simp [singletGluonMatrix, mulVec, dotProduct, Fin.sum_univ_two]

/-- **Non-singlet vectors are eigenvectors.** A flavour-blind kernel acts on the non-singlet
sector as multiplication by its quark-quark entry: the gluon does not mix with it. -/
theorem flavorBlindMatrix_mulVec_of_mem_nonSinglet {v : Species Flavor → R}
    (hv : v ∈ nonSinglet) : flavorBlindMatrix qq qg gq gg *ᵥ v = qq • v := by
  rw [mem_nonSinglet] at hv
  ext s
  cases s <;> simp [hv.1, hv.2]

/-- **Non-singlet combinations evolve without gluon mixing.** For a non-singlet `w` and an
arbitrary vector `f`, the combination `w ⬝ᵥ f` of the components of `P *ᵥ f` is `qq` times the
same combination of the components of `f`. -/
theorem dotProduct_flavorBlindMatrix_mulVec_of_mem_nonSinglet {w : Species Flavor → R}
    (hw : w ∈ nonSinglet) (f : Species Flavor → R) :
    w ⬝ᵥ (flavorBlindMatrix qq qg gq gg *ᵥ f) = qq * (w ⬝ᵥ f) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, transpose_flavorBlindMatrix,
    flavorBlindMatrix_mulVec_of_mem_nonSinglet _ _ _ _ hw, smul_dotProduct, smul_eq_mul]

/-- The non-singlet sector is invariant. -/
theorem flavorBlindMatrix_mulVec_mem_nonSinglet {v : Species Flavor → R} (hv : v ∈ nonSinglet) :
    flavorBlindMatrix qq qg gq gg *ᵥ v ∈ nonSinglet := by
  rw [flavorBlindMatrix_mulVec_of_mem_nonSinglet _ _ _ _ hv]
  exact Submodule.smul_mem _ _ hv

/-- A flavour-blind kernel maps `singletVector` into the singlet sector. -/
theorem flavorBlindMatrix_mulVec_singletVector :
    flavorBlindMatrix qq qg gq gg *ᵥ singletVector =
      qq • singletVector +
        (2 * Fintype.card Flavor * gq) • Pi.single (gluon : Species Flavor) 1 := by
  ext s
  cases s <;> simp [one_add_one_eq_two, Finset.card_univ, mul_comm]

/-- A flavour-blind kernel maps the gluon basis vector into the singlet sector. -/
theorem flavorBlindMatrix_mulVec_single_gluon :
    flavorBlindMatrix qq qg gq gg *ᵥ Pi.single (gluon : Species Flavor) 1 =
      qg • singletVector + gg • Pi.single gluon 1 := by
  ext s
  cases s <;> simp

/-- The singlet sector is invariant. -/
theorem flavorBlindMatrix_mulVec_mem_singletSector {v : Species Flavor → R}
    (hv : v ∈ singletSector) : flavorBlindMatrix qq qg gq gg *ᵥ v ∈ singletSector := by
  obtain ⟨a, b, rfl⟩ := mem_singletSector.1 hv
  rw [mulVec_add, mulVec_smul, mulVec_smul, flavorBlindMatrix_mulVec_singletVector,
    flavorBlindMatrix_mulVec_single_gluon]
  have h₁ : (singletVector : Species Flavor → R) ∈ singletSector :=
    Submodule.subset_span (by simp)
  have h₂ : (Pi.single gluon 1 : Species Flavor → R) ∈ singletSector :=
    Submodule.subset_span (by simp)
  exact Submodule.add_mem _
    (Submodule.smul_mem _ _ (Submodule.add_mem _ (Submodule.smul_mem _ _ h₁)
      (Submodule.smul_mem _ _ h₂)))
    (Submodule.smul_mem _ _ (Submodule.add_mem _ (Submodule.smul_mem _ _ h₁)
      (Submodule.smul_mem _ _ h₂)))

end Matrix

end Species
end Parton
end Particles
end EpsilonEridani
