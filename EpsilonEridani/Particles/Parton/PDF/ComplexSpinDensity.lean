/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.Particles.Parton.PDF.Positivity

/-!
# The complex forward helicity-amplitude matrix

At fixed flavour, momentum fraction `x` and scale `Q²`, the forward quark-nucleon helicity
amplitudes form a hermitian positive-semidefinite `4 × 4` complex matrix in the helicity basis
`idxPP, idxPM, idxMP, idxMM` of `EpsilonEridani.Particles.Parton.PDF.SpinDensity`. This module
introduces that matrix, `SpinDensityC`, and reads the leading-twist triple off it:

* the unpolarized density `f₁` and the helicity density `Δq` (`SpinDensityC.f1`,
  `SpinDensityC.deltaQ`) are the same combinations of diagonal entries as in the real case, and
  are real because the diagonal of a hermitian matrix is real (`SpinDensityC.ofReal_f1`,
  `SpinDensityC.ofReal_deltaQ`);
* transversity `h₁` (`SpinDensityC.transversity`) is the double-helicity-flip entry, which is a
  complex number in general and is real under time-reversal invariance
  (`SpinDensityC.IsTimeReversalInvariant.im_transversity`) and under parity invariance
  (`SpinDensityC.IsParityInvariant.im_transversity`).

Time reversal is antiunitary, and in the helicity basis it acts on the forward amplitudes by
complex conjugation, so `SpinDensityC.IsTimeReversalInvariant` says that the matrix is fixed by
entrywise conjugation. For a hermitian matrix this is the same as being symmetric
(`SpinDensityC.isTimeReversalInvariant_iff_transpose_eq`). The real `SpinDensity` is exactly the
time-reversal-invariant case: `SpinDensityC.toSpinDensity` and `SpinDensity.toSpinDensityC`
are mutually inverse on it, compatibly with `f₁`, `Δq` and `h₁`, and package into
`SpinDensityC.timeReversalInvariantEquiv`. The specialisation is proper:
`SpinDensityC.exists_not_isTimeReversalInvariant` exhibits a rank-one matrix whose transversity
is `i`.

The Soffer bound `2 ‖h₁‖ ≤ f₁ + Δq` (`SpinDensityC.soffer_bound`) uses positive
semidefiniteness and nothing else: neither parity nor time reversal. Its entrywise content,
`SpinDensityC.two_mul_norm_transversity_le_diag`, is `Matrix.PosSemidef.two_mul_norm_apply_le`,
whose real specialisation `Matrix.PosSemidef.two_mul_abs_apply_le` is the inequality behind the
real `two_mul_abs_h1_le_diag`.

As in `EpsilonEridani.Particles.Parton.PDF.Positivity`, every statement here is at fixed
`(x, Q²)` and per flavour.

## References

* R. L. Jaffe and X. Ji, *Chiral-odd parton distributions and Drell-Yan processes*,
  Nucl. Phys. B **375** (1992) 527.
* J. Soffer, *Positivity constraints for spin-dependent parton distributions*,
  Phys. Rev. Lett. **74** (1995) 1292 (arXiv:hep-ph/9409254).
* V. Barone, A. Drago and P. G. Ratcliffe, *Transverse polarisation of quarks in hadrons*,
  Phys. Rept. **359** (2002) 1 (arXiv:hep-ph/0104283), §3.
-/

@[expose] public section

noncomputable section

namespace EpsilonEridani
namespace Particles
namespace Parton
namespace PDF

open Matrix ComplexConjugate
open scoped ComplexOrder

/-- The leading-twist quark-nucleon forward helicity-amplitude matrix at one flavour, one
momentum fraction `x` and one scale `Q²`, as a complex matrix in the helicity basis
`idxPP, idxPM, idxMP, idxMM` of `SpinDensity`.

As for the real `SpinDensity`, positive semidefiniteness (the probability interpretation of the
amplitudes) is the only field beyond the matrix itself. No discrete symmetry is assumed:
parity and time reversal are the separate predicates `SpinDensityC.IsParityInvariant` and
`SpinDensityC.IsTimeReversalInvariant`. -/
@[ext]
structure SpinDensityC where
  /-- The matrix of forward quark-nucleon helicity amplitudes, in the basis
  `idxPP, idxPM, idxMP, idxMM`. -/
  mat : Matrix (Fin 4) (Fin 4) ℂ
  /-- Positive semidefiniteness, i.e. the probability interpretation of the amplitudes. -/
  posSemidef : mat.PosSemidef

namespace SpinDensityC

variable (ρ : SpinDensityC)

/-- The diagonal entries of the helicity-amplitude matrix are real: they are number densities. -/
@[simp]
lemma ofReal_re_mat_apply_self (i : Fin 4) : ((ρ.mat i i).re : ℂ) = ρ.mat i i :=
  ρ.posSemidef.1.coe_re_apply_self i

/-- The unpolarized leading-twist density `f₁`, the helicity average of the diagonal number
densities. At fixed `(x, Q²)`. -/
def f1 : ℝ :=
  ((ρ.mat idxPP idxPP).re + (ρ.mat idxPM idxPM).re + (ρ.mat idxMP idxMP).re
    + (ρ.mat idxMM idxMM).re) / 2

/-- The quark helicity density `Δq`, the helicity-weighted average of the diagonal number
densities. At fixed `(x, Q²)`. This is the density called `g1` for the real `SpinDensity`. -/
def deltaQ : ℝ :=
  ((ρ.mat idxPP idxPP).re - (ρ.mat idxPM idxPM).re - (ρ.mat idxMP idxMP).re
    + (ρ.mat idxMM idxMM).re) / 2

/-- Transversity `h₁` in the Jaffe-Ji normalisation, the double-helicity-flip entry of the
helicity-amplitude matrix. At fixed `(x, Q²)`. It is complex in general, and real under
time-reversal invariance (`IsTimeReversalInvariant.im_transversity`). -/
def transversity : ℂ := ρ.mat idxPP idxMM

/-- Defining expression for `f1`. -/
lemma f1_def :
    ρ.f1 = ((ρ.mat idxPP idxPP).re + (ρ.mat idxPM idxPM).re + (ρ.mat idxMP idxMP).re
      + (ρ.mat idxMM idxMM).re) / 2 := rfl

/-- Defining expression for `deltaQ`. -/
lemma deltaQ_def :
    ρ.deltaQ = ((ρ.mat idxPP idxPP).re - (ρ.mat idxPM idxPM).re - (ρ.mat idxMP idxMP).re
      + (ρ.mat idxMM idxMM).re) / 2 := rfl

/-- Defining expression for `transversity`. -/
lemma transversity_def : ρ.transversity = ρ.mat idxPP idxMM := rfl

/-- `f₁` is real: the helicity average of the complex diagonal entries is the real number
`f1`. -/
lemma ofReal_f1 :
    (ρ.f1 : ℂ) = (ρ.mat idxPP idxPP + ρ.mat idxPM idxPM + ρ.mat idxMP idxMP
      + ρ.mat idxMM idxMM) / 2 := by
  simp [f1]

/-- `Δq` is real: the helicity-weighted average of the complex diagonal entries is the real
number `deltaQ`. -/
lemma ofReal_deltaQ :
    (ρ.deltaQ : ℂ) = (ρ.mat idxPP idxPP - ρ.mat idxPM idxPM - ρ.mat idxMP idxMP
      + ρ.mat idxMM idxMM) / 2 := by
  simp [deltaQ]

/-- `f₁ + Δq` is twice the aligned diagonal entry of the helicity-amplitude matrix. This is
the combination the Soffer bound constrains. -/
lemma f1_add_deltaQ : ρ.f1 + ρ.deltaQ = (ρ.mat idxPP idxPP).re + (ρ.mat idxMM idxMM).re := by
  rw [f1, deltaQ]; ring

/-- `f₁ - Δq` is twice the anti-aligned diagonal entry of the helicity-amplitude matrix. -/
lemma f1_sub_deltaQ : ρ.f1 - ρ.deltaQ = (ρ.mat idxPM idxPM).re + (ρ.mat idxMP idxMP).re := by
  rw [f1, deltaQ]; ring

/-- The positive-semidefiniteness content of the Soffer bound, with the norm of the complex
double-helicity-flip entry in place of an absolute value. This is
`Matrix.PosSemidef.two_mul_norm_apply_le` at the indices `idxPP`, `idxMM`; for a real matrix it
is `two_mul_abs_h1_le_diag`, through `Matrix.PosSemidef.two_mul_abs_apply_le`. -/
theorem two_mul_norm_transversity_le_diag :
    2 * ‖ρ.transversity‖ ≤ (ρ.mat idxPP idxPP).re + (ρ.mat idxMM idxMM).re :=
  ρ.posSemidef.two_mul_norm_apply_le idxPP idxMM

/-- **The Soffer bound for the complex helicity-amplitude matrix.** `2 ‖h₁‖ ≤ f₁ + Δq` at fixed
`(x, Q²)`, from positive semidefiniteness alone; it uses neither parity nor time-reversal
invariance.

J. Soffer, Phys. Rev. Lett. **74** (1995) 1292 (arXiv:hep-ph/9409254). -/
theorem soffer_bound : 2 * ‖ρ.transversity‖ ≤ ρ.f1 + ρ.deltaQ := by
  rw [f1_add_deltaQ]
  exact ρ.two_mul_norm_transversity_le_diag

/-! ### Parity -/

/-- Parity invariance of the helicity-amplitude matrix: reversing every helicity leaves every
entry unchanged, `A_{Λλ,Λ'λ'} = A_{-Λ-λ,-Λ'-λ'}`. In the basis order `idxPP, idxPM, idxMP, idxMM`,
reversing both helicities of a basis index is `Fin.rev`. As for the real `SpinDensity`, this is a
hypothesis to be supplied, not a field, because the Soffer bound does not need it.

Unlike the real `IsParityInvariant`, which records only its diagonal content, this constrains the
off-diagonal entries too; with hermiticity it makes transversity real
(`IsParityInvariant.im_transversity`). -/
def IsParityInvariant : Prop :=
  ∀ i j, ρ.mat i.rev j.rev = ρ.mat i j

/-- Under parity invariance the two aligned diagonal entries are equal. -/
lemma IsParityInvariant.mat_idxMM_idxMM {ρ : SpinDensityC} (h : ρ.IsParityInvariant) :
    ρ.mat idxMM idxMM = ρ.mat idxPP idxPP :=
  h idxPP idxPP

/-- Under parity invariance the two anti-aligned diagonal entries are equal. -/
lemma IsParityInvariant.mat_idxMP_idxMP {ρ : SpinDensityC} (h : ρ.IsParityInvariant) :
    ρ.mat idxMP idxMP = ρ.mat idxPM idxPM :=
  h idxPM idxPM

/-- Under parity invariance `f₁` reduces to the single-nucleon-helicity expression
`q_{+/+} + q_{−/+}`. -/
lemma f1_eq_of_parityInvariant (h : ρ.IsParityInvariant) :
    ρ.f1 = (ρ.mat idxPP idxPP).re + (ρ.mat idxPM idxPM).re := by
  rw [f1, h.mat_idxMM_idxMM, h.mat_idxMP_idxMP]; ring

/-- Under parity invariance `Δq` reduces to the single-nucleon-helicity expression
`q_{+/+} - q_{−/+}`. -/
lemma deltaQ_eq_of_parityInvariant (h : ρ.IsParityInvariant) :
    ρ.deltaQ = (ρ.mat idxPP idxPP).re - (ρ.mat idxPM idxPM).re := by
  rw [deltaQ, h.mat_idxMM_idxMM, h.mat_idxMP_idxMP]; ring

/-- Under parity invariance transversity is real: parity identifies the double-flip entry with
its transpose, which hermiticity identifies with its conjugate. -/
lemma IsParityInvariant.im_transversity {ρ : SpinDensityC} (h : ρ.IsParityInvariant) :
    ρ.transversity.im = 0 := by
  have hconj : conj (ρ.mat idxMM idxPP) = ρ.mat idxPP idxMM := ρ.posSemidef.1.apply idxPP idxMM
  rw [← h idxMM idxPP] at hconj
  exact Complex.conj_eq_iff_im.mp hconj

/-! ### Time reversal and the real specialisation -/

/-- Time-reversal invariance of the helicity-amplitude matrix. Time reversal is antiunitary and,
with the standard phase conventions for the helicity states, acts on the forward amplitudes in
the helicity basis by complex conjugation, so invariance says that the matrix equals its entrywise
complex conjugate. Under it the double-flip entry is real
and the matrix descends to the real `SpinDensity` (`toSpinDensity`). -/
def IsTimeReversalInvariant : Prop :=
  ρ.mat.map (starRingEnd ℂ) = ρ.mat

/-- Time-reversal invariance says exactly that every entry of the matrix is real. -/
lemma isTimeReversalInvariant_iff_forall_im_eq_zero :
    ρ.IsTimeReversalInvariant ↔ ∀ i j, (ρ.mat i j).im = 0 := by
  simp [IsTimeReversalInvariant, ← Matrix.ext_iff, Complex.conj_eq_iff_im]

/-- For the hermitian helicity-amplitude matrix, time-reversal invariance is the same as
symmetry of the matrix. -/
lemma isTimeReversalInvariant_iff_transpose_eq :
    ρ.IsTimeReversalInvariant ↔ ρ.matᵀ = ρ.mat := by
  have hconj : ∀ i j, conj (ρ.mat i j) = ρ.mat j i := fun i j => ρ.posSemidef.1.apply j i
  simp only [IsTimeReversalInvariant, ← Matrix.ext_iff, map_apply, transpose_apply, hconj]

/-- Under time-reversal invariance transversity is real. -/
lemma IsTimeReversalInvariant.im_transversity {ρ : SpinDensityC}
    (h : ρ.IsTimeReversalInvariant) : ρ.transversity.im = 0 :=
  (ρ.isTimeReversalInvariant_iff_forall_im_eq_zero.mp h) idxPP idxMM

/-- A time-reversal-invariant matrix is the image of its real part under `ℝ → ℂ`. -/
lemma IsTimeReversalInvariant.map_re_map_ofReal {ρ : SpinDensityC}
    (h : ρ.IsTimeReversalInvariant) : (ρ.mat.map Complex.re).map ((↑) : ℝ → ℂ) = ρ.mat := by
  ext i j
  simp [Complex.ext_iff, (ρ.isTimeReversalInvariant_iff_forall_im_eq_zero.mp h) i j]

/-- The real spin-density matrix of a time-reversal-invariant helicity-amplitude matrix: its
entrywise real part, which is positive semidefinite because the matrix is real. -/
def toSpinDensity (h : ρ.IsTimeReversalInvariant) : SpinDensity where
  mat := ρ.mat.map Complex.re
  posSemidef := (Matrix.posSemidef_map_ofReal_iff (𝕜 := ℂ)).mp (h.map_re_map_ofReal ▸ ρ.posSemidef)

@[simp]
lemma mat_toSpinDensity (h : ρ.IsTimeReversalInvariant) :
    (ρ.toSpinDensity h).mat = ρ.mat.map Complex.re := by
  rfl

/-- `toSpinDensity` is compatible with `f₁`. -/
@[simp]
lemma f1_toSpinDensity (h : ρ.IsTimeReversalInvariant) : PDF.f1 (ρ.toSpinDensity h) = ρ.f1 := by
  simp [PDF.f1_def, f1]

/-- `toSpinDensity` is compatible with `Δq`, which is `g1` for the real `SpinDensity`. -/
@[simp]
lemma g1_toSpinDensity (h : ρ.IsTimeReversalInvariant) :
    PDF.g1 (ρ.toSpinDensity h) = ρ.deltaQ := by
  simp [PDF.g1_def, deltaQ]

/-- `toSpinDensity` is compatible with transversity: the real `h1` is the (real) double-flip
entry. -/
@[simp]
lemma ofReal_h1_toSpinDensity (h : ρ.IsTimeReversalInvariant) :
    (PDF.h1 (ρ.toSpinDensity h) : ℂ) = ρ.transversity :=
  Complex.ext (by simp [PDF.h1_def, transversity_def])
    (by simpa [PDF.h1_def] using h.im_transversity.symm)

end SpinDensityC

namespace SpinDensity

/-- The complex helicity-amplitude matrix of a real spin-density matrix, obtained by the
coercion `ℝ → ℂ`. It is time-reversal invariant (`isTimeReversalInvariant_toSpinDensityC`). -/
def toSpinDensityC (ρ : SpinDensity) : SpinDensityC where
  mat := ρ.mat.map ((↑) : ℝ → ℂ)
  posSemidef := (Matrix.posSemidef_map_ofReal_iff (𝕜 := ℂ)).mpr ρ.posSemidef

variable (ρ : SpinDensity)

@[simp]
lemma mat_toSpinDensityC : ρ.toSpinDensityC.mat = ρ.mat.map ((↑) : ℝ → ℂ) := by
  rfl

/-- The complex matrix of a real spin-density matrix is time-reversal invariant. -/
lemma isTimeReversalInvariant_toSpinDensityC : ρ.toSpinDensityC.IsTimeReversalInvariant := by
  simp [SpinDensityC.isTimeReversalInvariant_iff_forall_im_eq_zero]

@[simp]
lemma f1_toSpinDensityC : ρ.toSpinDensityC.f1 = PDF.f1 ρ := by
  simp [SpinDensityC.f1, PDF.f1_def]

@[simp]
lemma deltaQ_toSpinDensityC : ρ.toSpinDensityC.deltaQ = PDF.g1 ρ := by
  simp [SpinDensityC.deltaQ, PDF.g1_def]

@[simp]
lemma transversity_toSpinDensityC : ρ.toSpinDensityC.transversity = (PDF.h1 ρ : ℂ) := by
  simp [SpinDensityC.transversity_def, PDF.h1_def]

@[simp]
lemma toSpinDensity_toSpinDensityC :
    ρ.toSpinDensityC.toSpinDensity ρ.isTimeReversalInvariant_toSpinDensityC = ρ := by
  ext i j
  simp

end SpinDensity

namespace SpinDensityC

@[simp]
lemma toSpinDensityC_toSpinDensity (ρ : SpinDensityC) (h : ρ.IsTimeReversalInvariant) :
    (ρ.toSpinDensity h).toSpinDensityC = ρ := by
  ext : 1
  exact h.map_re_map_ofReal

/-- **The real spin-density matrix is the time-reversal-invariant complex one.** Taking the real
part and coercing back are inverse bijections between the time-reversal-invariant complex
helicity-amplitude matrices and the real spin-density matrices. -/
@[simps]
def timeReversalInvariantEquiv : {ρ : SpinDensityC // ρ.IsTimeReversalInvariant} ≃ SpinDensity where
  toFun ρ := ρ.1.toSpinDensity ρ.2
  invFun ρ := ⟨ρ.toSpinDensityC, ρ.isTimeReversalInvariant_toSpinDensityC⟩
  left_inv ρ := Subtype.ext (toSpinDensityC_toSpinDensity ρ.1 ρ.2)
  right_inv ρ := ρ.toSpinDensity_toSpinDensityC

/-- **The real spin-density matrix is a proper specialisation.** The rank-one matrix
`v vᴴ` with `v = (1, 0, 0, -i)` is positive semidefinite and its transversity is `i`, so it is
not time-reversal invariant and has no real counterpart. It also saturates the Soffer bound:
`2 ‖h₁‖ = 2 = f₁ + Δq`. -/
theorem exists_not_isTimeReversalInvariant :
    ∃ ρ : SpinDensityC, ¬ ρ.IsTimeReversalInvariant ∧ ρ.transversity = Complex.I ∧
      2 * ‖ρ.transversity‖ = ρ.f1 + ρ.deltaQ := by
  let v : Fin 4 → ℂ := ![1, 0, 0, -Complex.I]
  let ρ : SpinDensityC := ⟨vecMulVec v (star v), posSemidef_vecMulVec_self_star v⟩
  have hI : ρ.transversity = Complex.I := by
    simp [ρ, v, transversity_def, idxPP, idxMM]
  refine ⟨ρ, fun h => ?_, hI, ?_⟩
  · simpa [hI] using h.im_transversity
  · rw [hI, f1_add_deltaQ]
    simp [ρ, v, idxPP, idxMM, vecMulVec_apply]
    norm_num

/-- **Parity does not imply time reversal.** The rank-one matrix `v vᴴ` with
`v = (1, i, i, 1)` is parity invariant, because `v` is unchanged by reversing every helicity, but
its `idxPP, idxPM` entry is `-i`, so it is not time-reversal invariant. Its transversity is `1`,
real as `IsParityInvariant.im_transversity` requires. -/
theorem exists_isParityInvariant_not_isTimeReversalInvariant :
    ∃ ρ : SpinDensityC, ρ.IsParityInvariant ∧ ¬ ρ.IsTimeReversalInvariant ∧
      ρ.transversity = 1 := by
  let v : Fin 4 → ℂ := ![1, Complex.I, Complex.I, 1]
  let ρ : SpinDensityC := ⟨vecMulVec v (star v), posSemidef_vecMulVec_self_star v⟩
  refine ⟨ρ, fun i j => ?_, fun h => ?_, ?_⟩
  · fin_cases i <;> fin_cases j <;> simp [ρ, v, vecMulVec_apply]
  · simpa [ρ, v, idxPP, idxPM, vecMulVec_apply] using
      (ρ.isTimeReversalInvariant_iff_forall_im_eq_zero.mp h) idxPP idxPM
  · simp [ρ, v, transversity_def, idxPP, idxMM]

end SpinDensityC

end PDF
end Parton
end Particles
end EpsilonEridani
