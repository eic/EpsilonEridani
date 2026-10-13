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
(`SpinDensityC.isTimeReversalInvariant_iff_isSymm`). Every helicity-amplitude matrix has a real
part `SpinDensityC.re`, a real `SpinDensity` with the same `f₁` and `Δq` and with the real part of
`h₁`. The real `SpinDensity` is exactly the time-reversal-invariant case: `SpinDensityC.re` and
`SpinDensity.toSpinDensityC` are mutually inverse on it and package into
`SpinDensityC.timeReversalInvariantEquiv`. The specialisation is proper: the rank-one matrix
`SpinDensityC.sofferSaturating` has transversity `i`
(`SpinDensityC.exists_not_isTimeReversalInvariant`).

Parity, `SpinDensityC.IsParityInvariant`, is stated on the entries that angular-momentum
conservation allows in the forward direction, descends to the real part
(`SpinDensityC.IsParityInvariant.re`), and corresponds exactly to the real
`IsParityInvariant` under the specialisation (`SpinDensity.isParityInvariant_toSpinDensityC_iff`).

Positivity of `f₁` and helicity dominance `|Δq| ≤ f₁` (`SpinDensityC.f1_nonneg`,
`SpinDensityC.abs_deltaQ_le_f1`, the real statements applied to the real part) and the Soffer
bound `2 ‖h₁‖ ≤ f₁ + Δq` (`SpinDensityC.soffer_bound`) use positive semidefiniteness and nothing
else: neither parity nor time reversal. The entrywise content of the Soffer bound,
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
lemma coe_re_mat_apply_self (i : Fin 4) : ((ρ.mat i i).re : ℂ) = ρ.mat i i :=
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

/-- `f₁ + Δq` is the sum of the two aligned diagonal entries of the helicity-amplitude matrix.
This is the combination the Soffer bound constrains. -/
lemma f1_add_deltaQ : ρ.f1 + ρ.deltaQ = (ρ.mat idxPP idxPP).re + (ρ.mat idxMM idxMM).re := by
  rw [f1_def, deltaQ_def]; ring

/-- `f₁ - Δq` is the sum of the two anti-aligned diagonal entries of the helicity-amplitude
matrix. -/
lemma f1_sub_deltaQ : ρ.f1 - ρ.deltaQ = (ρ.mat idxPM idxPM).re + (ρ.mat idxMP idxMP).re := by
  rw [f1_def, deltaQ_def]; ring

/-- The real spin-density matrix of a helicity-amplitude matrix: its entrywise real part, which
is positive semidefinite (`Matrix.PosSemidef.map_re`). On time-reversal-invariant matrices it is
the inverse of `SpinDensity.toSpinDensityC` (`timeReversalInvariantEquiv`). -/
def re : SpinDensity where
  mat := ρ.mat.map Complex.re
  posSemidef := ρ.posSemidef.map_re

@[simp]
lemma mat_re : ρ.re.mat = ρ.mat.map Complex.re := rfl

/-- The real part is compatible with `f₁`. -/
@[simp]
lemma f1_re : PDF.f1 ρ.re = ρ.f1 := rfl

/-- The real part is compatible with `Δq`, which is `g1` for the real `SpinDensity`. -/
@[simp]
lemma g1_re : PDF.g1 ρ.re = ρ.deltaQ := rfl

/-- The real part is compatible with transversity: the real `h1` is the real part of the
double-flip entry. -/
@[simp]
lemma h1_re : PDF.h1 ρ.re = ρ.transversity.re := rfl

/-- **Unpolarized positivity.** `f₁` is nonnegative at fixed `(x, Q²)`, from positive
semidefiniteness alone. This is `PDF.f1_nonneg` for the real part. -/
theorem f1_nonneg : 0 ≤ ρ.f1 :=
  ρ.f1_re ▸ PDF.f1_nonneg ρ.re

/-- **Helicity dominance.** `|Δq| ≤ f₁` at fixed `(x, Q²)`, from positive semidefiniteness
alone. This is `PDF.abs_g1_le_f1` for the real part. -/
theorem abs_deltaQ_le_f1 : |ρ.deltaQ| ≤ ρ.f1 :=
  ρ.f1_re ▸ ρ.g1_re ▸ PDF.abs_g1_le_f1 ρ.re

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

/-- Parity invariance of the helicity-amplitude matrix, `A_{Λλ,Λ'λ'} = A_{-Λ-λ,-Λ'-λ'}`, on the
entries that angular-momentum conservation allows in the forward direction: the two aligned
diagonal entries are equal, the two anti-aligned diagonal entries are equal, and the two
double-helicity-flip entries are equal. As for the real `SpinDensity`, this is a hypothesis to be
supplied, not a field, because the Soffer bound does not need it.

On a real matrix the double-flip relation is automatic, and this is the real `IsParityInvariant`
(`SpinDensity.isParityInvariant_toSpinDensityC_iff`). On a complex one it makes transversity
real (`IsParityInvariant.im_transversity`). -/
def IsParityInvariant : Prop :=
  ρ.mat idxMM idxMM = ρ.mat idxPP idxPP ∧ ρ.mat idxMP idxMP = ρ.mat idxPM idxPM ∧
    ρ.mat idxMM idxPP = ρ.mat idxPP idxMM

/-- Under parity invariance the two aligned diagonal entries are equal. -/
lemma IsParityInvariant.mat_idxMM_eq_mat_idxPP {ρ : SpinDensityC} (h : ρ.IsParityInvariant) :
    ρ.mat idxMM idxMM = ρ.mat idxPP idxPP :=
  h.1

/-- Under parity invariance the two anti-aligned diagonal entries are equal. -/
lemma IsParityInvariant.mat_idxMP_eq_mat_idxPM {ρ : SpinDensityC} (h : ρ.IsParityInvariant) :
    ρ.mat idxMP idxMP = ρ.mat idxPM idxPM :=
  h.2.1

/-- Under parity invariance the two double-helicity-flip entries are equal. -/
lemma IsParityInvariant.mat_idxMM_idxPP_eq_mat_idxPP_idxMM {ρ : SpinDensityC}
    (h : ρ.IsParityInvariant) :
    ρ.mat idxMM idxPP = ρ.mat idxPP idxMM :=
  h.2.2

/-- Under parity invariance `f₁` reduces to the single-nucleon-helicity expression
`q_{+/+} + q_{−/+}`. -/
lemma f1_eq_of_parityInvariant (h : ρ.IsParityInvariant) :
    ρ.f1 = (ρ.mat idxPP idxPP).re + (ρ.mat idxPM idxPM).re := by
  rw [f1_def, h.mat_idxMM_eq_mat_idxPP, h.mat_idxMP_eq_mat_idxPM]; ring

/-- Under parity invariance `Δq` reduces to the single-nucleon-helicity expression
`q_{+/+} - q_{−/+}`. -/
lemma deltaQ_eq_of_parityInvariant (h : ρ.IsParityInvariant) :
    ρ.deltaQ = (ρ.mat idxPP idxPP).re - (ρ.mat idxPM idxPM).re := by
  rw [deltaQ_def, h.mat_idxMM_eq_mat_idxPP, h.mat_idxMP_eq_mat_idxPM]; ring

/-- Under parity invariance transversity is real. -/
lemma IsParityInvariant.im_transversity {ρ : SpinDensityC} (h : ρ.IsParityInvariant) :
    ρ.transversity.im = 0 := by
  -- Parity identifies the double-flip entry with its transpose, hermiticity with its conjugate.
  have hconj : conj (ρ.mat idxMM idxPP) = ρ.mat idxPP idxMM := ρ.posSemidef.1.apply idxPP idxMM
  rw [h.mat_idxMM_idxPP_eq_mat_idxPP_idxMM] at hconj
  exact Complex.conj_eq_iff_im.mp hconj

/-- Parity invariance descends to the real part: the two real diagonal equations are the real
parts of the complex ones, with no time-reversal assumption. The converse, from a
parity-invariant real part back to a parity-invariant helicity-amplitude matrix, needs
time-reversal invariance (`isParityInvariant_re_iff`). -/
lemma IsParityInvariant.re {ρ : SpinDensityC} (h : ρ.IsParityInvariant) :
    PDF.IsParityInvariant ρ.re :=
  ⟨congrArg Complex.re h.1, congrArg Complex.re h.2.1⟩

/-! ### Time reversal and the real specialisation -/

/-- Time-reversal invariance of the helicity-amplitude matrix. Time reversal is antiunitary and,
with the standard phase conventions for the helicity states, acts on the forward amplitudes in
the helicity basis by complex conjugation, so invariance says that the matrix equals its entrywise
complex conjugate. Under it the double-flip entry is real
and the matrix is the complex matrix of its real part (`toSpinDensityC_re`). -/
def IsTimeReversalInvariant : Prop :=
  ρ.mat.map (starRingEnd ℂ) = ρ.mat

/-- Time-reversal invariance says exactly that every entry of the matrix is real. -/
lemma isTimeReversalInvariant_iff_forall_im_eq_zero :
    ρ.IsTimeReversalInvariant ↔ ∀ i j, (ρ.mat i j).im = 0 := by
  simp [IsTimeReversalInvariant, ← Matrix.ext_iff, Complex.conj_eq_iff_im]

/-- For the hermitian helicity-amplitude matrix, time-reversal invariance is the same as
symmetry of the matrix. -/
lemma isTimeReversalInvariant_iff_isSymm :
    ρ.IsTimeReversalInvariant ↔ ρ.mat.IsSymm := by
  have hconj : ∀ i j, conj (ρ.mat i j) = ρ.mat j i := fun i j => ρ.posSemidef.1.apply j i
  simp only [IsTimeReversalInvariant, IsSymm, ← Matrix.ext_iff, map_apply, transpose_apply, hconj]

/-- Under time-reversal invariance transversity is real. -/
lemma IsTimeReversalInvariant.im_transversity {ρ : SpinDensityC}
    (h : ρ.IsTimeReversalInvariant) : ρ.transversity.im = 0 :=
  (ρ.isTimeReversalInvariant_iff_forall_im_eq_zero.mp h) idxPP idxMM

/-- A time-reversal-invariant matrix is the image of its real part under `ℝ → ℂ`. -/
lemma IsTimeReversalInvariant.map_re_map_ofReal {ρ : SpinDensityC}
    (h : ρ.IsTimeReversalInvariant) : (ρ.mat.map Complex.re).map ((↑) : ℝ → ℂ) = ρ.mat := by
  ext i j
  simp [Complex.ext_iff, (ρ.isTimeReversalInvariant_iff_forall_im_eq_zero.mp h) i j]

/-- When transversity is real, the real `h1` of the real part is transversity itself.
Transversity is real under time-reversal invariance
(`IsTimeReversalInvariant.im_transversity`) and under parity invariance
(`IsParityInvariant.im_transversity`). -/
lemma ofReal_h1_re {ρ : SpinDensityC} (h : ρ.transversity.im = 0) :
    (PDF.h1 ρ.re : ℂ) = ρ.transversity := by
  rw [h1_re, Complex.ext_iff]
  exact ⟨Complex.ofReal_re _, by simp [h]⟩

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
@[simp]
lemma isTimeReversalInvariant_toSpinDensityC : ρ.toSpinDensityC.IsTimeReversalInvariant := by
  simp [SpinDensityC.isTimeReversalInvariant_iff_forall_im_eq_zero]

@[simp]
lemma f1_toSpinDensityC : ρ.toSpinDensityC.f1 = PDF.f1 ρ := by
  simp [SpinDensityC.f1_def, PDF.f1_def]

@[simp]
lemma deltaQ_toSpinDensityC : ρ.toSpinDensityC.deltaQ = PDF.g1 ρ := by
  simp [SpinDensityC.deltaQ_def, PDF.g1_def]

@[simp]
lemma transversity_toSpinDensityC : ρ.toSpinDensityC.transversity = (PDF.h1 ρ : ℂ) := by
  simp [SpinDensityC.transversity_def, PDF.h1_def]

/-- Parity invariance of a real spin-density matrix is parity invariance of its complex matrix: the
double-flip relation of the complex predicate holds automatically for a real symmetric matrix. -/
@[simp]
lemma isParityInvariant_toSpinDensityC_iff :
    ρ.toSpinDensityC.IsParityInvariant ↔ PDF.IsParityInvariant ρ := by
  have hsym : ρ.mat idxMM idxPP = ρ.mat idxPP idxMM := by
    simpa using ρ.posSemidef.1.apply idxPP idxMM
  simp [SpinDensityC.IsParityInvariant, PDF.IsParityInvariant, hsym]

@[simp]
lemma re_toSpinDensityC : ρ.toSpinDensityC.re = ρ := by
  ext i j
  simp

end SpinDensity

namespace SpinDensityC

/-- A time-reversal-invariant helicity-amplitude matrix is the complex matrix of its real
part. -/
@[simp]
lemma toSpinDensityC_re {ρ : SpinDensityC} (h : ρ.IsTimeReversalInvariant) :
    ρ.re.toSpinDensityC = ρ := by
  ext : 1
  exact h.map_re_map_ofReal

/-- On time-reversal-invariant matrices, taking the real part preserves and reflects parity
invariance. -/
@[simp]
lemma isParityInvariant_re_iff {ρ : SpinDensityC} (h : ρ.IsTimeReversalInvariant) :
    PDF.IsParityInvariant ρ.re ↔ ρ.IsParityInvariant := by
  conv_rhs => rw [← toSpinDensityC_re h]
  exact (SpinDensity.isParityInvariant_toSpinDensityC_iff _).symm

/-- **The real spin-density matrix is the time-reversal-invariant complex one.** Taking the real
part and coercing back are inverse bijections between the time-reversal-invariant complex
helicity-amplitude matrices and the real spin-density matrices. -/
@[simps]
def timeReversalInvariantEquiv : {ρ : SpinDensityC // ρ.IsTimeReversalInvariant} ≃ SpinDensity where
  toFun ρ := ρ.1.re
  invFun ρ := ⟨ρ.toSpinDensityC, ρ.isTimeReversalInvariant_toSpinDensityC⟩
  left_inv ρ := Subtype.ext (toSpinDensityC_re ρ.2)
  right_inv ρ := ρ.re_toSpinDensityC

/-- The rank-one helicity-amplitude matrix `v vᴴ` with `v = (1, 0, 0, -i)`. Its transversity is
`i` (`transversity_sofferSaturating`), so it is not time-reversal invariant
(`not_isTimeReversalInvariant_sofferSaturating`), and it saturates the Soffer bound
(`two_mul_norm_transversity_sofferSaturating`). -/
def sofferSaturating : SpinDensityC :=
  ⟨vecMulVec ![1, 0, 0, -Complex.I] (star ![1, 0, 0, -Complex.I]),
    posSemidef_vecMulVec_self_star _⟩

@[simp]
lemma mat_sofferSaturating :
    sofferSaturating.mat = vecMulVec ![1, 0, 0, -Complex.I] (star ![1, 0, 0, -Complex.I]) :=
  rfl

@[simp]
lemma transversity_sofferSaturating : sofferSaturating.transversity = Complex.I := by
  simp [transversity_def, idxPP, idxMM]

/-- `sofferSaturating` is not time-reversal invariant: its transversity is not real. -/
lemma not_isTimeReversalInvariant_sofferSaturating :
    ¬ sofferSaturating.IsTimeReversalInvariant := fun h => by
  simpa using h.im_transversity

/-- `sofferSaturating` saturates the Soffer bound: `2 ‖h₁‖ = 2 = f₁ + Δq`. -/
lemma two_mul_norm_transversity_sofferSaturating :
    2 * ‖sofferSaturating.transversity‖ = sofferSaturating.f1 + sofferSaturating.deltaQ := by
  rw [transversity_sofferSaturating, f1_add_deltaQ]
  norm_num [idxPP, idxMM, vecMulVec_apply]

/-- **The real spin-density matrix is a proper specialisation.** There is a positive-semidefinite
helicity-amplitude matrix, `sofferSaturating`, that is not time-reversal invariant, so has no real
counterpart, and saturates the Soffer bound. -/
theorem exists_not_isTimeReversalInvariant :
    ∃ ρ : SpinDensityC, ¬ ρ.IsTimeReversalInvariant ∧ ρ.transversity = Complex.I ∧
      2 * ‖ρ.transversity‖ = ρ.f1 + ρ.deltaQ :=
  ⟨sofferSaturating, not_isTimeReversalInvariant_sofferSaturating,
    transversity_sofferSaturating, two_mul_norm_transversity_sofferSaturating⟩

end SpinDensityC

end PDF
end Parton
end Particles
end EpsilonEridani
