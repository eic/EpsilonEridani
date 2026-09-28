/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import EpsilonEridani.QFT.QCD.SU2Generators
public import EpsilonEridani.QFT.QCD.SUNStructureConstants
/-!

# Genuine `su(3)` normalized generator data

The `su(2)` package of `EpsilonEridani.QFT.QCD.SU2Generators` is repeated here for `su(3)`,
the colour algebra of QCD: generators `Tᵃ = λᵃ / 2` built from the Gell-Mann matrices,
structure constants `f^{abc}` given by the standard table, and invariants
`T_F = 1/2`, `C_F = 4/3`, `C_A = 3`.

Mathlib at this pin has no Gell-Mann matrices, so they are defined here.  Everything
about the eighth generator is controlled by `invSqrt3 = 1/√3`; it is kept opaque and
handled through `invSqrt3_mul_self` rather than unfolded, so that the case sweeps stay
arithmetic in `ℂ`.

All three identities are proved here: trace normalization (`su3TraceStatement`,
`T_F = 1/2`), the fundamental Casimir (`su3FundamentalStatement`, `C_F = 4/3`) and the
adjoint Casimir (`su3AdjointStatement`, `C_A = 3`).  `su3NormalizedData` therefore
instantiates every contract field of `NormalizedGeneratorData` with the corresponding
identity rather than with a placeholder, and `su3CasimirDerivationAssumptions` carries
the full derivation package with identity bridges.

The adjoint Casimir is a sum of 4096 products of table entries, and `simp` cannot
evaluate `structConst3` at that scale: the fallback arm of its match carries one side
condition per explicit arm.  It is therefore checked in integer arithmetic instead.
Every entry has the form `(p + q √3) / 2` with `p q : ℤ`; `code3` records the entries
as a computable table, agreeing with `structConst3` definitionally
(`structConst3_eq_val`), and the two resulting integer sums are checked by kernel
evaluation (`code3_sum_identity`), which adds no axioms.

-/

@[expose] public section

noncomputable section

namespace EpsilonEridani
namespace QFT
namespace QCD
namespace RepresentationColor

open Matrix Complex

/-! ### The irrational normalization of the eighth generator -/

/-- `√3`, the normalization appearing in the eighth Gell-Mann matrix and in the
structure constants `f^{458} = f^{678} = √3/2`. -/
def rt3 : ℝ := Real.sqrt 3

lemma rt3_mul_self : rt3 * rt3 = 3 :=
  Real.mul_self_sqrt (by norm_num)

lemma rt3_sq : rt3 ^ 2 = 3 := by
  rw [sq, rt3_mul_self]

/-- `1/√3`, as a complex number.  Deliberately opaque: the proofs below never unfold
it, they only use `invSqrt3_mul_self`. -/
def invSqrt3 : ℂ := ((rt3⁻¹ : ℝ) : ℂ)

lemma invSqrt3_mul_self : invSqrt3 * invSqrt3 = (3 : ℂ)⁻¹ := by
  rw [invSqrt3, ← Complex.ofReal_mul, ← mul_inv, rt3_mul_self]
  norm_num

lemma invSqrt3_sq : invSqrt3 ^ 2 = (3 : ℂ)⁻¹ := by
  rw [sq, invSqrt3_mul_self]

/-! ### Data -/

/-- The Gell-Mann matrices `λ¹, …, λ⁸`, indexed by `Fin 8` (so `gellMann3 0 = λ¹`). -/
def gellMann3 : Fin 8 → Matrix (Fin 3) (Fin 3) ℂ
  | 0 => !![0, 1, 0; 1, 0, 0; 0, 0, 0]
  | 1 => !![0, -I, 0; I, 0, 0; 0, 0, 0]
  | 2 => !![1, 0, 0; 0, -1, 0; 0, 0, 0]
  | 3 => !![0, 0, 1; 0, 0, 0; 1, 0, 0]
  | 4 => !![0, 0, -I; 0, 0, 0; I, 0, 0]
  | 5 => !![0, 0, 0; 0, 0, 1; 0, 1, 0]
  | 6 => !![0, 0, 0; 0, 0, -I; 0, I, 0]
  | 7 => !![invSqrt3, 0, 0; 0, invSqrt3, 0; 0, 0, -2 * invSqrt3]

/-- Matrix entries of the fundamental `su(3)` generators `Tᵃ = λᵃ / 2`. -/
def su3GenEntry (a : Fin 8) (i j : Fin 3) : ℂ :=
  (1 / 2 : ℂ) * gellMann3 a i j

/-- The `su(3)` structure constants `f^{abc}`, indexed by `Fin 8` (so the entry
`0, 1, 2` is the standard `f^{123} = 1`).  Totally antisymmetric; the nonzero
independent values are `f^{123} = 1`, `f^{147} = f^{246} = f^{257} = f^{345} = 1/2`,
`f^{156} = f^{367} = -1/2` and `f^{458} = f^{678} = √3/2`. -/
def structConst3 : Fin 8 → Fin 8 → Fin 8 → ℝ
  | 0, 1, 2 => 1
  | 0, 2, 1 => -1
  | 0, 3, 6 => 1 / 2
  | 0, 4, 5 => -(1 / 2)
  | 0, 5, 4 => 1 / 2
  | 0, 6, 3 => -(1 / 2)
  | 1, 0, 2 => -1
  | 1, 2, 0 => 1
  | 1, 3, 5 => 1 / 2
  | 1, 4, 6 => 1 / 2
  | 1, 5, 3 => -(1 / 2)
  | 1, 6, 4 => -(1 / 2)
  | 2, 0, 1 => 1
  | 2, 1, 0 => -1
  | 2, 3, 4 => 1 / 2
  | 2, 4, 3 => -(1 / 2)
  | 2, 5, 6 => -(1 / 2)
  | 2, 6, 5 => 1 / 2
  | 3, 0, 6 => -(1 / 2)
  | 3, 1, 5 => -(1 / 2)
  | 3, 2, 4 => -(1 / 2)
  | 3, 4, 2 => 1 / 2
  | 3, 4, 7 => rt3 / 2
  | 3, 5, 1 => 1 / 2
  | 3, 6, 0 => 1 / 2
  | 3, 7, 4 => -(rt3 / 2)
  | 4, 0, 5 => 1 / 2
  | 4, 1, 6 => -(1 / 2)
  | 4, 2, 3 => 1 / 2
  | 4, 3, 2 => -(1 / 2)
  | 4, 3, 7 => -(rt3 / 2)
  | 4, 5, 0 => -(1 / 2)
  | 4, 6, 1 => 1 / 2
  | 4, 7, 3 => rt3 / 2
  | 5, 0, 4 => -(1 / 2)
  | 5, 1, 3 => 1 / 2
  | 5, 2, 6 => 1 / 2
  | 5, 3, 1 => -(1 / 2)
  | 5, 4, 0 => 1 / 2
  | 5, 6, 2 => -(1 / 2)
  | 5, 6, 7 => rt3 / 2
  | 5, 7, 6 => -(rt3 / 2)
  | 6, 0, 3 => 1 / 2
  | 6, 1, 4 => 1 / 2
  | 6, 2, 5 => -(1 / 2)
  | 6, 3, 0 => -(1 / 2)
  | 6, 4, 1 => -(1 / 2)
  | 6, 5, 2 => 1 / 2
  | 6, 5, 7 => -(rt3 / 2)
  | 6, 7, 5 => rt3 / 2
  | 7, 3, 4 => rt3 / 2
  | 7, 4, 3 => -(rt3 / 2)
  | 7, 5, 6 => rt3 / 2
  | 7, 6, 5 => -(rt3 / 2)
  | _, _, _ => 0

/-- Kronecker delta on the adjoint index set of `su(3)`. -/
def su3DeltaAdj (a b : Fin 8) : ℝ := if a = b then 1 else 0

/-- Kronecker delta on the fundamental index set of `su(3)`. -/
def su3DeltaFund (i j : Fin 3) : ℝ := if i = j then 1 else 0

/-! ### The three identities, stated concretely -/

/-- Trace normalization for `su(3)`: `Σᵢⱼ (Tᵃ)ᵢⱼ (Tᵇ)ⱼᵢ = (1/2) δᵃᵇ`. -/
def SU3TraceStatement : Prop :=
  ∀ a b : Fin 8,
    (∑ i : Fin 3, ∑ j : Fin 3, su3GenEntry a i j * su3GenEntry b j i)
      = ((1 / 2 : ℝ) : ℂ) * ((su3DeltaAdj a b : ℝ) : ℂ)

/-- Fundamental Casimir for `su(3)`: `Σₐ Σₖ (Tᵃ)ᵢₖ (Tᵃ)ₖⱼ = (4/3) δᵢⱼ`. -/
def SU3FundamentalStatement : Prop :=
  ∀ i j : Fin 3,
    (∑ a : Fin 8, ∑ k : Fin 3, su3GenEntry a i k * su3GenEntry a k j)
      = ((4 / 3 : ℝ) : ℂ) * ((su3DeltaFund i j : ℝ) : ℂ)

/-- Adjoint Casimir for `su(3)`: `Σ_{cd} f^{acd} f^{bcd} = 3 δᵃᵇ`. -/
def SU3AdjointStatement : Prop :=
  ∀ a b : Fin 8,
    (∑ c : Fin 8, ∑ d : Fin 8, structConst3 a c d * structConst3 b c d)
      = (3 : ℝ) * su3DeltaAdj a b

/-! ### Proofs of the identities -/

/-- A double index sum of the form appearing in `SU3TraceStatement` is a matrix trace. -/
private lemma sum_mul_eq_trace (M N : Matrix (Fin 3) (Fin 3) ℂ) :
    (∑ i : Fin 3, ∑ j : Fin 3, M i j * N j i) = Matrix.trace (M * N) := by
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply]

/-- The fundamental `su(3)` generators `λᵃ/2` are trace-normalized with `T_F = 1/2`.

Routed through `Matrix.trace` and `Matrix.trace_fin_three` rather than a generic
`Finset.sum` unfolding: the latter no longer finishes within the default heartbeat budget
over all 64 cases. -/
lemma su3TraceStatement : SU3TraceStatement := by
  intro a b
  have h : (∑ i : Fin 3, ∑ j : Fin 3, su3GenEntry a i j * su3GenEntry b j i)
      = (1 / 4 : ℂ) * Matrix.trace (gellMann3 a * gellMann3 b) := by
    simp only [su3GenEntry, ← sum_mul_eq_trace]
    rw [Finset.mul_sum]
    congr 1
    ext i
    rw [Finset.mul_sum]
    congr 1
    ext j
    ring
  rw [h]
  fin_cases a <;> fin_cases b <;>
    simp [gellMann3, Matrix.trace_fin_three, su3DeltaAdj]
  all_goals ring_nf
  all_goals simp [invSqrt3_sq]
  all_goals ring_nf

/-- The fundamental `su(3)` Casimir: `Σₐ (λᵃ/2)(λᵃ/2) = (4/3) · 1`. -/
lemma su3FundamentalStatement : SU3FundamentalStatement := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [su3GenEntry, su3DeltaFund, gellMann3, Fin.sum_univ_three, Fin.sum_univ_eight] <;>
    ring_nf <;>
    simp [invSqrt3_sq, Complex.I_sq] <;>
    ring_nf

/-- The seven values taken by `structConst3`, as a computable code. -/
private inductive StructConstCode
  | zero | one | negOne | half | negHalf | rt3Half | negRt3Half

/-- The real value of a structure-constant code; each arm is the literal used in
`structConst3`, so that `structConst3_eq_val` holds by `rfl`. -/
private def StructConstCode.val : StructConstCode → ℝ
  | .zero => 0
  | .one => 1
  | .negOne => -1
  | .half => 1 / 2
  | .negHalf => -(1 / 2)
  | .rt3Half => rt3 / 2
  | .negRt3Half => -(rt3 / 2)

/-- The rational part `p` of a code whose value is `(p + q √3) / 2`. -/
private def StructConstCode.p : StructConstCode → ℤ
  | .one => 2 | .negOne => -2 | .half => 1 | .negHalf => -1 | _ => 0

/-- The irrational part `q` of a code whose value is `(p + q √3) / 2`. -/
private def StructConstCode.q : StructConstCode → ℤ
  | .rt3Half => 1 | .negRt3Half => -1 | _ => 0

private lemma StructConstCode.val_eq (k : StructConstCode) :
    k.val = ((k.p : ℝ) + (k.q : ℝ) * rt3) / 2 := by
  cases k <;> simp [StructConstCode.val, StructConstCode.p, StructConstCode.q] <;> ring

/-- `structConst3` as a computable table of codes, arm for arm. -/
private def code3 : Fin 8 → Fin 8 → Fin 8 → StructConstCode
  | 0, 1, 2 => .one
  | 0, 2, 1 => .negOne
  | 0, 3, 6 => .half
  | 0, 4, 5 => .negHalf
  | 0, 5, 4 => .half
  | 0, 6, 3 => .negHalf
  | 1, 0, 2 => .negOne
  | 1, 2, 0 => .one
  | 1, 3, 5 => .half
  | 1, 4, 6 => .half
  | 1, 5, 3 => .negHalf
  | 1, 6, 4 => .negHalf
  | 2, 0, 1 => .one
  | 2, 1, 0 => .negOne
  | 2, 3, 4 => .half
  | 2, 4, 3 => .negHalf
  | 2, 5, 6 => .negHalf
  | 2, 6, 5 => .half
  | 3, 0, 6 => .negHalf
  | 3, 1, 5 => .negHalf
  | 3, 2, 4 => .negHalf
  | 3, 4, 2 => .half
  | 3, 4, 7 => .rt3Half
  | 3, 5, 1 => .half
  | 3, 6, 0 => .half
  | 3, 7, 4 => .negRt3Half
  | 4, 0, 5 => .half
  | 4, 1, 6 => .negHalf
  | 4, 2, 3 => .half
  | 4, 3, 2 => .negHalf
  | 4, 3, 7 => .negRt3Half
  | 4, 5, 0 => .negHalf
  | 4, 6, 1 => .half
  | 4, 7, 3 => .rt3Half
  | 5, 0, 4 => .negHalf
  | 5, 1, 3 => .half
  | 5, 2, 6 => .half
  | 5, 3, 1 => .negHalf
  | 5, 4, 0 => .half
  | 5, 6, 2 => .negHalf
  | 5, 6, 7 => .rt3Half
  | 5, 7, 6 => .negRt3Half
  | 6, 0, 3 => .half
  | 6, 1, 4 => .half
  | 6, 2, 5 => .negHalf
  | 6, 3, 0 => .negHalf
  | 6, 4, 1 => .negHalf
  | 6, 5, 2 => .half
  | 6, 5, 7 => .negRt3Half
  | 6, 7, 5 => .rt3Half
  | 7, 3, 4 => .rt3Half
  | 7, 4, 3 => .negRt3Half
  | 7, 5, 6 => .rt3Half
  | 7, 6, 5 => .negRt3Half
  | _, _, _ => .zero

private lemma structConst3_eq_val (a b c : Fin 8) :
    structConst3 a b c = (code3 a b c).val := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> rfl

/-- The adjoint Casimir in integer arithmetic: writing each entry as `(p + q √3) / 2`, the
rational and `√3` parts of `Σ_{cd} f^{acd} f^{bcd}` are `12 δᵃᵇ / 4` and `0`. -/
private lemma code3_sum_identity (a b : Fin 8) :
    (∑ c : Fin 8, ∑ d : Fin 8,
        ((code3 a c d).p * (code3 b c d).p + 3 * ((code3 a c d).q * (code3 b c d).q)))
      = (if a = b then 12 else 0) ∧
    (∑ c : Fin 8, ∑ d : Fin 8,
        ((code3 a c d).p * (code3 b c d).q + (code3 a c d).q * (code3 b c d).p)) = 0 := by
  revert a b
  decide +kernel

/-- The `su(3)` adjoint Casimir: `Σ_{cd} f^{acd} f^{bcd} = 3 δᵃᵇ`, so `C_A = 3`. -/
lemma su3AdjointStatement : SU3AdjointStatement := by
  intro a b
  obtain ⟨hP, hQ⟩ := code3_sum_identity a b
  have hterm : ∀ c d : Fin 8, structConst3 a c d * structConst3 b c d
      = (((code3 a c d).p * (code3 b c d).p + 3 * ((code3 a c d).q * (code3 b c d).q) : ℤ)
          + (((code3 a c d).p * (code3 b c d).q + (code3 a c d).q * (code3 b c d).p : ℤ)
            : ℝ) * rt3) / 4 := by
    intro c d
    rw [structConst3_eq_val, structConst3_eq_val, StructConstCode.val_eq,
      StructConstCode.val_eq]
    push_cast
    linear_combination ((code3 a c d).q * (code3 b c d).q / 4 : ℝ) * rt3_mul_self
  have hP' := congrArg (Int.cast : ℤ → ℝ) hP
  have hQ' := congrArg (Int.cast : ℤ → ℝ) hQ
  simp_rw [hterm, ← Finset.sum_div, Finset.sum_add_distrib, ← Finset.sum_mul]
  push_cast at hP' hQ' ⊢
  rw [hP', hQ']
  split_ifs with h <;> norm_num [su3DeltaAdj, h]

/-! ### The genuine `su(3)` package -/

/-- Genuine normalized generator data for `su(3)`: Gell-Mann generators `λᵃ/2`, the
standard structure constants, and `T_F = 1/2`, `C_F = 4/3`, `C_A = 3`.  Every contract
field is instantiated with the corresponding concrete identity, and every witness is a
proof of that identity — no placeholders. -/
def su3NormalizedData : NormalizedGeneratorData where
  AdjIndex := Fin 8
  FundIndex := Fin 3
  adjFintype := inferInstance
  fundFintype := inferInstance
  genEntry := su3GenEntry
  structConst := structConst3
  deltaAdj := su3DeltaAdj
  deltaFund := su3DeltaFund
  tF := 1 / 2
  cF := 4 / 3
  cA := 3
  traceNormalization := SU3TraceStatement
  hTraceNormalization := su3TraceStatement
  fundamentalCasimir := SU3FundamentalStatement
  hFundamentalCasimir := su3FundamentalStatement
  adjointCasimir := SU3AdjointStatement
  hAdjointCasimir := su3AdjointStatement

/-- `su(3)` satisfies the trace-normalization identity of `NormalizedGeneratorData`. -/
lemma su3NormalizedData_traceIdentity : su3NormalizedData.TraceIdentity :=
  su3TraceStatement

/-- `su(3)` satisfies the fundamental Casimir identity of `NormalizedGeneratorData`. -/
lemma su3NormalizedData_fundamentalIdentity :
    su3NormalizedData.FundamentalCasimirIdentity :=
  su3FundamentalStatement

/-- `su(3)` satisfies the adjoint Casimir identity of `NormalizedGeneratorData`. -/
lemma su3NormalizedData_adjointIdentity : su3NormalizedData.AdjointCasimirIdentity :=
  su3AdjointStatement

/-- The `su(3)` sector carries a full derivation package: all three
representation-level identities are proved, not assumed, and the contract bridges are
the identity map because the contracts *are* the identities. -/
def su3CasimirDerivationAssumptions :
    CasimirDerivationAssumptions su3NormalizedData where
  hTraceIdentity := su3NormalizedData_traceIdentity
  hFundamentalIdentity := su3NormalizedData_fundamentalIdentity
  hAdjointIdentity := su3NormalizedData_adjointIdentity
  traceImpliesContract := fun h => h
  fundamentalImpliesContract := fun h => h
  adjointImpliesContract := fun h => h

/-- The colour invariants of the genuine `su(3)` package are the standard QCD ones. -/
lemma su3NormalizedData_colorInvariants :
    colorInvariantsOf su3NormalizedData = { cF := 4 / 3, cA := 3, tF := 1 / 2 } := by
  rfl

end RepresentationColor
end QCD
end QFT
end EpsilonEridani
