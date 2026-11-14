/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.QFT.QCD.EnergyMomentumTensor.GluonPart
public import EpsilonEridani.QFT.QCD.EnergyMomentumTensor.QuarkPart
public import EpsilonEridani.Relativity.CliffordAlgebraExtensions

/-!
# The total symmetric energy-momentum tensor

The symmetric, gauge-invariant (Belinfante) energy-momentum tensor of QCD is the sum
`T_{μν} = T_q{}_{μν} + T_g{}_{μν}` of the quark part
`EpsilonEridani.QFT.QCD.EnergyMomentumTensor.quarkPart` and the gluon part
`EpsilonEridani.QFT.QCD.EnergyMomentumTensor.gluonPart`. This file collects the properties of
the sum that follow pointwise from those of the parts: symmetry, gauge invariance, tensor
transformation, and the classical value of the trace.

The conventions are those of the two parts. The quark field `ψ`, its covariant derivatives
`Dψ`, the Dirac conjugation matrix `β` and the gamma matrices `γ` with a lower index are as in
`EpsilonEridani.QFT.QCD.EnergyMomentumTensor.QuarkPart`. The colour multiplet `F` of field
strengths is as in `EpsilonEridani.QFT.QCD.EnergyMomentumTensor.GluonPart`.

## Main definitions

* `total g β γ ψ Dψ F`: the total tensor `T = T_q + T_g`.

## Main statements

* `isSymm_total`: `T` is symmetric, as an identity and without equations of motion.
* `total_mulVec_gaugeRotate`: `T` is gauge invariant, concretely under a colour rotation of the
  quark field together with an orthogonal rotation of the gluon multiplet
  (`total_mulVec_gaugeRotate_of_mem_unitaryGroup`).
* `total_equivariant`: `T` transforms as a tensor under a transformation preserving `g`.
* `trace_total`: `T^μ{}_μ = Re (ψ‾ i γ^μ D_μ ψ) + (D / 4 - 1) F^a_{αβ} F^{a αβ}` in spacetime
  dimension `D`.
* `trace_total_of_diracEq`: in four dimensions and on solutions of the Dirac equation
  `i γ^μ D_μ ψ = M ψ`, the trace is the classical value `Re (ψ‾ M ψ)`, which is
  `Σ_q m_q ψ‾_q ψ_q` for a mass matrix diagonal in flavour: classically only the quark masses
  break tracelessness. `trace_total_γDown_of_diracEq` is this statement for the
  Dirac-representation gamma matrices acting on the spin index.

## References

* F. J. Belinfante, *Physica* **7** (1940) 449.
* X. Ji, *Phys. Rev. Lett.* **78** (1997) 610, arXiv:hep-ph/9603249.
-/

public section

noncomputable section

namespace EpsilonEridani
namespace QFT
namespace QCD
namespace EnergyMomentumTensor

open Matrix Complex

variable {n m ι : Type*} [Fintype n] [DecidableEq n] [Fintype m] [Fintype ι]

/-- The total symmetric, gauge-invariant energy-momentum tensor `T_{μν} = T_q{}_{μν} + T_g{}_{μν}`
of a quark field `ψ` with covariant derivatives `Dψ` and a colour multiplet `F` of field
strengths, with lower indices. -/
def total (g : Matrix n n ℝ) (β : Matrix m m ℂ) (γ : n → Matrix m m ℂ) (ψ : m → ℂ)
    (Dψ : n → m → ℂ) (F : ι → Matrix n n ℝ) : Matrix n n ℝ :=
  quarkPart β γ ψ Dψ + gluonPart g F

lemma total_def (g : Matrix n n ℝ) (β : Matrix m m ℂ) (γ : n → Matrix m m ℂ) (ψ : m → ℂ)
    (Dψ : n → m → ℂ) (F : ι → Matrix n n ℝ) :
    total g β γ ψ Dψ F = quarkPart β γ ψ Dψ + gluonPart g F := (rfl)

variable {g : Matrix n n ℝ} {β : Matrix m m ℂ} {γ : n → Matrix m m ℂ}

/-- The total energy-momentum tensor is symmetric for a symmetric metric. This is an identity:
it uses no equation of motion. -/
@[simp]
theorem isSymm_total (hg : g.IsSymm) (ψ : m → ℂ) (Dψ : n → m → ℂ) (F : ι → Matrix n n ℝ) :
    (total g β γ ψ Dψ F).IsSymm :=
  (isSymm_quarkPart β γ ψ Dψ).add (isSymm_gluonPart hg F)

/-- The total energy-momentum tensor is gauge invariant: it is unchanged when the quark field
and its covariant derivatives are transformed by a `U` preserving the bilinears `ψ‾ γ_μ χ` and
the gluon multiplet is rotated by an orthogonal `R`. -/
theorem total_mulVec_gaugeRotate [DecidableEq ι] {U : Matrix m m ℂ}
    (hU : ∀ μ, Uᴴ * (β * γ μ) * U = β * γ μ) {R : Matrix ι ι ℝ} (hR : R ∈ orthogonalGroup ι ℝ)
    (ψ : m → ℂ) (Dψ : n → m → ℂ) (F : ι → Matrix n n ℝ) :
    total g β γ (U *ᵥ ψ) (fun ν => U *ᵥ Dψ ν) (gaugeRotate R F) = total g β γ ψ Dψ F := by
  rw [total_def, total_def, quarkPart_mulVec hU, gluonPart_gaugeRotate g hR]

/-- The total energy-momentum tensor is invariant under a colour rotation: a unitary `U`
commuting with each `β * γ μ` (for instance, commuting with `β` and with the gamma matrices),
acting on the quark field and its covariant derivatives, together with an orthogonal rotation of
the gluon multiplet. -/
theorem total_mulVec_gaugeRotate_of_mem_unitaryGroup [DecidableEq ι] [DecidableEq m]
    {U : Matrix m m ℂ} (hU : U ∈ unitaryGroup m ℂ) (h : ∀ μ, Commute U (β * γ μ))
    {R : Matrix ι ι ℝ} (hR : R ∈ orthogonalGroup ι ℝ) (ψ : m → ℂ) (Dψ : n → m → ℂ)
    (F : ι → Matrix n n ℝ) :
    total g β γ (U *ᵥ ψ) (fun ν => U *ᵥ Dψ ν) (gaugeRotate R F) = total g β γ ψ Dψ F :=
  total_mulVec_gaugeRotate (fun μ => (commute_unitary_iff_star_left_conjugate hU).mp (h μ)) hR
    ψ Dψ F

/-- The total energy-momentum tensor transforms as a tensor with two lower indices under a
transformation `Λ` preserving the metric, when the quark field transforms by an `S` under which
the bilinears `ψ‾ γ_μ χ` transform as a vector. -/
theorem total_equivariant {Λ : Matrix n n ℝ} (hΛ : Λᵀ * g * Λ = g) {S : Matrix m m ℂ}
    (hS : ∀ μ, Sᴴ * (β * γ μ) * S = ∑ α, (Λ α μ : ℂ) • (β * γ α)) (ψ : m → ℂ)
    (Dψ : n → m → ℂ) (F : ι → Matrix n n ℝ) :
    total g β γ (S *ᵥ ψ) (fun ν => ∑ α, (Λ α ν : ℂ) • S *ᵥ Dψ α) (fun a => Λᵀ * F a * Λ) =
      Λᵀ * total g β γ ψ Dψ F * Λ := by
  rw [total_def, total_def, quarkPart_equivariant hS, gluonPart_equivariant hΛ, Matrix.mul_add,
    Matrix.add_mul]

/-- The trace `T^μ{}_μ = Re (ψ‾ i γ^μ D_μ ψ) + (D / 4 - 1) F^a_{αβ} F^{a αβ}` of the total
energy-momentum tensor in spacetime dimension `D = card n`. -/
theorem trace_total (hg : g.IsSymm) (hγ : ∀ μ, (β * γ μ).IsHermitian) (ψ : m → ℂ)
    (Dψ : n → m → ℂ) (F : ι → Matrix n n ℝ) :
    trace (g⁻¹ * total g β γ ψ Dψ F) =
      (star ψ ⬝ᵥ β *ᵥ diracOpApply g γ Dψ).re + (Fintype.card n / 4 - 1) * gluonFieldSq g F := by
  rw [total_def, Matrix.mul_add, trace_add, trace_quarkPart hg hγ, trace_gluonPart]

/-- In four spacetime dimensions and on solutions of the Dirac equation `i γ^μ D_μ ψ = M ψ`, the
trace of the total energy-momentum tensor is the classical value `Re (ψ‾ M ψ)`, that is
`Σ_q m_q ψ‾_q ψ_q` for a mass matrix diagonal in flavour: the gluon part is traceless and the
quark part contributes only through the masses. -/
theorem trace_total_of_diracEq (hn : Fintype.card n = 4) (hg : g.IsSymm)
    (hγ : ∀ μ, (β * γ μ).IsHermitian) {M : Matrix m m ℂ} {ψ : m → ℂ} {Dψ : n → m → ℂ}
    (h : diracOpApply g γ Dψ = M *ᵥ ψ) (F : ι → Matrix n n ℝ) :
    trace (g⁻¹ * total g β γ ψ Dψ F) = (star ψ ⬝ᵥ (β * M) *ᵥ ψ).re := by
  rw [total_def, Matrix.mul_add, trace_add, trace_quarkPart_of_diracEq hg hγ h, trace_gluonPart,
    hn]
  norm_num

/-- `trace_total_of_diracEq` for the Dirac-representation gamma matrices `β = γ⁰` and
`γ_μ = spaceTime.γDown μ` acting on the spin index of a single quark, whose Hermiticity hypothesis
is `spaceTime.isHermitian_γ0_mul_γDown`. The spacetime index is the `Fin 4` of `spaceTime.γDown`;
the statement holds for every symmetric metric `g` on it, and `diracOpApply g` is `i γ^μ D_μ ψ`
for the Minkowski metric `minkowskiMatrix.submatrix finSumFinEquiv.symm finSumFinEquiv.symm`
that lowers `spaceTime.γDown`. -/
theorem trace_total_γDown_of_diracEq {g : Matrix (Fin 4) (Fin 4) ℝ} (hg : g.IsSymm)
    {M : Matrix (Fin 4) (Fin 4) ℂ} {ψ : Fin 4 → ℂ} {Dψ : Fin 4 → Fin 4 → ℂ}
    (h : diracOpApply g spaceTime.γDown Dψ = M *ᵥ ψ) (F : ι → Matrix (Fin 4) (Fin 4) ℝ) :
    trace (g⁻¹ * total g spaceTime.γ0 spaceTime.γDown ψ Dψ F) =
      (star ψ ⬝ᵥ (spaceTime.γ0 * M) *ᵥ ψ).re :=
  trace_total_of_diracEq (Fintype.card_fin 4) hg spaceTime.isHermitian_γ0_mul_γDown h F

end EnergyMomentumTensor
end QCD
end QFT
end EpsilonEridani
