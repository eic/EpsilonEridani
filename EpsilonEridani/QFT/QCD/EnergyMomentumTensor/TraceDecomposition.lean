/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.Mathematics.LinearAlgebra.Matrix.MetricTrace
public import EpsilonEridani.QFT.QCD.EnergyMomentumTensor.Total

/-!
# The trace and traceless parts of the energy-momentum tensor of QCD

The symmetric energy-momentum tensor `T = T_q + T_g` of QCD
(`EpsilonEridani.QFT.QCD.EnergyMomentumTensor.total`) splits, with respect to the metric `g`,
into its trace part `(1/D) g_{μν} T^α{}_α` and its traceless part (`Matrix.tracePart`,
`Matrix.tracelessPart`). The traceless parts of the quark and gluon tensors are the twist-two
operators whose forward matrix elements give the quark and gluon momentum fractions, while the
trace part carries the quark masses and, beyond the classical theory, the trace anomaly.

Both projections are linear, so they commute with the quark-gluon split: the trace (traceless)
part of the total is the sum of the trace (traceless) parts of the quark and gluon parts. This
file records that, together with the classical values of the parts. In four dimensions the
gluon part is traceless, so it is its own traceless part; on solutions of the Dirac equation
`i γ^μ D_μ ψ = M ψ` the trace part of the quark part is `(1/D) g_{μν} Re (ψ‾ M ψ)`. Hence, in
four dimensions and on shell, the trace part of the total tensor is `(1/4) g_{μν} Re (ψ‾ M ψ)`,
the classical mass term, and the traceless part of the total is the traceless part of the quark
part plus the whole gluon part.

## Main statements

* `tracePart_total`, `tracelessPart_total`: the projections commute with the quark-gluon split.
* `tracePart_gluonPart`, `tracelessPart_gluonPart`: the trace part
  `(D / 4 - 1) / D · g_{μν} F^a_{αβ} F^{a αβ}` of the gluon part in dimension `D`, and the
  remaining traceless part. The trace part vanishes in four dimensions or when
  `F^a_{αβ} F^{a αβ} = 0` (`tracePart_gluonPart_eq_zero`), so that the gluon part is then its own
  traceless part (`tracelessPart_gluonPart_eq_self`).
* `tracePart_quarkPart`, `tracelessPart_quarkPart`: the trace part
  `(1/D) g_{μν} Re (ψ‾ i γ^α D_α ψ)` of the quark part and the remaining traceless part. The trace
  part on solutions of the Dirac equation is `(1/D) g_{μν} Re (ψ‾ M ψ)`
  (`tracePart_quarkPart_of_diracEq`); the traceless part of the quark part is then the quark part
  minus this (`tracelessPart_quarkPart_of_diracEq`).
* `tracePart_total_of_diracEq` and `tracelessPart_total_of_trace_gluonPart_eq_zero`: the trace
  part of the total in four dimensions is the classical mass term, and, whenever the gluon part is
  traceless, the traceless part of the total is the traceless part of the quark part plus the
  gluon part.

## References

* X. Ji, *Phys. Rev. Lett.* **74** (1995) 1071, arXiv:hep-ph/9410274.
* X. Ji, *Phys. Rev. D* **52** (1995) 271, arXiv:hep-ph/9502213.
-/

public section

noncomputable section

namespace EpsilonEridani
namespace QFT
namespace QCD
namespace EnergyMomentumTensor

open Matrix Complex

variable {n m ι : Type*} [Fintype n] [DecidableEq n] [Fintype m] [Fintype ι]
  {g : Matrix n n ℝ} {β : Matrix m m ℂ} {γ : n → Matrix m m ℂ}

/-- The trace part of the total energy-momentum tensor is the sum of the trace parts of its quark
and gluon parts. -/
theorem tracePart_total (ψ : m → ℂ) (Dψ : n → m → ℂ) (F : ι → Matrix n n ℝ) :
    tracePart g (total g β γ ψ Dψ F) =
      tracePart g (quarkPart β γ ψ Dψ) + tracePart g (gluonPart g F) := by
  rw [total_def, map_add]

/-- The traceless part of the total energy-momentum tensor is the sum of the traceless parts of
its quark and gluon parts. -/
theorem tracelessPart_total (ψ : m → ℂ) (Dψ : n → m → ℂ) (F : ι → Matrix n n ℝ) :
    tracelessPart g (total g β γ ψ Dψ F) =
      tracelessPart g (quarkPart β γ ψ Dψ) + tracelessPart g (gluonPart g F) := by
  rw [total_def, map_add]

/-- The trace part `(D / 4 - 1) / D · g_{μν} F^a_{αβ} F^{a αβ}` of the gluon part in spacetime
dimension `D = card n`. -/
theorem tracePart_gluonPart (g : Matrix n n ℝ) (F : ι → Matrix n n ℝ) :
    tracePart g (gluonPart g F) =
      ((Fintype.card n / 4 - 1) * gluonFieldSq g F / Fintype.card n) • g := by
  rw [tracePart_apply, trace_gluonPart]

/-- The traceless part `T^g_{μν} - (D / 4 - 1) / D · g_{μν} F^a_{αβ} F^{a αβ}` of the gluon part in
spacetime dimension `D = card n`. -/
theorem tracelessPart_gluonPart (g : Matrix n n ℝ) (F : ι → Matrix n n ℝ) :
    tracelessPart g (gluonPart g F) =
      gluonPart g F - ((Fintype.card n / 4 - 1) * gluonFieldSq g F / Fintype.card n) • g := by
  rw [tracelessPart_apply, tracePart_gluonPart]

/-- The gluon part has no trace part in four spacetime dimensions, or when
`F^a_{αβ} F^{a αβ} = 0`. -/
theorem tracePart_gluonPart_eq_zero (g : Matrix n n ℝ) {F : ι → Matrix n n ℝ}
    (h : Fintype.card n = 4 ∨ gluonFieldSq g F = 0) : tracePart g (gluonPart g F) = 0 := by
  rw [tracePart_apply, (trace_gluonPart_eq_zero_iff g F).2 h, zero_div, zero_smul]

/-- The gluon part is its own traceless part in four spacetime dimensions, or when
`F^a_{αβ} F^{a αβ} = 0`. -/
theorem tracelessPart_gluonPart_eq_self (g : Matrix n n ℝ) {F : ι → Matrix n n ℝ}
    (h : Fintype.card n = 4 ∨ gluonFieldSq g F = 0) :
    tracelessPart g (gluonPart g F) = gluonPart g F := by
  rw [tracelessPart_apply, tracePart_gluonPart_eq_zero g h, sub_zero]

/-- The trace part `(1/D) g_{μν} Re (ψ‾ i γ^α D_α ψ)` of the quark part in spacetime dimension
`D = card n`. -/
theorem tracePart_quarkPart (hg : g.IsSymm) (hγ : ∀ μ, (β * γ μ).IsHermitian) (ψ : m → ℂ)
    (Dψ : n → m → ℂ) :
    tracePart g (quarkPart β γ ψ Dψ) =
      ((star ψ ⬝ᵥ β *ᵥ diracOpApply g γ Dψ).re / Fintype.card n) • g := by
  rw [tracePart_apply, trace_quarkPart hg hγ]

/-- The traceless part `T^q_{μν} - (1/D) g_{μν} Re (ψ‾ i γ^α D_α ψ)` of the quark part in spacetime
dimension `D = card n`. -/
theorem tracelessPart_quarkPart (hg : g.IsSymm) (hγ : ∀ μ, (β * γ μ).IsHermitian) (ψ : m → ℂ)
    (Dψ : n → m → ℂ) :
    tracelessPart g (quarkPart β γ ψ Dψ) =
      quarkPart β γ ψ Dψ - ((star ψ ⬝ᵥ β *ᵥ diracOpApply g γ Dψ).re / Fintype.card n) • g := by
  rw [tracelessPart_apply, tracePart_quarkPart hg hγ]

/-- On solutions of the Dirac equation `i γ^μ D_μ ψ = M ψ`, the trace part of the quark part is
`(1/D) g_{μν} Re (ψ‾ M ψ)` in spacetime dimension `D = card n`. -/
theorem tracePart_quarkPart_of_diracEq (hg : g.IsSymm) (hγ : ∀ μ, (β * γ μ).IsHermitian)
    {M : Matrix m m ℂ} {ψ : m → ℂ} {Dψ : n → m → ℂ} (h : diracOpApply g γ Dψ = M *ᵥ ψ) :
    tracePart g (quarkPart β γ ψ Dψ) =
      ((star ψ ⬝ᵥ (β * M) *ᵥ ψ).re / Fintype.card n) • g := by
  rw [tracePart_apply, trace_quarkPart_of_diracEq hg hγ h]

/-- On solutions of the Dirac equation `i γ^μ D_μ ψ = M ψ`, the traceless part of the quark part
is `T^q_{μν} - (1/D) g_{μν} Re (ψ‾ M ψ)` in spacetime dimension `D = card n`. -/
theorem tracelessPart_quarkPart_of_diracEq (hg : g.IsSymm) (hγ : ∀ μ, (β * γ μ).IsHermitian)
    {M : Matrix m m ℂ} {ψ : m → ℂ} {Dψ : n → m → ℂ} (h : diracOpApply g γ Dψ = M *ᵥ ψ) :
    tracelessPart g (quarkPart β γ ψ Dψ) =
      quarkPart β γ ψ Dψ - ((star ψ ⬝ᵥ (β * M) *ᵥ ψ).re / Fintype.card n) • g := by
  rw [tracelessPart_apply, tracePart_quarkPart_of_diracEq hg hγ h]

/-- In four spacetime dimensions and on solutions of the Dirac equation `i γ^μ D_μ ψ = M ψ`, the
trace part of the total energy-momentum tensor is the classical mass term
`(1/4) g_{μν} Re (ψ‾ M ψ)`. -/
theorem tracePart_total_of_diracEq (hn : Fintype.card n = 4) (hg : g.IsSymm)
    (hγ : ∀ μ, (β * γ μ).IsHermitian) {M : Matrix m m ℂ} {ψ : m → ℂ} {Dψ : n → m → ℂ}
    (h : diracOpApply g γ Dψ = M *ᵥ ψ) (F : ι → Matrix n n ℝ) :
    tracePart g (total g β γ ψ Dψ F) = ((star ψ ⬝ᵥ (β * M) *ᵥ ψ).re / 4) • g := by
  rw [tracePart_total, tracePart_quarkPart_of_diracEq hg hγ h,
    tracePart_gluonPart_eq_zero g (.inl hn), add_zero, hn]
  norm_num

/-- When the gluon part is traceless, as it is in four spacetime dimensions or when
`F^a_{αβ} F^{a αβ} = 0` (`trace_gluonPart_eq_zero_iff`), the traceless part of the total
energy-momentum tensor is the traceless part of the quark part plus the whole gluon part. -/
theorem tracelessPart_total_of_trace_gluonPart_eq_zero (ψ : m → ℂ) (Dψ : n → m → ℂ)
    {F : ι → Matrix n n ℝ} (h : trace (g⁻¹ * gluonPart g F) = 0) :
    tracelessPart g (total g β γ ψ Dψ F) =
      tracelessPart g (quarkPart β γ ψ Dψ) + gluonPart g F := by
  rw [tracelessPart_total,
    tracelessPart_gluonPart_eq_self g ((trace_gluonPart_eq_zero_iff g F).1 h)]

end EnergyMomentumTensor
end QCD
end QFT
end EpsilonEridani
