/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
public import Physlib.Relativity.Tensors.RealTensor.Vector.MinkowskiProduct

/-!
# Minkowski product extensions

Local extensions to `Physlib.Relativity.Tensors.RealTensor.Vector.MinkowskiProduct`, not yet
upstreamed to Physlib: symmetry of the Minkowski product as a bilinear form
(`isSymm_toBilinForm_minkowskiProduct`), the witness that supplies the `IsRefl` hypothesis of
the reflexive-form results about light-cone bases in
`EpsilonEridani.Relativity.LightConeBasis`.
-/

public section

namespace EpsilonEridani

open Lorentz Vector

variable {d : ℕ}

/-- The Minkowski product is a symmetric bilinear form; in particular the reflexivity hypothesis
of `LightConeBasis.bilinForm_eq_plus_mul_minus_add` and
`LightConeBasis.isSelfAdjoint_transverseProj` holds for it (via `IsSymm.isRefl`). -/
theorem isSymm_toBilinForm_minkowskiProduct : (minkowskiProduct (d := d)).toBilinForm.IsSymm :=
  ⟨minkowskiProduct_symm⟩

end EpsilonEridani
