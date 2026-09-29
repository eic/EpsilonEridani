import EpsilonEridani.QFT.QCD.Basic
import EpsilonEridani.QFT.QCD.SU3Generators
import EpsilonEridani.QFT.Scattering.DIS.Exclusive.Kinematics.Basic
import SubVerso.Examples
open SubVerso.Examples

%example asymptotic_freedom
open EpsilonEridani.QFT.QCD in
/-- Asymptotic freedom — the one-loop coefficient of the QCD β-function is
β₀ = 11 − (2/3) n_f, so QCD is asymptotically free for fewer than 16.5 quark flavours. -/
theorem asymptotic_freedom (nF : ℝ) (h : 2 * nF < 33) :
    beta0 (suNColorFactors 3 nF) = 11 - (2 / 3) * nF ∧
      IsAsymptoticallyFree (suNColorFactors 3 nF) :=
  ⟨by rw [beta0_suNColorFactors]; ring, isAsymptoticallyFree_qcd nF h⟩
%end

%example su3_adjoint_casimir
open EpsilonEridani.QFT.QCD.RepresentationColor in
/-- The adjoint Casimir of SU(3) — the Gell-Mann structure constants satisfy
Σ_{c,d} f^{acd} f^{bcd} = 3 δ^{ab}, i.e. C_A = 3, checked over every index. -/
theorem su3_adjoint_casimir (a b : Fin 8) :
    (∑ c : Fin 8, ∑ d : Fin 8, structConst3 a c d * structConst3 b c d) =
      3 * su3DeltaAdj a b :=
  su3AdjointStatement a b
%end

%example dvcs_momentum_transfer
open EpsilonEridani.QFT.Scattering.DIS.Exclusive.Kinematics in
/-- Momentum transfer in deeply virtual Compton scattering — momentum conservation
p + q = p' + q' makes the hadronic t = (p' − p)² equal to the photon-side (q − q')². -/
theorem dvcs_momentum_transfer {V : Type} [AddCommGroup V] [Module ℝ V]
    (g : LinearMap.BilinForm ℝ V) (K : ExclKinematics V) :
    K.tMom g = g (K.q - K.qPrime) (K.q - K.qPrime) :=
  K.tMom_eq_photon_transfer_sq g
%end
