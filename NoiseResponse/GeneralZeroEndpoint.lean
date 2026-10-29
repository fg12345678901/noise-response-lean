/- Added by cx on 2026-10-29: zero-frequency sufficiency for a
   genuinely varying constant-rank Jacobian, using the output projector. -/
module

public import NoiseResponse.IsotropicPotentialCalculus
public import NoiseResponse.ZeroEndpointPotential
public import Mathlib.Tactic

@[expose] public section
set_option maxRecDepth 1900
set_option maxHeartbeats 7000000
noncomputable section
open Matrix Filter
open scoped Topology Matrix.Norms.L2Operator
namespace NoiseResponse.GeneralEndpoint
open NoiseResponse.IsotropicSpectrum
variable {m n : Type*} [Fintype m] [DecidableEq m] [Nonempty m]
variable [Fintype n] [DecidableEq n]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
local instance : NormedAlgebra ℝ (Matrix m m ℂ) where
  norm_smul_le := norm_smul_le

theorem projector_adjoint_derivative (P : E → Matrix m m ℂ) (x v : E)
    (hP : DifferentiableAt ℝ P x) (hPH : ∀ᶠ y in 𝓝 x, (P y)ᴴ=P y) :
    (fderiv ℝ P x v)ᴴ=fderiv ℝ P x v := by
  have hh := (adjointRealCLM (m := m) (n := m)).hasFDerivAt.comp x hP.hasFDerivAt
  have heq : P=ᶠ[𝓝 x] (adjointRealCLM ∘ P) := by
    filter_upwards [hPH] with y hy
    simpa only [Function.comp_def,adjointRealCLM_apply] using! hy.symm
  have hfd := (hh.congr_of_eventuallyEq heq).fderiv
  have he := congrArg (fun L : E →L[ℝ] Matrix m m ℂ => L v) hfd
  simpa only [ContinuousLinearMap.comp_apply,adjointRealCLM_apply] using! he.symm

theorem range_projector_derivative (P : E → Matrix m m ℂ) (A : E → Matrix m n ℂ)
    (G : Matrix n m ℂ) (x v : E)
    (hP : DifferentiableAt ℝ P x) (hA : DifferentiableAt ℝ A x)
    (hPP : ∀ᶠ y in 𝓝 x, P y*P y=P y)
    (hPH : ∀ᶠ y in 𝓝 x, (P y)ᴴ=P y)
    (hPA : ∀ᶠ y in 𝓝 x, P y*A y=A y) (hAG : A x*G=P x) :
    fderiv ℝ P x v=(1-P x)*fderiv ℝ A x v*G+
      Gᴴ*(fderiv ℝ A x v)ᴴ*(1-P x) := by
  have hp := (complexMulCLM (l := m) (m := m) (n := n)).hasFDerivAt_of_bilinear
    hP.hasFDerivAt hA.hasFDerivAt
  have heq : A=ᶠ[𝓝 x] (fun y => complexMulCLM (P y) (A y)) := by
    filter_upwards [hPA] with y hy
    simpa only [complexMulCLM_apply] using! hy.symm
  have he := congrArg (fun L : E →L[ℝ] Matrix m n ℂ => L v)
    (hp.congr_of_eventuallyEq heq).fderiv
  have hd : fderiv ℝ P x v*A x+P x*fderiv ℝ A x v=fderiv ℝ A x v := by
    simpa only [ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.precompL_apply,ContinuousLinearMap.precompR_apply,
      ContinuousLinearMap.compL_apply,complexMulCLM_apply,add_comm] using! he.symm
  have hdp : fderiv ℝ P x v*P x=(1-P x)*fderiv ℝ A x v*G := by
    have hh := congrArg (fun D : Matrix m n ℂ => D*G) hd
    rw [Matrix.add_mul,Matrix.mul_assoc,hAG] at hh
    simp only [Matrix.sub_mul,Matrix.one_mul]
    exact eq_sub_of_add_eq hh
  have hpd : P x*fderiv ℝ P x v=Gᴴ*(fderiv ℝ A x v)ᴴ*(1-P x) := by
    have hh := congrArg Matrix.conjTranspose hdp
    simpa only [Matrix.conjTranspose_mul,Matrix.conjTranspose_sub,Matrix.conjTranspose_one,
      hPH.self_of_nhds,projector_adjoint_derivative P x v hP hPH,Matrix.mul_assoc] using! hh
  have hh := NoiseResponse.TraceSeries.idempotent_field_derivative P x v hP hPP
  rw [hpd,hdp,add_comm] at hh
  exact hh.symm

theorem zero_response_projector_identity (η : ℝ) (A Ai : Matrix m n ℂ)
    (G : Matrix n m ℂ) (P : Matrix m m ℂ) (hP : Pᴴ=P) (hAG : A*G=P) :
    NoiseResponse.Curvature.response η G Ai (Aiᴴ*A+Aᴴ*Ai)=
      (η⁻¹*(2 : ℝ)⁻¹) • ((1-P)*Ai*G+Gᴴ*Aiᴴ*(1-P)) := by
  have hGA : Gᴴ*Aᴴ=P := by
    simpa only [Matrix.conjTranspose_mul,hP] using congrArg Matrix.conjTranspose hAG
  unfold NoiseResponse.Curvature.response
  congr 1
  simp only [Matrix.mul_add,Matrix.add_mul,Matrix.sub_mul,Matrix.mul_sub,
    Matrix.one_mul,Matrix.mul_one]
  have h₁ : Gᴴ*(Aiᴴ*A)*G=Gᴴ*Aiᴴ*P := by simp only [Matrix.mul_assoc,hAG]
  have h₂ : Gᴴ*(Aᴴ*Ai)*G=P*Ai*G := by rw [← Matrix.mul_assoc Gᴴ Aᴴ Ai,hGA]
  rw [h₁,h₂]
  abel

def zeroPotential (η : ℝ) (M : Matrix m m ℂ) (P : E → Matrix m m ℂ) (x : E) : ℝ :=
  -(2*η)⁻¹*(M*P x).trace.re

theorem zero_gradient_identity (η : ℝ) (M : Matrix m m ℂ)
    (A : E → Matrix m n ℂ) (P : E → Matrix m m ℂ) (G : Matrix n m ℂ)
    (x v : E) (hA : DifferentiableAt ℝ A x) (hP : DifferentiableAt ℝ P x)
    (hPP : ∀ᶠ y in 𝓝 x, P y*P y=P y)
    (hPH : ∀ᶠ y in 𝓝 x, (P y)ᴴ=P y)
    (hPA : ∀ᶠ y in 𝓝 x, P y*A y=A y) (hAG : A x*G=P x) :
    deriv (fun t : ℝ => zeroPotential η M P (x+t • v)) 0=
      -(NoiseResponse.Curvature.response η G (fderiv ℝ A x v)
        ((fderiv ℝ A x v)ᴴ*A x+(A x)ᴴ*fderiv ℝ A x v)*M).trace.re := by
  have hp := NoiseResponse.MatrixCalculus.hasDerivAt_line hP v
  let L : Matrix m m ℂ →L[ℝ] ℝ := NoiseResponse.TraceSeries.traceLeftCLM matrixTrace M
  have hh := (L.hasFDerivAt.comp_hasDerivAt 0 hp).const_mul (-(2*η)⁻¹)
  have he : deriv (fun t : ℝ => zeroPotential η M P (x+t • v)) 0=
      -(2*η)⁻¹*(M*fderiv ℝ P x v).trace.re := by
    simpa only [L,NoiseResponse.TraceSeries.traceLeftCLM_apply,matrixTrace_apply,zeroPotential] using! hh.deriv
  rw [he,range_projector_derivative P A G x v hP hA hPP hPH hPA hAG,
    zero_response_projector_identity η (A x) (fderiv ℝ A x v) G (P x) hPH.self_of_nhds hAG,
    Matrix.smul_mul,Matrix.trace_smul,Complex.smul_re,Matrix.trace_mul_comm M]
  have hcoef : (2*η)⁻¹=η⁻¹*(2 : ℝ)⁻¹ := by ring
  rw [hcoef]
  simp only [smul_eq_mul]
  ring

end NoiseResponse.GeneralEndpoint
