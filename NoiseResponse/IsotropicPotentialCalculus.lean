/- Added by cx on 2026-10-29: the trace potential differentiates to
   minus the original integrated A4 response for any finite isotropic spectrum. -/
module

public import NoiseResponse.IsotropicMatrixIntegral
public import NoiseResponse.IsotropicResolventAlgebra
public import NoiseResponse.IsotropicScalarPotential
public import Mathlib.Tactic

@[expose] public section
set_option maxRecDepth 1900
set_option maxHeartbeats 7000000
noncomputable section
open Matrix Filter Set MeasureTheory
open scoped Topology Matrix.Norms.L2Operator
namespace NoiseResponse.IsotropicSpectrum
variable {Ω m n : Type*} [MeasurableSpace Ω]
variable [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] [Nonempty n]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

local instance : NormedAlgebra ℝ (Matrix n n ℂ) where
  norm_smul_le := norm_smul_le

def adjointRealCLM : Matrix m n ℂ →L[ℝ] Matrix n m ℂ :=
  (show Matrix m n ℂ →ₗ[ℝ] Matrix n m ℂ from
    { toFun := Matrix.conjTranspose
      map_add' := Matrix.conjTranspose_add
      map_smul' := by intro c B; simp }).toContinuousLinearMap

omit [DecidableEq m] [DecidableEq n] [Nonempty n] in
@[simp] theorem adjointRealCLM_apply (B : Matrix m n ℂ) : adjointRealCLM B=Bᴴ := rfl

def complexMulCLM {l : Type*} [Fintype l] :
    Matrix l m ℂ →L[ℝ] Matrix m n ℂ →L[ℝ] Matrix l n ℂ :=
  ((LinearMap.toContinuousLinearMap :
      (Matrix m n ℂ →ₗ[ℝ] Matrix l n ℂ) ≃ₗ[ℝ]
        (Matrix m n ℂ →L[ℝ] Matrix l n ℂ)).toLinearMap.comp
      (mulLinearMap ℝ)).toContinuousLinearMap

omit [DecidableEq m] [DecidableEq n] [Nonempty n] in
@[simp] theorem complexMulCLM_apply {l : Type*} [Fintype l]
    (A : Matrix l m ℂ) (B : Matrix m n ℂ) : complexMulCLM A B=A*B := rfl

def traceRightCLM (D : Matrix n n ℂ) : Matrix n n ℂ →L[ℝ] ℝ :=
  matrixTrace.comp ((ContinuousLinearMap.mul ℝ (Matrix n n ℂ)).flip D)

@[simp] theorem traceRightCLM_apply (D B : Matrix n n ℂ) :
    traceRightCLM D B=(B*D).trace.re := rfl

theorem gram_hasFDerivAt (A : E → Matrix m n ℂ) (x : E)
    (hA : DifferentiableAt ℝ A x) :
    DifferentiableAt ℝ (fun y => (A y)ᴴ*A y) x ∧
      ∀ v, fderiv ℝ (fun y => (A y)ᴴ*A y) x v=
        (fderiv ℝ A x v)ᴴ*A x+(A x)ᴴ*fderiv ℝ A x v := by
  have ha := adjointRealCLM.hasFDerivAt.comp x hA.hasFDerivAt
  have hg := (complexMulCLM (l := n) (m := m) (n := n)).hasFDerivAt_of_bilinear ha hA.hasFDerivAt
  refine ⟨hg.differentiableAt,?_⟩
  intro v
  have hh := congrArg (fun L : E →L[ℝ] Matrix n n ℂ => L v) hg.fderiv
  simpa only [ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.precompL_apply,ContinuousLinearMap.precompR_apply,
    ContinuousLinearMap.compL_apply,Function.comp_def,complexMulCLM_apply,adjointRealCLM_apply,
    add_comm] using! hh

def isotropicFrozenResponse (ν : Measure Ω) (z : Ω → ℂ) (η : ℝ)
    (A : E → Matrix m n ℂ) (P : E → Matrix n n ℂ) (x v : E) : ℝ :=
  ∫ w, (NoiseResponse.Curvature.response η
    (η • ((star (z w) • matrixResolvent (P x-η • ((A x)ᴴ*A x)) (star (z w)))*(A x)ᴴ))
    (fderiv ℝ A x v) ((fderiv ℝ A x v)ᴴ*A x+(A x)ᴴ*fderiv ℝ A x v)).trace.re ∂ν

theorem isotropic_gradient_identity (ν : Measure Ω) [IsFiniteMeasure ν]
    (z : Ω → ℂ) (hz : Measurable z) (hu : ∀ w, ‖z w‖=1)
    (η : ℝ) (hη : η ≠ 0) (A : E → Matrix m n ℂ) (P : E → Matrix n n ℂ)
    (x v : E) (hA : DifferentiableAt ℝ A x) (hP : DifferentiableAt ℝ P x)
    (hPP : ∀ᶠ y in 𝓝 x, P y*P y=P y)
    (hAt : (A x)ᴴ=(A x)ᵀ) (hAit : (fderiv ℝ A x v)ᴴ=(fderiv ℝ A x v)ᵀ)
    (hPt : (P x)ᵀ=P x) (hPH : (P x)ᴴ=P x)
    (hAP : A x*P x=A x) (hPA : P x*(A x)ᵀ=(A x)ᵀ)
    (hB : ‖P x-η • ((A x)ᴴ*A x)‖<1) :
    deriv (fun t : ℝ => isotropicPotential ν z η P (fun y => (A y)ᴴ*A y) (x+t • v)) 0=
      -isotropicFrozenResponse ν z η A P x v := by
  let H : E → Matrix n n ℂ := fun y => (A y)ᴴ*A y
  let B := P x-η • H x
  let D := (fderiv ℝ A x v)ᴴ*A x+(A x)ᴴ*fderiv ℝ A x v
  obtain ⟨hH,hHD⟩ := gram_hasFDerivAt A x hA
  have hHP : H x*P x=H x := by dsimp only [H]; rw [Matrix.mul_assoc,hAP]
  have hPH' : P x*H x=H x := by dsimp only [H]; rw [hAt,← Matrix.mul_assoc,hPA]
  have hp := isotropicPotential_hasFDerivAt ν z hu η hη P H x hP hH hPP hPH' hHP hB
  have hline := NoiseResponse.MatrixCalculus.hasDerivAt_line hp.differentiableAt v
  have hv := congrArg (fun L : E →L[ℝ] ℝ => L v) hp.fderiv
  have hi := coefficientSeries_readout_integral ν z hz hu B hB (traceRightCLM D)
  have hd : deriv (fun t : ℝ => isotropicPotential ν z η P H (x+t • v)) 0=
      (1/2 : ℝ)*traceRightCLM D (NoiseResponse.TraceSeries.coefficientSeries (spectralCoeff ν z) B) := by
    rw [hline.deriv]
    simpa only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.comp_apply,
      NoiseResponse.TraceSeries.traceLeftCLM_apply,smul_eq_mul,H,hHD v,
      traceRightCLM_apply,matrixTrace_apply,D,B] using! hv
  rw [hd,hi,← integral_const_mul]
  unfold isotropicFrozenResponse
  rw [← integral_neg]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro w
  have hc := isotropic_response_trace η hη (A x) (fderiv ℝ A x v) hAt hAit (P x)
    hPt hPH hPP.self_of_nhds hAP hPA (by simpa only [hAt] using hB) (z w) (hu w)
  have hcomm := matrixResolvent_pair_commutes B hB (z w) (star (z w)) (hu w)
    (by simpa only [norm_star] using hu w)
  dsimp only [B,H,D] at hcomm ⊢
  simp only [traceRightCLM_apply,hAt,hAit]
  simp only [hAt,hAit] at hc
  rw [hc]
  simp only [hAt,hAit] at hcomm ⊢
  have hre (c : ℂ) : (-(1/2 : ℂ)*c).re=-(1/2 : ℝ)*c.re := by
    norm_num [Complex.mul_re]
  rw [hre,hcomm]
  ring

end NoiseResponse.IsotropicSpectrum
