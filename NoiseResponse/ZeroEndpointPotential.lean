/- Added by cx on 2026-10-29: zero-endpoint sufficiency in a full-column
   normal frame. Actual Gram inverse, range projector and derivatives;
   no projection-derivative or potential identity is assumed. -/
module

public import NoiseResponse.EndpointPotentialCalculus
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Tactic

@[expose] public section
set_option maxRecDepth 1500
set_option maxHeartbeats 5000000
noncomputable section
open Matrix Filter
open scoped Topology Matrix.Norms.Elementwise
attribute [local instance] matrixNormTopology
namespace NoiseResponse.Classification
open NoiseResponse.MatrixCalculus
variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem gram_inverse_derivative (K T : E → Matrix n n ℂ) (x v : E)
    (hK : DifferentiableAt ℝ K x) (hT : DifferentiableAt ℝ T x)
    (hKT : ∀ᶠ y in 𝓝 x, K y*T y=1) :
    fderiv ℝ T x v=-(T x*fderiv ℝ K x v*T x) := by
  have ht : Tendsto (fun t : ℝ => x+t • v) (𝓝 0) (𝓝 x) := by
    have hc : Continuous (fun t : ℝ => x+t • v) := by fun_prop
    simpa only [zero_smul, add_zero] using hc.tendsto 0
  have hp := hasDerivAt_mul (hasDerivAt_line hK v) (hasDerivAt_line hT v)
  have he := hp.unique ((hasDerivAt_const 0 (1 : Matrix n n ℂ)).congr_of_eventuallyEq (ht hKT))
  simp only [zero_smul, add_zero] at he
  have heq : K x*fderiv ℝ T x v=-(fderiv ℝ K x v*T x) :=
    (eq_neg_iff_add_eq_zero).mpr (by simpa only [add_comm] using he)
  have hTK : T x*K x=1 := mul_eq_one_comm.mp hKT.self_of_nhds
  have hh := congrArg (fun B : Matrix n n ℂ => T x*B) heq
  simpa only [← Matrix.mul_assoc, hTK, Matrix.one_mul, Matrix.mul_neg] using hh

theorem hermitian_inverse (K T : Matrix n n ℂ) (hK : Kᴴ=K) (hKT : K*T=1) : Tᴴ=T := by
  have he := congrArg Matrix.conjTranspose hKT
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_one, hK] at he
  have hh := congrArg (fun B : Matrix n n ℂ => B*T) he
  simpa only [Matrix.mul_assoc, hKT, Matrix.mul_one, Matrix.one_mul] using hh

def frameProjector (A : Matrix m n ℂ) (T : Matrix n n ℂ) : Matrix m m ℂ := A*T*Aᴴ

theorem frameProjector_properties (A : Matrix m n ℂ) (T : Matrix n n ℂ)
    (hKT : (Aᴴ*A)*T=1) :
    (frameProjector A T)ᴴ=frameProjector A T ∧
      frameProjector A T*A=A ∧ frameProjector A T*frameProjector A T=frameProjector A T := by
  have hT : Tᴴ=T := hermitian_inverse _ _ (by simp) hKT
  have hTK : T*(Aᴴ*A)=1 := mul_eq_one_comm.mp hKT
  have hPA : frameProjector A T*A=A := by
    calc
      _ = A*(T*(Aᴴ*A)) := by simp only [frameProjector, Matrix.mul_assoc]
      _ = A := by rw [hTK, Matrix.mul_one]
  refine ⟨?_,hPA,?_⟩
  · simp only [frameProjector, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      hT, Matrix.mul_assoc]
  · change frameProjector A T*(A*T*Aᴴ)=frameProjector A T
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hPA]
    rfl

theorem frameProjector_range (A : Matrix m n ℂ) (T : Matrix n n ℂ)
    (hKT : (Aᴴ*A)*T=1) :
    LinearMap.range (frameProjector A T).toLin'=LinearMap.range A.toLin' := by
  have hPA := (frameProjector_properties A T hKT).2.1
  apply le_antisymm
  · rw [frameProjector, Matrix.mul_assoc, Matrix.toLin'_mul]
    exact LinearMap.range_comp_le_range _ _
  · intro y hy
    obtain ⟨v,rfl⟩ := hy
    refine ⟨A.toLin' v,?_⟩
    have he := congrArg (fun B : Matrix m n ℂ => B.toLin' v) hPA
    simpa only [Matrix.toLin'_mul, LinearMap.comp_apply] using he

theorem zero_endpoint_projector_derivative (A : E → Matrix m n ℂ)
    (T : E → Matrix n n ℂ) (x v : E)
    (hA : DifferentiableAt ℝ A x) (hT : DifferentiableAt ℝ T x)
    (hKT : ∀ᶠ y in 𝓝 x, ((A y)ᴴ*A y)*T y=1) :
    fderiv ℝ (fun y => frameProjector (A y) (T y)) x v=
      fderiv ℝ A x v*T x*(A x)ᴴ+A x*T x*(fderiv ℝ A x v)ᴴ-
        A x*T x*((fderiv ℝ A x v)ᴴ*A x+(A x)ᴴ*fderiv ℝ A x v)*T x*(A x)ᴴ := by
  have hAH : HasFDerivAt (fun y => (A y)ᴴ) (adjCLM.comp (fderiv ℝ A x)) x := by
    exact adjCLM.hasFDerivAt.comp x hA.hasFDerivAt
  have hK : DifferentiableAt ℝ (fun y => (A y)ᴴ*A y) x :=
    ((mulCLM (l := n) (m := m) (n := n)).hasFDerivAt_of_bilinear
      hAH hA.hasFDerivAt).differentiableAt
  have hAT : DifferentiableAt ℝ (fun y => A y*T y) x :=
    ((mulCLM (l := m) (m := n) (n := n)).hasFDerivAt_of_bilinear
      hA.hasFDerivAt hT.hasFDerivAt).differentiableAt
  have hAi : fderiv ℝ (fun y => (A y)ᴴ) x v=(fderiv ℝ A x v)ᴴ := by
    exact congrArg (fun L : E →L[ℝ] Matrix n m ℂ => L v) hAH.fderiv
  unfold frameProjector
  rw [fderiv_mul_apply hAT hAH.differentiableAt v,
    fderiv_mul_apply hA hT v,
    gram_inverse_derivative _ T x v hK hT hKT,
    fderiv_mul_apply hAH.differentiableAt hA v, hAi]
  simp only [Matrix.add_mul, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
  abel

def zeroEndpointPotential (η : ℝ) (M : Matrix m m ℂ)
    (A : E → Matrix m n ℂ) (T : E → Matrix n n ℂ) (x : E) : ℝ :=
  -(2*η)⁻¹*traceRealCLM (M*frameProjector (A x) (T x))

theorem zero_endpoint_gradient_identity (η : ℝ) (hη : η ≠ 0) (M : Matrix m m ℂ)
    (A : E → Matrix m n ℂ) (T : E → Matrix n n ℂ) (x v : E)
    (hA : DifferentiableAt ℝ A x) (hT : DifferentiableAt ℝ T x)
    (hKT : ∀ᶠ y in 𝓝 x, ((A y)ᴴ*A y)*T y=1) :
    deriv (fun t : ℝ => zeroEndpointPotential η M A T (x+t • v)) 0=
      -(Matrix.trace (NoiseResponse.Curvature.response η (T x*(A x)ᴴ)
        (fderiv ℝ A x v) ((fderiv ℝ A x v)ᴴ*A x+(A x)ᴴ*fderiv ℝ A x v)*M)).re := by
  have hAHfd : HasFDerivAt (fun y => (A y)ᴴ) (adjCLM.comp (fderiv ℝ A x)) x := by
    exact adjCLM.hasFDerivAt.comp x hA.hasFDerivAt
  have hAH := hAHfd.differentiableAt
  have hAT : DifferentiableAt ℝ (fun y => A y*T y) x :=
    ((mulCLM (l := m) (m := n) (n := n)).hasFDerivAt_of_bilinear
      hA.hasFDerivAt hT.hasFDerivAt).differentiableAt
  have hP : DifferentiableAt ℝ (fun y => frameProjector (A y) (T y)) x :=
    ((mulCLM (l := m) (m := n) (n := m)).hasFDerivAt_of_bilinear
      hAT.hasFDerivAt hAH.hasFDerivAt).differentiableAt
  have hTreal : (T x)ᴴ=T x := hermitian_inverse _ _ (by simp) hKT.self_of_nhds
  have hp := hasDerivAt_line hP v
  rw [zero_endpoint_projector_derivative A T x v hA hT hKT] at hp
  have hleft := hasDerivAt_mul (hasDerivAt_const 0 M) hp
  have hh := (traceRealCLM.hasFDerivAt.comp_hasDerivAt 0 hleft).const_mul (-(2*η)⁻¹)
  rw [show deriv (fun t : ℝ => zeroEndpointPotential η M A T (x+t • v)) 0=
    -(2*η)⁻¹*traceRealCLM (M*(fderiv ℝ A x v*T x*(A x)ᴴ+
      A x*T x*(fderiv ℝ A x v)ᴴ-
      A x*T x*((fderiv ℝ A x v)ᴴ*A x+(A x)ᴴ*fderiv ℝ A x v)*T x*(A x)ᴴ)) by
      simpa only [zeroEndpointPotential, Function.comp_def, zero_mul, zero_add] using hh.deriv]
  simp only [NoiseResponse.Curvature.response, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hTreal, Matrix.smul_mul,
    traceRealCLM_apply, Matrix.trace_smul, Complex.smul_re, Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm M]
  have he : -(2*η)⁻¹=-(η⁻¹*(2 : ℝ)⁻¹) := by field_simp
  rw [he]
  simp only [smul_eq_mul, neg_mul]
  congr 2
  abel

end NoiseResponse.Classification

#print axioms NoiseResponse.Classification.zero_endpoint_gradient_identity
