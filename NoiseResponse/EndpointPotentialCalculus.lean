/- Added by cx on 2026-10-29: genuine derivative of the Nyquist
   trace potential, with its resolvent derivative proved implicitly.
   This is an endpoint sufficiency component, not the full theorem. -/
module

public import NoiseResponse.CurvatureCalculus
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Trace
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

def traceRealCLM : Matrix m m ℂ →L[ℝ] ℝ :=
  Complex.reCLM.comp (Matrix.traceLinearMap m ℝ ℂ).toContinuousLinearMap

@[simp] theorem traceRealCLM_apply (A : Matrix m m ℂ) : traceRealCLM A=A.trace.re := rfl

def nyquistResolventDen (η : ℝ) (H : Matrix m m ℂ) : Matrix m m ℂ :=
  (2 : ℝ) • 1-η • H

theorem nyquist_resolvent_derivative (η : ℝ)
    (H T : E → Matrix m m ℂ) (x v : E)
    (hH : DifferentiableAt ℝ H x) (hT : DifferentiableAt ℝ T x)
    (hR : ∀ᶠ y in 𝓝 x, nyquistResolventDen η (H y)*T y=1) :
    fderiv ℝ T x v=η • (T x*fderiv ℝ H x v*T x) := by
  have ht : Tendsto (fun t : ℝ => x+t • v) (𝓝 0) (𝓝 x) := by
    have hc : Continuous (fun t : ℝ => x+t • v) := by fun_prop
    simpa only [zero_smul, add_zero] using hc.tendsto 0
  have hHl := hasDerivAt_line hH v
  have hTl := hasDerivAt_line hT v
  have hden := ((hHl.const_smul η).neg).const_add ((2 : ℝ) • (1 : Matrix m m ℂ))
  have hp := hasDerivAt_mul hden hTl
  have hline := ht hR
  change (fun t : ℝ => (2 • (1 : Matrix m m ℂ)-η • H (x+t • v))*T (x+t • v))
    =ᶠ[𝓝 0] (fun _ => 1) at hline
  have he := hp.unique ((hasDerivAt_const 0 (1 : Matrix m m ℂ)).congr_of_eventuallyEq hline)
  simp only [Pi.neg_apply, Pi.smul_apply, zero_smul, add_zero, neg_smul,
    Matrix.neg_mul, Matrix.smul_mul] at he
  have heq : nyquistResolventDen η (H x)*fderiv ℝ T x v=
      η • (fderiv ℝ H x v*T x) := by
    change -(η • (fderiv ℝ H x v*T x))+
      nyquistResolventDen η (H x)*fderiv ℝ T x v=0 at he
    exact eq_of_sub_eq_zero (by simpa only [sub_eq_add_neg, add_comm] using he)
  have hTR : T x*nyquistResolventDen η (H x)=1 := mul_eq_one_comm.mp hR.self_of_nhds
  have hh := congrArg (fun B : Matrix m m ℂ => T x*B) heq
  simpa only [← Matrix.mul_assoc, hTR, Matrix.one_mul, Matrix.mul_smul] using hh

theorem nyquist_product_derivative (η : ℝ)
    (H T : E → Matrix m m ℂ) (x v : E)
    (hH : DifferentiableAt ℝ H x) (hT : DifferentiableAt ℝ T x)
    (hR : ∀ᶠ y in 𝓝 x, nyquistResolventDen η (H y)*T y=1) :
    fderiv ℝ (fun y => H y*T y) x v=(2 : ℝ) • (T x*fderiv ℝ H x v*T x) := by
  have hHT : η • (H x*T x)=(2 : ℝ) • T x-1 := by
    have he := hR.self_of_nhds
    unfold nyquistResolventDen at he
    rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul] at he
    apply (eq_sub_iff_add_eq).mpr
    simpa only [add_comm] using (sub_eq_iff_eq_add.mp he).symm
  rw [fderiv_mul_apply hH hT v, nyquist_resolvent_derivative η H T x v hH hT hR]
  calc
    _ = fderiv ℝ H x v*T x+(η • (H x*T x))*fderiv ℝ H x v*T x := by
      simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
    _ = _ := by
      rw [hHT]
      simp only [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul]
      abel

def nyquistPotential (M : Matrix m m ℂ) (H T : E → Matrix m m ℂ) (x : E) : ℝ :=
  (1/2 : ℝ)*traceRealCLM (M*(H x*T x))

theorem nyquist_potential_derivative (η : ℝ) (M : Matrix m m ℂ)
    (H T : E → Matrix m m ℂ) (x v : E)
    (hH : DifferentiableAt ℝ H x) (hT : DifferentiableAt ℝ T x)
    (hR : ∀ᶠ y in 𝓝 x, nyquistResolventDen η (H y)*T y=1) :
    deriv (fun t : ℝ => nyquistPotential M H T (x+t • v)) 0=
      traceRealCLM (M*(T x*fderiv ℝ H x v*T x)) := by
  have hprod : DifferentiableAt ℝ (fun y => H y*T y) x :=
    ((mulCLM (l := m) (m := m) (n := m)).hasFDerivAt_of_bilinear
      hH.hasFDerivAt hT.hasFDerivAt).differentiableAt
  have hp := hasDerivAt_line hprod v
  rw [nyquist_product_derivative η H T x v hH hT hR] at hp
  have hleft := hasDerivAt_mul (hasDerivAt_const 0 M) hp
  have hr := traceRealCLM.hasFDerivAt.comp_hasDerivAt 0 hleft
  have hh := hr.const_mul (1/2 : ℝ)
  convert hh.deriv using 1
  · rfl
  · simp only [zero_mul, zero_add, Matrix.mul_smul, map_smul, smul_eq_mul]
    ring

/-- Algebraic identification of the Nyquist A4 coefficient. -/
theorem nyquist_response_coefficient (η : ℝ) (hη : η ≠ 0)
    (A Ai : Matrix m n ℂ) (T : Matrix m m ℂ) (hT : Tᴴ=T)
    (hR : nyquistResolventDen η (A*Aᴴ)*T=1) :
    NoiseResponse.Curvature.response η (-η • (Aᴴ*T)) Ai (Aiᴴ*A+Aᴴ*Ai)=
      -(T*(Ai*Aᴴ+A*Aiᴴ)*T) := by
  have hRT : T*nyquistResolventDen η (A*Aᴴ)=1 := mul_eq_one_comm.mp hR
  have h1 : η • ((A*Aᴴ)*T)=(2 : ℝ) • T-1 := by
    unfold nyquistResolventDen at hR
    simp only [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul] at hR
    apply (eq_sub_iff_add_eq).mpr
    simpa only [add_comm] using (sub_eq_iff_eq_add.mp hR).symm
  have h2 : η • (T*(A*Aᴴ))=(2 : ℝ) • T-1 := by
    unfold nyquistResolventDen at hRT
    simp only [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one] at hRT
    apply (eq_sub_iff_add_eq).mpr
    simpa only [add_comm] using (sub_eq_iff_eq_add.mp hRT).symm
  have hquad : η • (T*A*(Aiᴴ*A+Aᴴ*Ai)*Aᴴ*T)=
      (2 : ℝ) • (T*A*Aiᴴ*T)-T*A*Aiᴴ+
        (2 : ℝ) • (T*Ai*Aᴴ*T)-Ai*Aᴴ*T := by
    calc
      _ = T*A*Aiᴴ*(η • ((A*Aᴴ)*T))+(η • (T*(A*Aᴴ)))*Ai*Aᴴ*T := by
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
          smul_add, Matrix.mul_assoc]
      _ = _ := by
        rw [h1,h2]
        simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
          Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
        abel
  have hinner (Ki : Matrix n n ℂ) :
      (-η • (Aᴴ*T))ᴴ*Aiᴴ+Ai*(-η • (Aᴴ*T))-
        (-η • (Aᴴ*T))ᴴ*Ki*(-η • (Aᴴ*T))=
      (-η) • (T*A*Aiᴴ+Ai*Aᴴ*T+η • (T*A*Ki*Aᴴ*T)) := by
    simp only [Matrix.conjTranspose_smul, star_trivial, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hT, Matrix.smul_mul, Matrix.mul_smul,
      smul_add, smul_sub, smul_smul, Matrix.mul_assoc]
    module
  unfold NoiseResponse.Curvature.response
  rw [hinner, smul_smul,
    show η⁻¹*(2 : ℝ)⁻¹*(-η)=(-1/2 : ℝ) by field_simp, hquad]
  simp only [Matrix.mul_add, Matrix.add_mul, smul_add, smul_sub, smul_smul,
    Matrix.mul_assoc]
  module

theorem nyquist_resolvent_hermitian (η : ℝ) (H T : Matrix m m ℂ)
    (hH : Hᴴ=H) (hR : nyquistResolventDen η H*T=1) : Tᴴ=T := by
  have hRH : (nyquistResolventDen η H)ᴴ=nyquistResolventDen η H := by
    simp only [nyquistResolventDen, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_one, star_trivial, hH]
  have he := congrArg Matrix.conjTranspose hR
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_one, hRH] at he
  have hh := congrArg (fun B : Matrix m m ℂ => B*T) he
  simpa only [Matrix.mul_assoc, hR, Matrix.mul_one, Matrix.one_mul] using hh

/-- The whole Nyquist endpoint component of (13): its actual A4
    coefficient equals minus the derivative of the stated trace potential.
    The inverse relation and differentiability are explicit conditions;
    neither the derivative formula nor an existing potential is assumed. -/
theorem nyquist_gradient_identity (η : ℝ) (hη : η ≠ 0) (M : Matrix m m ℂ)
    (A : E → Matrix m n ℂ) (T : E → Matrix m m ℂ) (x v : E)
    (hA : DifferentiableAt ℝ A x) (hT : DifferentiableAt ℝ T x)
    (hR : ∀ᶠ y in 𝓝 x, nyquistResolventDen η (A y*(A y)ᴴ)*T y=1) :
    deriv (fun t : ℝ => nyquistPotential M (fun y => A y*(A y)ᴴ) T (x+t • v)) 0=
      -(Matrix.trace (NoiseResponse.Curvature.response η (-η • ((A x)ᴴ*T x))
        (fderiv ℝ A x v) ((fderiv ℝ A x v)ᴴ*A x+(A x)ᴴ*fderiv ℝ A x v)*M)).re := by
  have hAH : DifferentiableAt ℝ (fun y => (A y)ᴴ) x := by
    exact (adjCLM.hasFDerivAt.comp x hA.hasFDerivAt).differentiableAt
  have hH : DifferentiableAt ℝ (fun y => A y*(A y)ᴴ) x :=
    ((mulCLM (l := m) (m := n) (n := m)).hasFDerivAt_of_bilinear
      hA.hasFDerivAt hAH.hasFDerivAt).differentiableAt
  have hTH : (T x)ᴴ=T x := nyquist_resolvent_hermitian η _ _ (by simp) hR.self_of_nhds
  have hAD : fderiv ℝ (fun y => (A y)ᴴ) x v=(fderiv ℝ A x v)ᴴ := by
    have he := congrArg (fun L : E →L[ℝ] Matrix n m ℂ => L v)
      (adjCLM.hasFDerivAt.comp x hA.hasFDerivAt).fderiv
    exact he
  rw [nyquist_potential_derivative η M _ T x v hH hT hR,
    fderiv_mul_apply hA hAH v, hAD,
    nyquist_response_coefficient η hη _ _ _ hTH hR.self_of_nhds]
  change (M*(T x*(fderiv ℝ A x v*(A x)ᴴ+A x*(fderiv ℝ A x v)ᴴ)*T x)).trace.re = _
  rw [Matrix.neg_mul, Matrix.trace_neg, Complex.neg_re, neg_neg, Matrix.trace_mul_comm]

end NoiseResponse.Classification

#print axioms NoiseResponse.Classification.nyquist_potential_derivative
#print axioms NoiseResponse.Classification.nyquist_response_coefficient
#print axioms NoiseResponse.Classification.nyquist_gradient_identity
