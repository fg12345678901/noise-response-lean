/- Added by cx on 2026-10-29: the original A4 trace collapses to a
   Gram-matrix one-form for symmetric scalar-filter transfers. -/
module

public import NoiseResponse.CurvatureAlgebra
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Tactic

@[expose] public section
set_option maxRecDepth 1700
set_option maxHeartbeats 6000000
noncomputable section
open Matrix
namespace NoiseResponse.IsotropicSpectrum
variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

theorem normalized_response (η : ℝ) (hη : η ≠ 0) (X : Matrix n m ℂ)
    (Ai : Matrix m n ℂ) (Ki : Matrix n n ℂ) :
    NoiseResponse.Curvature.response η (η • X) Ai Ki=
      (1/2 : ℝ) • (Xᴴ*Aiᴴ+Ai*X-η • (Xᴴ*Ki*X)) := by
  have hi : (η • X)ᴴ*Aiᴴ+Ai*(η • X)-(η • X)ᴴ*Ki*(η • X)=
      η • (Xᴴ*Aiᴴ+Ai*X-η • (Xᴴ*Ki*X)) := by
    simp only [Matrix.conjTranspose_smul,star_trivial,Matrix.smul_mul,Matrix.mul_smul,
      smul_add,smul_sub,smul_smul]
  unfold NoiseResponse.Curvature.response
  rw [hi,smul_smul,show η⁻¹*(2 : ℝ)⁻¹*η=(1/2 : ℝ) by field_simp]

theorem symmetric_trace_transpose (S D : Matrix n n ℂ) (hS : Sᵀ=S) :
    (S*Dᵀ).trace=(S*D).trace := by
  rw [← Matrix.trace_transpose (S*Dᵀ),Matrix.transpose_mul,Matrix.transpose_transpose,hS,
    Matrix.trace_mul_comm]

theorem symmetric_gram_trace (S : Matrix n n ℂ) (hS : Sᵀ=S)
    (A Ai : Matrix m n ℂ) :
    (S*(Aiᵀ*A+Aᵀ*Ai)).trace=2*(S*(Aᵀ*Ai)).trace := by
  have he : Aiᵀ*A=(Aᵀ*Ai)ᵀ := by simp only [Matrix.transpose_mul,Matrix.transpose_transpose]
  rw [Matrix.mul_add,Matrix.trace_add,he,symmetric_trace_transpose S _ hS]
  ring

theorem gram_response_trace (η : ℝ) (hη : η ≠ 0)
    (A Ai : Matrix m n ℂ) (hA : Aᴴ=Aᵀ) (hAi : Aiᴴ=Aiᵀ)
    (S : Matrix n n ℂ) (hS : Sᵀ=S) (hSH : (Sᴴ)ᵀ=Sᴴ)
    (hSK : S*(Aᵀ*A)=(Aᵀ*A)*S) :
    (NoiseResponse.Curvature.response η (η • (S*Aᵀ)) Ai (Aiᴴ*A+Aᴴ*Ai)).trace=
      (1/4 : ℂ)*((S+Sᴴ-(2*η : ℝ) • (S*Sᴴ*(Aᵀ*A)))*(Aiᵀ*A+Aᵀ*Ai)).trace := by
  have hAT : (Aᵀ)ᴴ=A := by rw [← hA,Matrix.conjTranspose_conjTranspose]
  have hK : (Aᵀ*A)ᴴ=Aᵀ*A := by
    rw [Matrix.conjTranspose_mul,hA,hAT]
  have hKS : (Aᵀ*A)*Sᴴ=Sᴴ*(Aᵀ*A) := by
    have he := congrArg Matrix.conjTranspose hSK
    simpa only [Matrix.conjTranspose_mul,hK] using he
  have hcross0 : ((S*Aᵀ)ᴴ*Aiᴴ).trace=(1/2 : ℂ)*(Sᴴ*(Aiᵀ*A+Aᵀ*Ai)).trace := by
    rw [Matrix.conjTranspose_mul,hAT,hAi]
    have he : (A*Sᴴ*Aiᵀ).trace=(Sᴴ*(Aiᵀ*A)).trace := by
      rw [Matrix.trace_mul_cycle]
      exact Matrix.trace_mul_comm _ _
    rw [he,symmetric_gram_trace _ hSH]
    have ht : Aiᵀ*A=(Aᵀ*Ai)ᵀ := by simp only [Matrix.transpose_mul,Matrix.transpose_transpose]
    rw [ht,symmetric_trace_transpose _ _ hSH]
    ring
  have hcross1 : (Ai*(S*Aᵀ)).trace=(1/2 : ℂ)*(S*(Aiᵀ*A+Aᵀ*Ai)).trace := by
    rw [← Matrix.mul_assoc,Matrix.trace_mul_cycle]
    rw [Matrix.trace_mul_comm (Aᵀ*Ai) S,symmetric_gram_trace _ hS]
    ring
  have hquad : ((S*Aᵀ)ᴴ*(Aiᴴ*A+Aᴴ*Ai)*(S*Aᵀ)).trace=
      (S*Sᴴ*(Aᵀ*A)*(Aiᵀ*A+Aᵀ*Ai)).trace := by
    rw [Matrix.conjTranspose_mul,hAT,hAi,hA]
    calc
      _ = (A*(Sᴴ*(Aiᵀ*A+Aᵀ*Ai)*S*Aᵀ)).trace := by simp only [Matrix.mul_assoc]
      _ = (Sᴴ*(Aiᵀ*A+Aᵀ*Ai)*S*(Aᵀ*A)).trace := by
        rw [Matrix.trace_mul_comm A]
        simp only [Matrix.mul_assoc]
      _ = ((Sᴴ*(Aiᵀ*A+Aᵀ*Ai))*(S*(Aᵀ*A))).trace := by simp only [Matrix.mul_assoc]
      _ = ((S*(Aᵀ*A))*(Sᴴ*(Aiᵀ*A+Aᵀ*Ai))).trace := Matrix.trace_mul_comm _ _
      _ = _ := by
        calc
          _ = (S*((Aᵀ*A)*Sᴴ)*(Aiᵀ*A+Aᵀ*Ai)).trace := by simp only [Matrix.mul_assoc]
          _ = _ := by rw [hKS]; simp only [Matrix.mul_assoc]
  rw [normalized_response η hη,Matrix.trace_smul,Matrix.trace_sub,Matrix.trace_add,
    Matrix.trace_smul,hcross0,hcross1,hquad]
  simp only [Matrix.sub_mul,Matrix.add_mul,Matrix.smul_mul,Matrix.trace_sub,
    Matrix.trace_add,Matrix.trace_smul,smul_eq_mul,Complex.real_smul]
  push_cast
  ring

end NoiseResponse.IsotropicSpectrum

#print axioms NoiseResponse.IsotropicSpectrum.gram_response_trace
