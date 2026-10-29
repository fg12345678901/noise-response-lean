/- Added by cx on 2026-10-29: the audited A4 Hermitian coefficient
   is exactly the manuscript (9) one-form, for the original PSD measure. -/
module

public import NoiseResponse.Theorem3Complete
public import Mathlib.Tactic

@[expose] public section
set_option maxRecDepth 2100
set_option maxHeartbeats 8000000
noncomputable section
open Matrix Filter Set MeasureTheory
open scoped Topology Matrix.Norms.L2Operator ComplexOrder
namespace NoiseResponse.OneForm
variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

theorem trace_adjoint_test (C X : Matrix m m ℂ) (hC : Cᴴ=C) :
    (Xᴴ*C).trace.re=(X*C).trace.re := by
  calc
    _ = ((C*X)ᴴ).trace.re := by rw [Matrix.conjTranspose_mul,hC]
    _ = (C*X).trace.re := by simp only [Matrix.trace_conjTranspose,Complex.star_def,Complex.conj_re]
    _ = _ := congrArg Complex.re (Matrix.trace_mul_comm C X)

theorem coefficient_one_form (η : ℝ) (A Ai : Matrix m n ℂ) (G : Matrix n m ℂ)
    (C : Matrix m m ℂ) (hC : Cᴴ=C) :
    (NoiseResponse.Curvature.response η G Ai (Aiᴴ*A+Aᴴ*Ai)*C).trace.re=
      η⁻¹*(Ai*G*C*(1-A*G)ᴴ).trace.re := by
  let X := Ai*G
  let Y := A*G
  have he : Gᴴ*Aiᴴ+Ai*G-Gᴴ*(Aiᴴ*A+Aᴴ*Ai)*G=Xᴴ+X-(Xᴴ*Y+Yᴴ*X) := by
    simp only [X,Y,Matrix.conjTranspose_mul,Matrix.mul_add,Matrix.add_mul,Matrix.mul_assoc]
  have hp : (Xᴴ*Y*C).trace.re=(Yᴴ*X*C).trace.re := by
    simpa only [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose] using
      trace_adjoint_test C (Yᴴ*X) hC
  have hx := trace_adjoint_test C X hC
  have hy : (X*C*Yᴴ).trace.re=(Yᴴ*X*C).trace.re :=
    congrArg Complex.re (Matrix.trace_mul_cycle X C Yᴴ)
  unfold NoiseResponse.Curvature.response
  rw [he]
  change (((η⁻¹*(2 : ℝ)⁻¹) • (Xᴴ+X-(Xᴴ*Y+Yᴴ*X)))*C).trace.re=
    η⁻¹*(X*C*(1-Y)ᴴ).trace.re
  simp only [Matrix.smul_mul,Matrix.trace_smul,Complex.real_smul,Matrix.sub_mul,Matrix.add_mul,
    Matrix.trace_sub,Matrix.trace_add,Complex.sub_re,Complex.add_re,Matrix.conjTranspose_sub,
    Matrix.conjTranspose_one,Matrix.mul_sub,Matrix.mul_one,hp,hx,hy]
  simp only [Complex.sub_re,Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero,hp,hx,hy]
  ring

end NoiseResponse.OneForm

namespace NoiseResponse.ResidualGeometry
open NoiseResponse.Sufficiency NoiseResponse.Geometry NoiseResponse.RankSafe
open NoiseResponse.Classification
variable {m n : Type*} [Fintype m] [DecidableEq m] [Nonempty m]
variable [Fintype n] [DecidableEq n]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {T : ℝ} [Fact (0 < T)]

theorem response_original_one_form (M : PSDMatrixMeasure (AddCircle T) m) (η : ℝ)
    (f : (n → ℝ) → (m → ℝ)) (ι : E → (n → ℝ)) (x v : E) :
    response M η f ι x v=
      ∫ w, η⁻¹*((fderiv ℝ (fun y => complexify (jacobian f ι y)) x v)*
        transfer η (complexify (jacobian f ι x)) (normalProjector (jacobian f ι x)) (fourier 1 w)*
        M.density w*(1-complexify (jacobian f ι x)*
          transfer η (complexify (jacobian f ι x)) (normalProjector (jacobian f ι x)) (fourier 1 w))ᴴ).trace.re
        ∂M.traceMeasure := by
  unfold response measuredFrozenResponse frequencyCoefficient
  apply integral_congr_ae
  filter_upwards [M.density_positive] with w hw
  exact NoiseResponse.OneForm.coefficient_one_form η _ _ _ _ hw.isHermitian.eq

end NoiseResponse.ResidualGeometry
