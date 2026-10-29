/- Added by cx on 2026-10-29: integrate the actual scalar normal
   transfer kernels to recover the stationary covariance and cross moment. -/
module

public import NoiseResponse.RankOneSpectralKernel
public import NoiseResponse.FlatResponseRealization
public import Mathlib.Tactic

@[expose] public section
set_option maxRecDepth 1200
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory Filter Set Matrix Complex
open scoped Topology Matrix.Norms.Elementwise ComplexConjugate
attribute [local instance] matrixNormTopology
namespace NoiseResponse.Classification
variable {Ω m : Type*} [MeasurableSpace Ω] [Fintype m] [DecidableEq m] [Nonempty m]

theorem cross_kernel_integrable
    (μ : Measure Ω) (F : Ω → Matrix m m ℂ) (hF : Integrable F μ)
    (z : Ω → ℂ) (hz : Measurable z) (hzunit : ∀ x, ‖z x‖=1)
    (a : ℝ) (ha : ‖a‖<1) : Integrable (fun x => causalCrossKernel a (z x) • F x) μ := by
  apply hF.bdd_smul (φ := fun x => causalCrossKernel a (z x)) (1/(1-‖a‖))
  · apply Measurable.aestronglyMeasurable
    unfold causalCrossKernel
    fun_prop
  · exact Eventually.of_forall (fun x => causalCrossKernel_bound a ha (z x) (hzunit x))

theorem weighted_hermitian_integral
    (μ : Measure Ω) (F : Ω → Matrix m m ℂ) (hH : ∀ᵐ x ∂μ, (F x)ᴴ=F x)
    (k : Ω → ℂ) (hk : Integrable (fun x => k x • F x) μ) :
    (∫ x, star (k x) • F x ∂μ)=(∫ x, k x • F x ∂μ)ᴴ := by
  rw [← NoiseResponse.MatrixCalculus.adjCLM_apply,
    ← NoiseResponse.MatrixCalculus.adjCLM.integral_comp_comm hk]
  apply integral_congr_ae
  filter_upwards [hH] with x hx
  simp only [NoiseResponse.MatrixCalculus.adjCLM_apply, Matrix.conjTranspose_smul, hx]

theorem normal_power_integral
    (μ : Measure Ω) (F : Ω → Matrix m m ℂ) (hF : Integrable F μ)
    (hH : ∀ᵐ x ∂μ, (F x)ᴴ=F x)
    (z : Ω → ℂ) (hz : Measurable z) (hzunit : ∀ x, ‖z x‖=1)
    (a : ℝ) (ha : ‖a‖<1) :
    (∫ x, normalPowerKernel a (z x) • F x ∂μ)=(1-(a : ℂ)^2)⁻¹ •
      ((∫ x, F x ∂μ)+(a : ℂ) • (spectralGenerating μ F z a+(spectralGenerating μ F z a)ᴴ)) := by
  have hk := cross_kernel_integrable μ F hF z hz hzunit a ha
  have hks : Integrable (fun x => star (causalCrossKernel a (z x)) • F x) μ := by
    apply hF.bdd_smul (φ := fun x => star (causalCrossKernel a (z x))) (1/(1-‖a‖))
    · apply Measurable.aestronglyMeasurable
      unfold causalCrossKernel
      fun_prop
    · exact Eventually.of_forall (fun x => by
        simpa only [norm_star] using causalCrossKernel_bound a ha (z x) (hzunit x))
  have hpoint (x : Ω) : normalPowerKernel a (z x) • F x=
      (1-(a : ℂ)^2)⁻¹ • (F x+(a : ℂ) •
        (causalCrossKernel a (z x) • F x+star (causalCrossKernel a (z x)) • F x)) := by
    rw [normalPowerKernel_poisson a ha (z x) (hzunit x)]
    simp only [mul_smul, add_smul, one_smul]
  have hK : (∫ x, causalCrossKernel a (z x) • F x ∂μ)=spectralGenerating μ F z a :=
    (spectral_generating_resolvent μ F hF z hz hzunit a ha).symm
  have hsum : Integrable (fun x => (a : ℂ) •
      (causalCrossKernel a (z x) • F x+star (causalCrossKernel a (z x)) • F x)) μ :=
    (hk.add hks).smul (a : ℂ)
  calc
    _ = ∫ x, (1-(a : ℂ)^2)⁻¹ • (F x+(a : ℂ) •
        (causalCrossKernel a (z x) • F x+star (causalCrossKernel a (z x)) • F x)) ∂μ :=
      integral_congr_ae (Eventually.of_forall hpoint)
    _ = _ := by
      rw [integral_smul, integral_add hF hsum, integral_smul,
        integral_add hk hks, weighted_hermitian_integral μ F hH _ hk, hK]

theorem realPart_complex_real_smul (c : ℝ) (A : Matrix m m ℂ) :
    matrixRealCLM ((c : ℂ) • A)=c • matrixRealCLM A := by
  ext i j
  change ((c : ℂ)*A i j).re=c*(A i j).re
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

theorem realPart_adjoint (A : Matrix m m ℂ) : matrixRealCLM Aᴴ=(matrixRealCLM A)ᵀ := by
  ext i j
  simp only [matrixRealCLM_apply, Matrix.conjTranspose_apply, Matrix.transpose_apply,
    Complex.star_def, Complex.conj_re]

variable {T : ℝ} [Fact (0 < T)]
namespace RealMatrixSpectrum
variable (S : RealMatrixSpectrum T m)

def normalSpectralCovariance (a : ℝ) : Matrix m m ℝ :=
  matrixRealCLM (∫ x, normalPowerKernel a (fourier 1 x) • S.F x ∂S.μ)

theorem cross_spectral_moment (a : ℝ) (ha : ‖a‖<1) :
    matrixRealCLM (∫ x, causalCrossKernel a (fourier 1 x) • S.F x ∂S.μ)=S.rankOneK a := by
  unfold causalCrossKernel
  rw [← spectral_generating_resolvent S.μ S.F S.integrable _
    (fourier 1).continuous.measurable (fun x => Circle.norm_coe _) a ha]
  exact (spectral_generating_real S.μ S.F S.integrable _
    (fourier 1).continuous.measurable (fun x => Circle.norm_coe _) a ha).symm

theorem normal_spectral_covariance (a : ℝ) (ha : ‖a‖<1) :
    S.normalSpectralCovariance a=(1-a^2)⁻¹ • S.rankOneC a := by
  unfold normalSpectralCovariance
  rw [normal_power_integral S.μ S.F S.integrable S.hermitian _
    (fourier 1).continuous.measurable (fun x => Circle.norm_coe _) a ha]
  have hc : ((1 : ℂ)-(a : ℂ)^2)⁻¹=(((1-a^2)⁻¹ : ℝ) : ℂ) := by simp
  rw [hc, realPart_complex_real_smul, map_add, realPart_complex_real_smul, map_add,
    realPart_adjoint]
  rw [← spectral_generating_real S.μ S.F S.integrable _
    (fourier 1).continuous.measurable (fun x => Circle.norm_coe _) a ha]
  rfl

end RealMatrixSpectrum
end NoiseResponse.Classification

#print axioms NoiseResponse.Classification.RealMatrixSpectrum.normal_spectral_covariance
