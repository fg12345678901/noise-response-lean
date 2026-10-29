/- Added by cx on 2026-10-29: actual spectral integrals supply the
   real covariance generator and its two endpoint limits. -/
module

public import NoiseResponse.NativeCovarianceNecessity
public import NoiseResponse.SpectralResolvent
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic

@[expose] public section
set_option maxRecDepth 1000
set_option maxHeartbeats 2000000
noncomputable section
open MeasureTheory Filter Set Matrix
open scoped Topology Matrix.Norms.Elementwise
attribute [local instance] matrixNormTopology
namespace NoiseResponse.Classification
variable {m Ω : Type*} [Fintype m] [DecidableEq m] [Nonempty m] [MeasurableSpace Ω]

def matrixRealCLM : Matrix m m ℂ →L[ℝ] Matrix m m ℝ :=
  (show Matrix m m ℂ →ₗ[ℝ] Matrix m m ℝ from
    { toFun := fun A i j => (A i j).re
      map_add' := by
        intro A B
        funext i j
        change (A i j+B i j).re = (A i j).re+(B i j).re
        exact Complex.add_re _ _
      map_smul' := by
        intro c A
        funext i j
        change (c • A i j).re = c • (A i j).re
        simp }).toContinuousLinearMap

@[simp] theorem matrixRealCLM_apply (A : Matrix m m ℂ) (i j : m) :
    matrixRealCLM A i j = (A i j).re := rfl

theorem spectral_covariance_bound
    (μ : Measure Ω) (f : Ω → Matrix m m ℂ) (hf : Integrable f μ)
    (z : Ω → ℂ) (hz : Measurable z) (hzunit : ∀ x, ‖z x‖ = 1) (n : ℕ) :
    ‖spectralCovariance μ f z n‖ ≤ ∫ x, ‖f x‖ ∂μ := by
  apply norm_integral_le_of_norm_le hf.norm
  exact Eventually.of_forall (fun x => by simp [norm_smul, norm_pow, hzunit x])

theorem spectral_generating_real (μ : Measure Ω) (f : Ω → Matrix m m ℂ)
    (hf : Integrable f μ) (z : Ω → ℂ) (hz : Measurable z)
    (hzunit : ∀ x, ‖z x‖ = 1) (a : ℝ) (ha : ‖a‖ < 1) :
    generating (fun n => matrixRealCLM (spectralCovariance μ f z n)) a =
      matrixRealCLM (spectralGenerating μ f z a) := by
  have he : generating (spectralCovariance μ f z) a = spectralGenerating μ f z a := by
    unfold generating spectralGenerating
    congr 1
    funext n
    ext i j
    simp [Complex.ofReal_pow]
  rw [generating_map (spectralCovariance μ f z) (∫ x, ‖f x‖ ∂μ)
    (spectral_covariance_bound μ f hf z hz hzunit) matrixRealCLM a ha, he]

/-- The endpoint limits in the covariance necessity theorem are derived
    from actual integrals. Symmetry of the two real atom matrices is a
    structural reality condition on the input spectral representation. -/
theorem spectral_integral_covariance_necessity
    (μ : Measure Ω) (f : Ω → Matrix m m ℂ) (hf : Integrable f μ)
    (z : Ω → ℂ) (hz : Measurable z) (hzunit : ∀ x, ‖z x‖ = 1)
    (η : ℝ) (hη : 0 < η)
    (hΓ0 : (matrixRealCLM (∫ x, f x ∂μ))ᵀ = matrixRealCLM (∫ x, f x ∂μ))
    (hM0 : (matrixRealCLM (∫ x in {x | z x = 1}, f x ∂μ))ᵀ =
      matrixRealCLM (∫ x in {x | z x = 1}, f x ∂μ))
    (hMpi : (matrixRealCLM (∫ x in {x | z x = -1}, f x ∂μ))ᵀ =
      matrixRealCLM (∫ x in {x | z x = -1}, f x ∂μ))
    (hp : ∀ u v, OrthonormalProbePair u v →
      (covariancePair (fun n => matrixRealCLM (spectralCovariance μ f z n))
        (matrixRealCLM (∫ x, f x ∂μ))
        (‖(matrixRealCLM : Matrix m m ℂ →L[ℝ] Matrix m m ℝ)‖ * ∫ x, ‖f x‖ ∂μ)
        (by positivity)
        (fun n => le_trans (matrixRealCLM.le_opNorm _) (mul_le_mul_of_nonneg_left
          (spectral_covariance_bound μ f hf z hz hzunit n) (norm_nonneg _))) u v).AllAxisPotentials η) :
    (∃ c0 : ℝ, matrixRealCLM (∫ x, f x ∂μ) =
      matrixRealCLM (∫ x in {x | z x = 1}, f x ∂μ) +
      matrixRealCLM (∫ x in {x | z x = -1}, f x ∂μ) + c0 • (1 : Matrix m m ℝ)) ∧
    ∀ n, ∃ cn : ℝ, matrixRealCLM (spectralCovariance μ f z n) =
      matrixRealCLM (∫ x in {x | z x = 1}, f x ∂μ) -
      ((-1 : ℝ)^n) • matrixRealCLM (∫ x in {x | z x = -1}, f x ∂μ) +
      cn • (1 : Matrix m m ℝ) := by
  apply matrix_generating_necessity _ _ _ _ hΓ0 hM0 hMpi _ (by positivity) _ η hη hp
  · have ht := (matrixRealCLM : Matrix m m ℂ →L[ℝ] Matrix m m ℝ).continuous.continuousAt.tendsto.comp
      (spectral_generating_zero_endpoint μ f hf z hz hzunit positiveEndpointPath
        (fun k => (positiveEndpointPath_bounds k).1)
        (fun k => (positiveEndpointPath_bounds k).2) positiveEndpointPath_tendsto)
    convert ht using 1
    funext k
    dsimp only [Function.comp_def]
    rw [spectral_generating_real μ f hf z hz hzunit _
      (by simpa only [Real.norm_eq_abs] using abs_lt.mpr (positiveEndpointPath_mem k))]
    change (1-positiveEndpointPath k) • matrixRealCLM _ =
      matrixRealCLM (((1 : ℂ)-(positiveEndpointPath k : ℂ)) • _)
    rw [show (1 : ℂ)-(positiveEndpointPath k : ℂ) = ((1-positiveEndpointPath k : ℝ) : ℂ) by simp]
    ext i j
    simp only [matrixRealCLM_apply, Matrix.smul_apply, smul_eq_mul,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  · have ht := (matrixRealCLM : Matrix m m ℂ →L[ℝ] Matrix m m ℝ).continuous.continuousAt.tendsto.comp
      (spectral_generating_nyquist_endpoint μ f hf z hz hzunit negativeEndpointPath
        (fun k => by unfold negativeEndpointPath; linarith [(positiveEndpointPath_bounds k).1])
        (fun k => (negativeEndpointPath_mem k).1) negativeEndpointPath_tendsto)
    simp only [map_neg] at ht
    convert ht using 1
    funext k
    dsimp only [Function.comp_def]
    rw [spectral_generating_real μ f hf z hz hzunit _
      (by simpa only [Real.norm_eq_abs] using abs_lt.mpr (negativeEndpointPath_mem k))]
    change (1+negativeEndpointPath k) • matrixRealCLM _ =
      matrixRealCLM (((1 : ℂ)+(negativeEndpointPath k : ℂ)) • _)
    rw [show (1 : ℂ)+(negativeEndpointPath k : ℂ) = ((1+negativeEndpointPath k : ℝ) : ℂ) by simp]
    ext i j
    simp only [matrixRealCLM_apply, Matrix.smul_apply, smul_eq_mul,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

end NoiseResponse.Classification

#print axioms NoiseResponse.Classification.spectral_integral_covariance_necessity
