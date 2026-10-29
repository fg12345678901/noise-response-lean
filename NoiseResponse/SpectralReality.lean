/- Added by cx on 2026-10-29: real covariance coefficients force
   real endpoint masses through the two actual Abel limits. -/
module

public import NoiseResponse.SpectralNativeBridge
public import NoiseResponse.IntegerSpectralAssembly
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

def matrixComplexifyCLM : Matrix m m ℝ →L[ℝ] Matrix m m ℂ :=
  (show Matrix m m ℝ →ₗ[ℝ] Matrix m m ℂ from
    { toFun := complexifyMatrix
      map_add' := complexifyMatrix_add
      map_smul' := by
        intro c A
        ext i j
        exact Complex.ofReal_mul _ _ }).toContinuousLinearMap

@[simp] theorem matrixComplexifyCLM_apply (A : Matrix m m ℝ) :
    matrixComplexifyCLM A = complexifyMatrix A := rfl

def realityProjection : Matrix m m ℂ →L[ℝ] Matrix m m ℂ :=
  matrixComplexifyCLM.comp matrixRealCLM

@[simp] theorem realityProjection_apply (A : Matrix m m ℂ) :
    realityProjection A = complexifyMatrix (matrixRealCLM A) := rfl

theorem spectralGenerating_eq_generating
    (μ : Measure Ω) (f : Ω → Matrix m m ℂ) (z : Ω → ℂ) (a : ℝ) :
    spectralGenerating μ f z a = generating (spectralCovariance μ f z) a := by
  unfold spectralGenerating generating
  congr 1
  funext n
  ext i j
  simp

theorem generating_preserves_reality
    (Γ : ℕ → Matrix m m ℂ) (B : ℝ) (hB : ∀ n, ‖Γ n‖ ≤ B)
    (hreal : ∀ n, realityProjection (Γ n) = Γ n) (a : ℝ) (ha : ‖a‖ < 1) :
    realityProjection (generating Γ a) = generating Γ a := by
  rw [← generating_map Γ B hB realityProjection a ha]
  congr 1
  funext n
  exact hreal n

theorem generating_limit_is_real
    (Γ : ℕ → Matrix m m ℂ) (B : ℝ) (hB : ∀ n, ‖Γ n‖ ≤ B)
    (hreal : ∀ n, realityProjection (Γ n)=Γ n)
    (a w : ℕ → ℝ) (ha : ∀ k, ‖a k‖ < 1) (M : Matrix m m ℂ)
    (hlim : Tendsto (fun k => w k • generating Γ (a k)) atTop (𝓝 M)) :
    realityProjection M = M := by
  have hp := realityProjection.continuous.continuousAt.tendsto.comp hlim
  have he (k : ℕ) : realityProjection (w k • generating Γ (a k)) =
      w k • generating Γ (a k) := by
    rw [map_smul, generating_preserves_reality Γ B hB hreal _ (ha k)]
  have hp' : Tendsto (fun k => w k • generating Γ (a k)) atTop
      (𝓝 (realityProjection M)) := by
    simpa only [Function.comp_def, he] using hp
  exact tendsto_nhds_unique hp' hlim

theorem spectral_endpoint_masses_real
    (μ : Measure Ω) (f : Ω → Matrix m m ℂ) (hf : Integrable f μ)
    (z : Ω → ℂ) (hz : Measurable z) (hzunit : ∀ x, ‖z x‖=1)
    (hreal : ∀ n, realityProjection (spectralCovariance μ f z n) =
      spectralCovariance μ f z n) :
    realityProjection (∫ x in {x | z x=1}, f x ∂μ) = (∫ x in {x | z x=1}, f x ∂μ) ∧
    realityProjection (∫ x in {x | z x = -1}, f x ∂μ) = (∫ x in {x | z x = -1}, f x ∂μ) := by
  have hn (a : ℝ) (ha : a ∈ Ioo (-1 : ℝ) 1) : ‖a‖ < 1 := by
    simpa only [Real.norm_eq_abs] using abs_lt.mpr ha
  constructor
  · have ht := spectral_generating_zero_endpoint μ f hf z hz hzunit positiveEndpointPath
      (fun k => (positiveEndpointPath_bounds k).1)
      (fun k => (positiveEndpointPath_bounds k).2) positiveEndpointPath_tendsto
    have he (k : ℕ) : ((1 : ℂ)-(positiveEndpointPath k : ℂ)) •
        spectralGenerating μ f z (positiveEndpointPath k) =
        (1-positiveEndpointPath k) • generating (spectralCovariance μ f z) (positiveEndpointPath k) := by
      rw [spectralGenerating_eq_generating]
      ext i j
      simp
    simp only [he] at ht
    exact generating_limit_is_real _ _ (spectral_covariance_bound μ f hf z hz hzunit) hreal
      _ _ (fun k => hn _ (positiveEndpointPath_mem k)) _ ht
  · have ht := spectral_generating_nyquist_endpoint μ f hf z hz hzunit negativeEndpointPath
      (fun k => by unfold negativeEndpointPath; linarith [(positiveEndpointPath_bounds k).1])
      (fun k => (negativeEndpointPath_mem k).1) negativeEndpointPath_tendsto
    have he (k : ℕ) : ((1 : ℂ)+(negativeEndpointPath k : ℂ)) •
        spectralGenerating μ f z (negativeEndpointPath k) =
        (1+negativeEndpointPath k) • generating (spectralCovariance μ f z) (negativeEndpointPath k) := by
      rw [spectralGenerating_eq_generating]
      ext i j
      simp
    simp only [he] at ht
    have h := generating_limit_is_real _ _ (spectral_covariance_bound μ f hf z hz hzunit) hreal
      _ _ (fun k => hn _ (negativeEndpointPath_mem k)) _ ht
    simpa only [map_neg, neg_inj] using h

end NoiseResponse.Classification

#print axioms NoiseResponse.Classification.spectral_endpoint_masses_real
