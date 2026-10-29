/- Added by cx on 2026-10-29: interchange the actual spectral integral
   and causal covariance generating series, including both atom limits. -/
module

public import NoiseResponse.AbelEndpoints
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Tactic

@[expose] public section

set_option maxRecDepth 1000
set_option maxHeartbeats 2000000
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace NoiseResponse.Classification
variable {Ω E : Type*} [MeasurableSpace Ω]
variable [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

def spectralCovariance (μ : Measure Ω) (f : Ω → E) (z : Ω → ℂ) (n : ℕ) :=
  ∫ x, (z x)^(n+1) • f x ∂μ

def spectralGenerating (μ : Measure Ω) (f : Ω → E) (z : Ω → ℂ) (a : ℝ) :=
  ∑' n : ℕ, (a : ℂ)^n • spectralCovariance μ f z n

theorem spectral_generating_resolvent
    (μ : Measure Ω) (f : Ω → E) (hf : Integrable f μ)
    (z : Ω → ℂ) (hz : Measurable z) (hzunit : ∀ x, ‖z x‖ = 1)
    (a : ℝ) (ha : ‖a‖ < 1) :
    spectralGenerating μ f z a = ∫ x, (z x/(1-(a : ℂ)*z x)) • f x ∂μ := by
  let F : ℕ → Ω → E := fun n x => (((a : ℂ)*z x)^n*z x) • f x
  have hn (n : ℕ) (x : Ω) : ‖F n x‖ = ‖a‖^n*‖f x‖ := by
    simp [F, norm_smul, norm_mul, norm_pow, hzunit x]
  have hm (n : ℕ) : AEStronglyMeasurable (fun x => ((a : ℂ)*z x)^n*z x) μ := by
    apply Measurable.aestronglyMeasurable
    fun_prop
  have hF (n : ℕ) : Integrable (F n) μ := by
    apply hf.bdd_smul (‖a‖^n) (hm n)
    exact Eventually.of_forall (fun x => by
      simp [norm_mul, norm_pow, hzunit x])
  have hnorm : Summable (fun n : ℕ => ∫ x, ‖F n x‖ ∂μ) := by
    have hint (n : ℕ) : (∫ x, ‖F n x‖ ∂μ) = ‖a‖^n * (∫ x, ‖f x‖ ∂μ) := by
      calc
        _ = ∫ x, ‖a‖^n * ‖f x‖ ∂μ :=
          integral_congr_ae (Eventually.of_forall (hn n))
        _ = _ := integral_const_mul _ _
    simpa only [hint] using
      (summable_geometric_of_norm_lt_one (by simpa using ha)).mul_right (∫ x, ‖f x‖ ∂μ)
  have hterm (n : ℕ) : (∫ x, F n x ∂μ) =
      (a : ℂ)^n • spectralCovariance μ f z n := by
    unfold F spectralCovariance
    rw [← integral_smul]
    congr 1
    funext x
    rw [smul_smul, mul_pow, pow_succ]
    congr 1
    ring
  have hsum (x : Ω) : (∑' n : ℕ, F n x) =
      (z x/(1-(a : ℂ)*z x)) • f x := by
    have hg : ‖(a : ℂ)*z x‖ < 1 := by simpa [norm_mul, hzunit x] using ha
    have hs := ((hasSum_geometric_of_norm_lt_one hg).mul_right (z x)).smul_const (f x)
    simpa only [F, div_eq_mul_inv, mul_comm] using hs.tsum_eq
  have hi := integral_tsum_of_summable_integral_norm hF hnorm
  simpa only [hterm, hsum, spectralGenerating] using hi

/-- Extract the actual zero-frequency atom directly from the covariance
    generating function, rather than assuming an Abel limit for it. -/
theorem spectral_generating_zero_endpoint
    (μ : Measure Ω) (f : Ω → E) (hf : Integrable f μ)
    (z : Ω → ℂ) (hz : Measurable z) (hzunit : ∀ x, ‖z x‖ = 1)
    (a : ℕ → ℝ) (ha₀ : ∀ k, 0 ≤ a k) (ha₁ : ∀ k, a k < 1)
    (ha : Tendsto a atTop (𝓝 1)) :
    Tendsto (fun k => ((1 : ℂ)-(a k : ℂ)) • spectralGenerating μ f z (a k))
      atTop (𝓝 (∫ x in {x | z x = 1}, f x ∂μ)) := by
  have he (k : ℕ) : ((1 : ℂ)-(a k : ℂ)) • spectralGenerating μ f z (a k) =
      ∫ x, abelKernel (a k) (z x) • f x ∂μ := by
    rw [spectral_generating_resolvent μ f hf z hz hzunit (a k)
      (by simpa [Real.norm_eq_abs, abs_of_nonneg (ha₀ k)] using ha₁ k), ← integral_smul]
    congr 1
    funext x
    simp only [abelKernel, smul_smul, mul_div_assoc]
  simpa only [he] using abel_integral_endpoint μ f hf z hz hzunit a ha₀ ha₁ ha

theorem spectral_generating_nyquist_endpoint
    (μ : Measure Ω) (f : Ω → E) (hf : Integrable f μ)
    (z : Ω → ℂ) (hz : Measurable z) (hzunit : ∀ x, ‖z x‖ = 1)
    (a : ℕ → ℝ) (ha₀ : ∀ k, a k ≤ 0) (ha₁ : ∀ k, -1 < a k)
    (ha : Tendsto a atTop (𝓝 (-1))) :
    Tendsto (fun k => ((1 : ℂ)+(a k : ℂ)) • spectralGenerating μ f z (a k))
      atTop (𝓝 (-(∫ x in {x | z x = -1}, f x ∂μ))) := by
  have he (k : ℕ) : ((1 : ℂ)+(a k : ℂ)) • spectralGenerating μ f z (a k) =
      ∫ x, (((1 : ℂ)+(a k : ℂ))*z x/(1-(a k : ℂ)*z x)) • f x ∂μ := by
    rw [spectral_generating_resolvent μ f hf z hz hzunit (a k)
      (by rw [Real.norm_eq_abs, abs_of_nonpos (ha₀ k)]; linarith [ha₁ k]), ← integral_smul]
    congr 1
    funext x
    simp only [smul_smul, mul_div_assoc]
  simpa only [he] using abel_integral_nyquist μ f hf z hz hzunit a ha₀ ha₁ ha

end NoiseResponse.Classification

#print axioms NoiseResponse.Classification.spectral_generating_resolvent
#print axioms NoiseResponse.Classification.spectral_generating_zero_endpoint
#print axioms NoiseResponse.Classification.spectral_generating_nyquist_endpoint
