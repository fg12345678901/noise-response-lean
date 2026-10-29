/- Added by cx on 2026-10-29: generating-function coefficient
   identification for bounded vector/matrix covariance sequences. -/
module

public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Tactic

@[expose] public section

set_option maxRecDepth 1000
set_option maxHeartbeats 1000000
noncomputable section
open Filter
open scoped Topology NNReal ENNReal
namespace NoiseResponse.Classification
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def covarianceSeries (γ : ℕ → E) : FormalMultilinearSeries ℝ ℝ E :=
  fun n => ContinuousMultilinearMap.mkPiRing ℝ (Fin n) (γ n)

@[simp] theorem covarianceSeries_coeff (γ : ℕ → E) (n : ℕ) :
    (covarianceSeries γ).coeff n = γ n := by
  simp [covarianceSeries, FormalMultilinearSeries.coeff]

def generating (γ : ℕ → E) (a : ℝ) : E := ∑' n : ℕ, a^n • γ n

theorem bounded_covariance_summable (γ : ℕ → E) (C : ℝ)
    (hC : ∀ n, ‖γ n‖ ≤ C) (a : ℝ) (ha : ‖a‖ < 1) :
    Summable (fun n : ℕ => a^n • γ n) := by
  have hg : Summable (fun n : ℕ => ‖a‖^n * C) :=
    (summable_geometric_of_norm_lt_one (by simpa using ha)).mul_right C
  apply Summable.of_norm_bounded hg
  intro n
  rw [norm_smul, norm_pow]
  exact mul_le_mul_of_nonneg_left (hC n) (pow_nonneg (norm_nonneg _) _)

theorem bounded_covariance_hasFPowerSeries (γ : ℕ → E) (C : ℝ)
    (hC : ∀ n, ‖γ n‖ ≤ C) :
    HasFPowerSeriesAt (generating γ) (covarianceSeries γ) 0 := by
  rw [hasFPowerSeriesAt_iff]
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1)] with a ha
  simp only [Metric.mem_ball, dist_zero_right] at ha
  simpa only [zero_add, covarianceSeries_coeff, generating] using
    (bounded_covariance_summable γ C hC a ha).hasSum

theorem bounded_covariance_hasFPowerSeriesOnBall (γ : ℕ → E) (C : ℝ)
    (hC : ∀ n, ‖γ n‖ ≤ C) :
    HasFPowerSeriesOnBall (generating γ) (covarianceSeries γ) 0 1 := by
  refine ⟨?_, by norm_num, ?_⟩
  · apply (covarianceSeries γ).le_radius_of_bound C (r := 1)
    intro n
    simpa [FormalMultilinearSeries.norm_apply_eq_norm_coef] using hC n
  · intro a ha
    have hn : ‖a‖ < 1 := by
      have h' : nndist a 0 < (1 : ℝ≥0) := by
        simpa only [Metric.mem_eball, ← ENNReal.coe_one, edist_lt_coe] using ha
      have h'' : dist a 0 < (1 : ℝ) := by exact_mod_cast h'
      simpa only [dist_zero_right] using h''
    simpa only [FormalMultilinearSeries.apply_eq_pow_smul_coeff,
      covarianceSeries_coeff, zero_add, generating] using
      (bounded_covariance_summable γ C hC a hn).hasSum

theorem bounded_generating_differentiable (γ : ℕ → E) (C : ℝ)
    (hC : ∀ n, ‖γ n‖ ≤ C) (a : ℝ) (ha : ‖a‖ < 1) :
    DifferentiableAt ℝ (generating γ) a := by
  exact ((bounded_covariance_hasFPowerSeriesOnBall γ C hC).analyticAt_of_mem
    (by
      have h' : nndist a 0 < (1 : ℝ≥0) := by
        exact_mod_cast (show dist a 0 < (1 : ℝ) by simpa only [dist_zero_right] using ha)
      simpa only [Metric.mem_eball, ← ENNReal.coe_one, edist_lt_coe] using h')).differentiableAt

/-- Equality on a neighborhood of zero identifies every covariance
    coefficient. No finite truncation or numerical differentiation is used. -/
theorem bounded_generating_eq_coefficients (γ δ : ℕ → E) (C D : ℝ)
    (hγ : ∀ n, ‖γ n‖ ≤ C) (hδ : ∀ n, ‖δ n‖ ≤ D)
    (h : generating γ =ᶠ[𝓝 (0 : ℝ)] generating δ) : γ = δ := by
  have he := (bounded_covariance_hasFPowerSeries γ C hγ).eq_formalMultilinearSeries_of_eventually
    (bounded_covariance_hasFPowerSeries δ D hδ) h
  funext n
  have hc := congrArg (fun p : FormalMultilinearSeries ℝ ℝ E => p.coeff n) he
  simpa only [covarianceSeries_coeff] using hc

def endpointCoefficient (m0 mpi : E) (n : ℕ) : E :=
  m0 - ((-1 : ℝ)^n) • mpi

theorem endpoint_generating (m0 mpi : E) (a : ℝ) (ha : ‖a‖ < 1) :
    generating (endpointCoefficient m0 mpi) a =
      (1-a)⁻¹ • m0 - (1+a)⁻¹ • mpi := by
  have hp := (hasSum_geometric_of_norm_lt_one ha).smul_const m0
  have hm := (hasSum_geometric_of_norm_lt_one (by simpa using ha : ‖-a‖ < 1)).smul_const mpi
  have he (n : ℕ) : a^n • endpointCoefficient m0 mpi n =
      a^n • m0 - (-a)^n • mpi := by
    simp only [endpointCoefficient, smul_sub, smul_smul, ← mul_pow, mul_neg_one]
  exact (by simpa only [he, sub_neg_eq_add] using hp.sub hm :
    HasSum (fun n : ℕ => a^n • endpointCoefficient m0 mpi n)
      ((1-a)⁻¹ • m0 - (1+a)⁻¹ • mpi)).tsum_eq

/-- The pole formula determined by the two endpoint masses identifies
    every positive-lag coefficient, with the Nyquist alternating sign. -/
theorem endpoint_poles_identify_coefficients (γ : ℕ → E) (C : ℝ)
    (hγ : ∀ n, ‖γ n‖ ≤ C) (m0 mpi : E)
    (h : ∀ a ∈ Set.Ioo (-1 : ℝ) 1,
      generating γ a = (1-a)⁻¹ • m0 - (1+a)⁻¹ • mpi) :
    ∀ n : ℕ, γ n = m0 - ((-1 : ℝ)^n) • mpi := by
  have hb : ∀ n, ‖endpointCoefficient m0 mpi n‖ ≤ ‖m0‖ + ‖mpi‖ := by
    intro n
    calc
      _ ≤ ‖m0‖ + ‖((-1 : ℝ)^n) • mpi‖ := norm_sub_le _ _
      _ = _ := by rw [norm_smul, norm_pow]; simp
  have he := bounded_generating_eq_coefficients γ (endpointCoefficient m0 mpi)
    C (‖m0‖+‖mpi‖) hγ hb (by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1)] with a ha
      simp only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at ha
      rw [endpoint_generating m0 mpi a (by simpa [Real.norm_eq_abs] using ha)]
      exact h a (abs_lt.mp ha))
  intro n
  exact congrFun he n

end NoiseResponse.Classification

#print axioms NoiseResponse.Classification.bounded_covariance_hasFPowerSeries
#print axioms NoiseResponse.Classification.bounded_generating_eq_coefficients
#print axioms NoiseResponse.Classification.endpoint_poles_identify_coefficients
