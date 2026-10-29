/- Added by cx on 2026-10-29: continuous test integrals determine
   integrable vector densities, via closed-set approximations and DCT. -/
module

public import NoiseResponse.AbelEndpoints
public import Mathlib.MeasureTheory.Function.AEEqOfIntegral
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
public import Mathlib.Tactic

@[expose] public section
set_option maxRecDepth 1000
set_option maxHeartbeats 3000000
noncomputable section
open MeasureTheory Filter Set
open scoped Topology NNReal
namespace NoiseResponse.Classification
variable {T : ℝ} [Fact (0 < T)]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem density_zero_of_continuous_tests
    (μ : Measure (AddCircle T)) (F : AddCircle T → E) (hF : Integrable F μ)
    (htest : ∀ φ : C(AddCircle T, ℝ), (∫ x, φ x • F x ∂μ)=0) :
    F =ᵐ[μ] 0 := by
  apply ae_eq_zero_of_forall_setIntegral_isClosed_eq_zero hF
  intro s hs
  let δ : ℕ → ℝ := fun n => 1/((n : ℝ)+1)
  have hδ (n : ℕ) : 0 < δ n := by unfold δ; positivity
  have hδlim : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let φ : ℕ → C(AddCircle T, ℝ) := fun n =>
    ⟨fun x => (thickenedIndicator (hδ n) s x : ℝ), by fun_prop⟩
  have hdom := tendsto_integral_of_dominated_convergence (μ := μ)
    (F := fun n x => φ n x • F x) (f := s.indicator F) (fun x => ‖F x‖)
    (fun n => (φ n).continuous.measurable.aestronglyMeasurable.smul hF.aestronglyMeasurable)
    hF.norm
    (fun n => Eventually.of_forall (fun x => by
      rw [norm_smul]
      have hb : ‖φ n x‖ ≤ 1 := by
        change ‖((thickenedIndicator (hδ n) s x : ℝ≥0) : ℝ)‖ ≤ 1
        rw [Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _)]
        exact_mod_cast thickenedIndicator_le_one (hδ n) s x
      exact (mul_le_mul_of_nonneg_right hb (norm_nonneg (F x))).trans_eq (one_mul _)))
    (Eventually.of_forall (fun x => by
      have hp := tendsto_pi_nhds.mp (thickenedIndicator_tendsto_indicator_closure hδ hδlim s) x
      have hp' := (NNReal.continuous_coe.continuousAt.tendsto.comp hp).smul_const (F x)
      by_cases hx : x ∈ s
      · simpa only [φ, ContinuousMap.coe_mk, Function.comp_def, hs.closure_eq, Set.indicator_of_mem hx,
          NNReal.coe_one, one_smul] using hp'
      · simpa only [φ, ContinuousMap.coe_mk, Function.comp_def, hs.closure_eq, Set.indicator_of_notMem hx,
          NNReal.coe_zero, zero_smul] using hp'))
  have hz : Tendsto (fun _ : ℕ => (0 : E)) atTop (𝓝 (∫ x in s, F x ∂μ)) := by
    simpa only [htest, integral_indicator hs.measurableSet] using hdom
  exact tendsto_nhds_unique hz tendsto_const_nhds

end NoiseResponse.Classification

#print axioms NoiseResponse.Classification.density_zero_of_continuous_tests
