/- Added by cx on 2026-10-29: bounded measurable spectral tests are
   determined by original measurable-set matrix integrals. This avoids
   selecting a density or a control measure as an extra assumption. -/
module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
public import Mathlib.Tactic

@[expose] public section
set_option maxRecDepth 1800
set_option maxHeartbeats 6000000
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace NoiseResponse.SpectralIntegral
variable {Ω E F ι : Type*} [MeasurableSpace Ω]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem simple_pairing_integral (B : E →L[ℝ] F →L[ℝ] ℝ)
    (μ : Measure Ω) (F₀ : Ω → F) (hF : Integrable F₀ μ) (C : SimpleFunc Ω E) :
    (∫ x, B (C x) (F₀ x) ∂μ)=
      ∑ v ∈ C.range, B v (∫ x in C ⁻¹' {v}, F₀ x ∂μ) := by
  classical
  have he (x : Ω) : B (C x) (F₀ x)=
      ∑ v ∈ C.range, (C ⁻¹' {v}).indicator (fun x => B v (F₀ x)) x := by
    rw [Finset.sum_eq_single (C x)]
    · simp
    · intro b hb hbx
      simp only [Set.indicator_of_notMem (show x ∉ C ⁻¹' {b} from fun h => hbx (by simpa using h.symm))]
    · intro hn
      exact (hn (C.mem_range_self x)).elim
  calc
    _ = ∫ x, ∑ v ∈ C.range, (C ⁻¹' {v}).indicator (fun x => B v (F₀ x)) x ∂μ :=
      integral_congr_ae (Eventually.of_forall he)
    _ = ∑ v ∈ C.range, ∫ x, (C ⁻¹' {v}).indicator (fun x => B v (F₀ x)) x ∂μ := by
      rw [integral_finset_sum]
      intro v hv
      exact ((B v).integrable_comp hF).indicator (C.measurableSet_fiber v)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [integral_indicator (C.measurableSet_fiber v),
        (B v).integral_comp_comm hF.integrableOn]

theorem bounded_pairing_limit (B : E →L[ℝ] F →L[ℝ] ℝ)
    (μ : Measure Ω) (F₀ : Ω → F) (hF : Integrable F₀ μ)
    (C : Ω → E) (hC : StronglyMeasurable C) (c : ℝ) (hc : 0 ≤ c) (hb : ∀ x, ‖C x‖ ≤ c) :
    Tendsto (fun k => ∫ x, B (hC.approxBounded c k x) (F₀ x) ∂μ) atTop
      (𝓝 (∫ x, B (C x) (F₀ x) ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => (‖B‖*c)*‖F₀ x‖)
  · intro k
    exact B.aestronglyMeasurable_comp₂
      (hC.approxBounded c k).stronglyMeasurable.aestronglyMeasurable hF.1
  · exact hF.norm.const_mul (‖B‖*c)
  · intro k
    apply Eventually.of_forall
    intro x
    calc
      _ ≤ ‖B (hC.approxBounded c k x)‖*‖F₀ x‖ := (B _).le_opNorm _
      _ ≤ (‖B‖*‖hC.approxBounded c k x‖)*‖F₀ x‖ :=
        mul_le_mul_of_nonneg_right (B.le_opNorm _) (norm_nonneg _)
      _ ≤ _ := by gcongr; exact hC.norm_approxBounded_le hc k x
  · apply Eventually.of_forall
    intro x
    exact (B.continuous₂.tendsto (C x,F₀ x)).comp
      ((hC.tendsto_approxBounded_of_norm_le (hb x)).prodMk_nhds tendsto_const_nhds)

theorem bounded_pairing_finite_split [Fintype ι]
    (B : E →L[ℝ] F →L[ℝ] ℝ) (μ : Measure Ω) (F₀ : Ω → F) (hF : Integrable F₀ μ)
    (ν : ι → Measure Ω) (G : ι → Ω → F) (hG : ∀ i, Integrable (G i) (ν i))
    (hsets : ∀ s : Set Ω, MeasurableSet s →
      (∫ x in s, F₀ x ∂μ)=∑ i, ∫ x in s, G i x ∂ν i)
    (C : Ω → E) (hC : StronglyMeasurable C) (c : ℝ) (hc : 0 ≤ c) (hb : ∀ x, ‖C x‖ ≤ c) :
    (∫ x, B (C x) (F₀ x) ∂μ)=∑ i, ∫ x, B (C x) (G i x) ∂ν i := by
  have hsimple (S : SimpleFunc Ω E) :
      (∫ x, B (S x) (F₀ x) ∂μ)=∑ i, ∫ x, B (S x) (G i x) ∂ν i := by
    classical
    rw [simple_pairing_integral B μ F₀ hF S]
    simp_rw [simple_pairing_integral B _ _ (hG _) S]
    simp_rw [hsets _ (S.measurableSet_fiber _),map_sum]
    exact Finset.sum_comm
  have hleft := bounded_pairing_limit B μ F₀ hF C hC c hc hb
  have hright := tendsto_finsetSum Finset.univ
    (fun i _ => bounded_pairing_limit B (ν i) (G i) (hG i) C hC c hc hb)
  exact tendsto_nhds_unique_of_eventuallyEq hleft hright
    (Eventually.of_forall (fun k => hsimple (hC.approxBounded c k)))

end NoiseResponse.SpectralIntegral
