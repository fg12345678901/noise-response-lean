/- Added by cx on 2026-10-29.
   V6 equations (B3)/(B7): endpoint extraction for integrable vector-valued
   spectral densities with an arbitrary positive base measure.
-/
module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic

@[expose] public section

set_option maxRecDepth 2000
set_option maxHeartbeats 1000000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology

namespace NoiseResponse
namespace Classification

def abelKernel (a : ℝ) (z : ℂ) : ℂ :=
  (1 - (a : ℂ)) * z / (1 - (a : ℂ) * z)

/-- The exact domination used to extract a zero-frequency atom. -/
theorem abelKernel_norm_le_one (a : ℝ) (z : ℂ)
    (ha₀ : 0 ≤ a) (ha₁ : a < 1) (hz : ‖z‖ = 1) :
    ‖abelKernel a z‖ ≤ 1 := by
  have hd : 1 - a ≤ ‖(1 : ℂ) - (a : ℂ) * z‖ := by
    calc
      1 - a = ‖(1 : ℂ)‖ - ‖(a : ℂ) * z‖ := by
        simp [norm_mul, hz, abs_of_nonneg ha₀]
      _ ≤ ‖(1 : ℂ) - (a : ℂ) * z‖ := norm_sub_norm_le _ _
  have hdpos : 0 < ‖(1 : ℂ) - (a : ℂ) * z‖ :=
    lt_of_lt_of_le (sub_pos.mpr ha₁) hd
  have hn : ‖(1 : ℂ) - (a : ℂ)‖ = 1 - a := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real]
    exact abs_of_pos (sub_pos.mpr ha₁)
  simpa only [abelKernel, norm_div, norm_mul, hn, hz, mul_one] using
    (div_le_one hdpos).mpr hd

/-- The pointwise endpoint limit includes the atom, not only the punctured circle. -/
theorem abelKernel_tendsto (a : ℕ → ℝ) (ha₁ : ∀ k, a k < 1)
    (ha : Tendsto a atTop (𝓝 1)) (z : ℂ) :
    Tendsto (fun k => abelKernel (a k) z) atTop
      (𝓝 (if z = 1 then (1 : ℂ) else 0)) := by
  have hac : Tendsto (fun k => (a k : ℂ)) atTop (𝓝 (1 : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp ha
  by_cases hz : z = 1
  · subst z
    have hk : ∀ k, abelKernel (a k) 1 = 1 := by
      intro k
      have h : (1 : ℂ) - (a k : ℂ) ≠ 0 := by
        apply sub_ne_zero.mpr
        exact_mod_cast (ne_of_gt (ha₁ k))
      simp [abelKernel, h]
    simpa [hk] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℂ)) atTop (𝓝 1))
  · have hd : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
    have h : Tendsto (fun k => ((1 : ℂ) - (a k : ℂ)) * z /
        ((1 : ℂ) - (a k : ℂ) * z)) atTop
        (𝓝 (((1 : ℂ) - 1) * z / ((1 : ℂ) - 1 * z))) :=
      (((tendsto_const_nhds (x := (1 : ℂ))).sub hac).mul
      (tendsto_const_nhds (x := z))).div
      ((tendsto_const_nhds (x := (1 : ℂ))).sub
        (hac.mul (tendsto_const_nhds (x := z))))
      (by simpa using hd)
    simpa [abelKernel, hz, Pi.div_apply] using h

variable {Ω E : Type*} [MeasurableSpace Ω]
variable [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- Dominated convergence extracts exactly the spectral mass at z=1.
    Matrices are an instance of the arbitrary complex Banach-space output. -/
theorem abel_integral_endpoint
    (μ : Measure Ω) (f : Ω → E) (hf : Integrable f μ)
    (z : Ω → ℂ) (hz : Measurable z) (hzunit : ∀ x, ‖z x‖ = 1)
    (a : ℕ → ℝ) (ha₀ : ∀ k, 0 ≤ a k) (ha₁ : ∀ k, a k < 1)
    (ha : Tendsto a atTop (𝓝 1)) :
    Tendsto (fun k => ∫ x, abelKernel (a k) (z x) • f x ∂μ)
      atTop (𝓝 (∫ x in {x | z x = 1}, f x ∂μ)) := by
  have hset : MeasurableSet {x | z x = 1} := measurableSet_eq_fun hz measurable_const
  have hm : ∀ k, Measurable (fun x => abelKernel (a k) (z x)) := by
    intro k
    unfold abelKernel
    fun_prop
  have hdom := tendsto_integral_of_dominated_convergence (μ := μ)
    (F := fun k x => abelKernel (a k) (z x) • f x)
    (f := {x | z x = 1}.indicator f) (fun x => ‖f x‖)
    (fun k => (hm k).aestronglyMeasurable.smul hf.aestronglyMeasurable)
    hf.norm
    (fun k => Filter.Eventually.of_forall (fun x => by
      rw [norm_smul]
      exact (mul_le_mul_of_nonneg_right
        (abelKernel_norm_le_one (a k) (z x) (ha₀ k) (ha₁ k) (hzunit x))
        (norm_nonneg (f x))).trans_eq (one_mul _)))
    (Filter.Eventually.of_forall (fun x => by
      have h := (abelKernel_tendsto a ha₁ ha (z x)).smul_const (f x)
      by_cases hx : z x = 1
      · simpa [hx] using h
      · simpa [hx] using h))
  simpa only [integral_indicator hset] using hdom

/-- The second endpoint has a minus sign: (1+a)K(a) tends to -M_pi.
    This is the Nyquist endpoint, not a second copy of the zero endpoint. -/
theorem abel_integral_nyquist
    (μ : Measure Ω) (f : Ω → E) (hf : Integrable f μ)
    (z : Ω → ℂ) (hz : Measurable z) (hzunit : ∀ x, ‖z x‖ = 1)
    (a : ℕ → ℝ) (ha₀ : ∀ k, a k ≤ 0) (ha₁ : ∀ k, -1 < a k)
    (ha : Tendsto a atTop (𝓝 (-1))) :
    Tendsto (fun k => ∫ x,
        (((1 : ℂ) + (a k : ℂ)) * z x / (1 - (a k : ℂ) * z x)) • f x ∂μ)
      atTop (𝓝 (-(∫ x in {x | z x = -1}, f x ∂μ))) := by
  have h := abel_integral_endpoint μ f hf (fun x => -z x) hz.neg
    (fun x => by simpa using hzunit x) (fun k => -a k)
    (fun k => neg_nonneg.mpr (ha₀ k)) (fun k => by linarith [ha₁ k])
    (by simpa using ha.neg)
  have hk (b : ℝ) (w : ℂ) :
      ((1 : ℂ) + (b : ℂ)) * w / (1 - (b : ℂ) * w) =
        -abelKernel (-b) (-w) := by
    simp [abelKernel, neg_div]
  have he : {x | -z x = 1} = {x | z x = -1} := by
    ext x; simp [neg_eq_iff_eq_neg]
  simpa only [he, hk, neg_smul, integral_neg] using h.neg

end Classification
end NoiseResponse

#print axioms NoiseResponse.Classification.abelKernel_norm_le_one
#print axioms NoiseResponse.Classification.abelKernel_tendsto
#print axioms NoiseResponse.Classification.abel_integral_endpoint
#print axioms NoiseResponse.Classification.abel_integral_nyquist
