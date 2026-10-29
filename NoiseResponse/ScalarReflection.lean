/- Added by cx on 2026-10-29: actual finite scalar measures with real
   Fourier coefficients are reflection invariant. -/
module

public import NoiseResponse.ScalarSpectralMeasure
public import Mathlib.Tactic

@[expose] public section
noncomputable section
open MeasureTheory Complex
open scoped Topology ComplexConjugate
namespace NoiseResponse.Classification
variable {T : ℝ} [Fact (0 < T)]

theorem real_fourier_implies_reflection
    (ν : Measure (AddCircle T)) [IsFiniteMeasure ν]
    (hreal : ∀ n : ℤ, (∫ x, fourier n x ∂ν).im=0) :
    ν.map (fun x => -x) = ν := by
  apply finite_measure_eq_of_fourier
  intro n
  rw [integral_map measurable_neg.aemeasurable
    (fourier n).continuous.measurable.aestronglyMeasurable]
  have he (x : AddCircle T) : fourier n (-x) = conj (fourier n x) := by
    rw [← fourier_neg]
    simp only [fourier_apply, smul_neg, neg_smul]
  simp_rw [he]
  rw [integral_conj]
  apply Complex.ext
  · exact Complex.conj_re _
  · change -(∫ x, fourier n x ∂ν).im = (∫ x, fourier n x ∂ν).im
    rw [hreal n]
    exact neg_zero

end NoiseResponse.Classification

#print axioms NoiseResponse.Classification.real_fourier_implies_reflection
