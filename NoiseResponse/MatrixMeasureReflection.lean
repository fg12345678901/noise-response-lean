/- Added by cx on 2026-10-29: the literal reflection law on a matrix
   measure induces a symmetric trace measure, conjugate RN density,
   and real Fourier covariances. -/
module

public import NoiseResponse.MatrixSpectrumRepresentation
public import Mathlib.MeasureTheory.Group.MeasurableEquiv
public import Mathlib.Tactic

@[expose] public section
set_option maxRecDepth 1000
set_option maxHeartbeats 3000000
noncomputable section
open MeasureTheory Filter Set Matrix Complex
open scoped Topology Matrix.Norms.Elementwise ComplexOrder MeasureTheory ComplexConjugate
attribute [local instance] matrixNormTopology
namespace NoiseResponse.Classification
variable {m : Type*} [Fintype m] [DecidableEq m] [Nonempty m]
variable {T : ℝ} [Fact (0 < T)]

def matrixConjugateCLM : Matrix m m ℂ →L[ℝ] Matrix m m ℂ :=
  (show Matrix m m ℂ →ₗ[ℝ] Matrix m m ℂ from
    { toFun := fun A i j => star (A i j)
      map_add' := by intro A B; ext i j; exact star_add _ _
      map_smul' := by
        intro c A
        funext i j
        change star (c • A i j)=c • star (A i j)
        simp }).toContinuousLinearMap

@[simp] theorem matrixConjugateCLM_apply (A : Matrix m m ℂ) (i j : m) :
    matrixConjugateCLM A i j=star (A i j) := rfl

@[simp] theorem matrixConjugateCLM_twice (A : Matrix m m ℂ) :
    matrixConjugateCLM (matrixConjugateCLM A)=A := by ext i j; simp

theorem matrixConjugateCLM_complex_smul (c : ℂ) (A : Matrix m m ℂ) :
    matrixConjugateCLM (c • A)=star c • matrixConjugateCLM A := by
  ext i j
  simp only [matrixConjugateCLM_apply, Matrix.smul_apply, smul_eq_mul, star_mul]
  ring

theorem conjugate_fixed_implies_real (A : Matrix m m ℂ) (h : matrixConjugateCLM A=A) :
    realityProjection A=A := by
  ext i j
  have he := congrArg (fun B : Matrix m m ℂ => (B i j).im) h
  simp only [matrixConjugateCLM_apply, Complex.star_def, Complex.conj_im] at he
  have hz : (A i j).im=0 := by linarith
  apply Complex.ext
  · rfl
  · simpa only [realityProjection_apply, complexifyMatrix, Complex.ofReal_im] using hz.symm

namespace PSDMatrixMeasure
variable (M : PSDMatrixMeasure (AddCircle T) m)

def RealReflection : Prop := ∀ s : Set (AddCircle T), MeasurableSet s →
  M.value ((fun x => -x) ⁻¹' s)=matrixConjugateCLM (M.value s)

theorem trace_reflection (hr : M.RealReflection) :
    M.traceMeasure.map (fun x => -x)=M.traceMeasure := by
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply measurable_neg hs]
  have he : M.traceMeasure.real ((fun x => -x) ⁻¹' s)=M.traceMeasure.real s := by
    rw [M.traceMeasure_real _ (measurable_neg hs), M.traceMeasure_real s hs, hr s hs]
    simp only [Matrix.trace, Complex.re_sum, Matrix.diag_apply, matrixConjugateCLM_apply,
      Complex.star_def, Complex.conj_re]
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp he

theorem trace_neg_preserving (hr : M.RealReflection) :
    MeasurePreserving (fun x : AddCircle T => -x) M.traceMeasure M.traceMeasure :=
  ⟨measurable_neg, M.trace_reflection hr⟩

theorem density_reflection (hr : M.RealReflection) :
    ∀ᵐ x ∂M.traceMeasure, M.density (-x)=matrixConjugateCLM (M.density x) := by
  have hp := M.trace_neg_preserving hr
  have hneg := hp.integrable_comp_of_integrable M.density_integrable
  have hg := matrixConjugateCLM.integrable_comp hneg
  have he : (fun x => matrixConjugateCLM (M.density (-x))) =ᵐ[M.traceMeasure] M.density := by
    apply M.trace_density_unique _ hg
    intro s hs
    rw [matrixConjugateCLM.integral_comp_comm (hneg.integrableOn (s := s))]
    dsimp only [Function.comp_def]
    have hn := hp.setIntegral_preimage_emb (MeasurableEquiv.neg (AddCircle T)).measurableEmbedding
      (fun x => M.density (-x)) s
    simp only [neg_neg] at hn
    rw [← hn, M.density_matrix_integral _ (measurable_neg hs), hr s hs,
      matrixConjugateCLM_twice]
  filter_upwards [he] with x hx
  have hc := congrArg matrixConjugateCLM hx
  simpa only [matrixConjugateCLM_twice] using hc

theorem real_fourier_covariances (hr : M.RealReflection) (n : ℤ) :
    realityProjection (densityTest M.traceMeasure M.density M.density_integrable (fourier n)) =
      densityTest M.traceMeasure M.density M.density_integrable (fourier n) := by
  apply conjugate_fixed_implies_real
  change matrixConjugateCLM (∫ x, fourier n x • M.density x ∂M.traceMeasure) =
    ∫ x, fourier n x • M.density x ∂M.traceMeasure
  rw [← matrixConjugateCLM.integral_comp_comm
    (integrable_test_smul _ _ M.density_integrable (fourier n))]
  have he (x : AddCircle T) : fourier n (-x)=star (fourier n x) := by
    rw [← starRingEnd_apply, ← fourier_neg]
    simp only [fourier_apply, smul_neg, neg_smul]
  calc
    _ = ∫ x, fourier n (-x) • M.density (-x) ∂M.traceMeasure := by
      apply integral_congr_ae
      filter_upwards [M.density_reflection hr] with x hx
      rw [matrixConjugateCLM_complex_smul, hx, he]
    _ = _ := (M.trace_neg_preserving hr).integral_comp
      (MeasurableEquiv.neg (AddCircle T)).measurableEmbedding
      (fun x : AddCircle T => fourier n x • M.density x)

def toRealMatrixSpectrum (hr : M.RealReflection) : RealMatrixSpectrum T m where
  μ := M.traceMeasure
  F := M.density
  integrable := M.density_integrable
  positive := M.density_positive
  real_moments := M.real_fourier_covariances hr

theorem integral_spectrum_represents (hr : M.RealReflection) (s : Set (AddCircle T))
    (hs : MeasurableSet s) :
    (∫ x in s, (M.toRealMatrixSpectrum hr).F x ∂(M.toRealMatrixSpectrum hr).μ)=M.value s :=
  M.density_matrix_integral s hs

end PSDMatrixMeasure
end NoiseResponse.Classification

#print axioms NoiseResponse.Classification.PSDMatrixMeasure.integral_spectrum_represents
