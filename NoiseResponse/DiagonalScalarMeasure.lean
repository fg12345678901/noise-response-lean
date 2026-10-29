/- Added by cx on 2026-10-29: the scalar remainder as an actual
   finite measure, with identities on measurable sets and continuous tests. -/
module

public import NoiseResponse.IsotropicDensity
public import NoiseResponse.MatrixSpectralMeasure
public import Mathlib.Tactic

@[expose] public section
set_option maxRecDepth 1000
set_option maxHeartbeats 3000000
noncomputable section
open MeasureTheory Filter Set Matrix Complex
open scoped Topology Matrix.Norms.Elementwise ComplexOrder ENNReal
attribute [local instance] matrixNormTopology
namespace NoiseResponse.Classification
variable {m : Type*} [Fintype m] [DecidableEq m] [Nonempty m]
variable {T : ℝ} [Fact (0 < T)]

def diagonalScalarMeasure (μ : Measure (AddCircle T)) (F : AddCircle T → Matrix m m ℂ)
    (i : m) : Measure (AddCircle T) := μ.withDensity (fun x => ENNReal.ofReal (F x i i).re)

theorem diagonalScalarMeasure_finite
    (μ : Measure (AddCircle T)) (F : AddCircle T → Matrix m m ℂ)
    (hF : Integrable F μ) (i : m) : IsFiniteMeasure (diagonalScalarMeasure μ F i) := by
  have hg : Integrable (fun x => (F x i i).re) μ :=
    Complex.reCLM.integrable_comp ((matrixEntryCLM i i).integrable_comp hF)
  exact isFiniteMeasure_withDensity_ofReal hg.hasFiniteIntegral

theorem diagonalScalarMeasure_set_real
    (μ : Measure (AddCircle T)) (F : AddCircle T → Matrix m m ℂ)
    (hF : Integrable F μ) (hp : ∀ᵐ x ∂μ, (F x).PosSemidef)
    (i : m) (s : Set (AddCircle T)) (hs : MeasurableSet s) :
    (diagonalScalarMeasure μ F i).real s=∫ x in s, (F x i i).re ∂μ := by
  have hg : Integrable (fun x => (F x i i).re) μ :=
    Complex.reCLM.integrable_comp ((matrixEntryCLM i i).integrable_comp hF)
  rw [diagonalScalarMeasure, withDensity_real_apply_eq_integral
    hg.aemeasurable.ennreal_ofReal.restrict (Eventually.of_forall (fun x hx => ENNReal.ofReal_lt_top))
    hs.nullMeasurableSet]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae hp] with x hx
  exact ENNReal.toReal_ofReal (Complex.nonneg_iff.mp (hx.diag_nonneg (i := i))).1

theorem diagonalScalarMeasure_set_integral
    (μ : Measure (AddCircle T)) (F : AddCircle T → Matrix m m ℂ)
    (hF : Integrable F μ) (hp : ∀ᵐ x ∂μ, (F x).PosSemidef)
    (i : m) (hiso : F =ᵐ[μ] fun x => F x i i • (1 : Matrix m m ℂ))
    (s : Set (AddCircle T)) (hs : MeasurableSet s) :
    (∫ x in s, F x ∂μ)=((diagonalScalarMeasure μ F i).real s : ℂ) • (1 : Matrix m m ℂ) := by
  rw [diagonalScalarMeasure_set_real μ F hF hp i s hs]
  calc
    _ = ∫ x in s, (F x i i).re • (1 : Matrix m m ℂ) ∂μ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae hiso, ae_restrict_of_ae hp] with x hx hpx
      have he : F x i i=((F x i i).re : ℂ) := by
        apply Complex.ext
        · rfl
        · exact (Complex.nonneg_iff.mp (hpx.diag_nonneg (i := i))).2.symm
      calc
        F x = F x i i • (1 : Matrix m m ℂ) := hx
        _ = _ := by rw [he]; simp only [Complex.ofReal_re]; rfl
    _ = _ := by rw [integral_smul_const]; rfl

theorem diagonalScalarMeasure_test_integral
    (μ : Measure (AddCircle T)) (F : AddCircle T → Matrix m m ℂ)
    (hF : Integrable F μ) (hp : ∀ᵐ x ∂μ, (F x).PosSemidef)
    (i : m) (hiso : F =ᵐ[μ] fun x => F x i i • (1 : Matrix m m ℂ))
    (φ : C(AddCircle T, ℂ)) :
    (∫ x, φ x • F x ∂μ)=(∫ x, φ x ∂diagonalScalarMeasure μ F i) • (1 : Matrix m m ℂ) := by
  have hg : Integrable (fun x => (F x i i).re) μ :=
    Complex.reCLM.integrable_comp ((matrixEntryCLM i i).integrable_comp hF)
  have hi : Integrable (fun x => φ x*F x i i) μ := by
    have he := (matrixEntryCLM i i).integrable_comp (integrable_test_smul μ F hF φ)
    change Integrable (fun x => φ x*F x i i) μ at he
    exact he
  have hν : (∫ x, φ x ∂diagonalScalarMeasure μ F i)=∫ x, φ x * F x i i ∂μ := by
    rw [diagonalScalarMeasure, integral_withDensity_eq_integral_toReal_smul₀
      hg.aemeasurable.ennreal_ofReal (Eventually.of_forall (fun x => ENNReal.ofReal_lt_top))]
    apply integral_congr_ae
    filter_upwards [hp] with x hx
    have he : ((F x i i).re : ℂ)=F x i i := by
      apply Complex.ext
      · rfl
      · exact (Complex.nonneg_iff.mp (hx.diag_nonneg (i := i))).2
    rw [ENNReal.toReal_ofReal (Complex.nonneg_iff.mp (hx.diag_nonneg (i := i))).1]
    change ((F x i i).re : ℂ)*φ x=φ x*F x i i
    rw [he, mul_comm]
  rw [hν]
  calc
    _ = ∫ x, scalarMatrixCLM (φ x*F x i i) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hiso] with x hx
      conv_lhs => rw [hx, smul_smul]
      rfl
    _ = scalarMatrixCLM (m := m) (∫ x, φ x*F x i i ∂μ) :=
      ContinuousLinearMap.integral_comp_comm (scalarMatrixCLM (m := m)) hi
    _ = _ := rfl

end NoiseResponse.Classification

#print axioms NoiseResponse.Classification.diagonalScalarMeasure_set_integral
