/- Added by cx on 2026-10-29: positivity, finite mass, and endpoint
   nullity for the scalar measure identified by continuous tests. -/
module

public import NoiseResponse.SpectralIsotropy
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Tactic

@[expose] public section
set_option maxRecDepth 1000
set_option maxHeartbeats 2000000
noncomputable section
open MeasureTheory Filter Set Matrix
open scoped Topology Matrix.Norms.Elementwise NNReal ENNReal
attribute [local instance] matrixNormTopology
namespace NoiseResponse.Classification
variable {m : Type*} [Fintype m] [DecidableEq m] [Nonempty m]
variable {T : ℝ} [Fact (0 < T)]

theorem scalar_spectrum_is_positive_measure
    (μ : Measure (AddCircle T)) (F : AddCircle T → Matrix m m ℂ)
    (hF : Integrable F μ)
    (hdiag : ∀ᵐ x ∂μ, ∀ i, 0 ≤ (F x i i).re ∧ (F x i i).im = 0)
    (hiso : ∀ n : ℤ, ∃ cn : ℂ,
      densityTest μ F hF (fourier n) = cn • (1 : Matrix m m ℂ)) :
    ∃ ν : Measure (AddCircle T), IsFiniteMeasure ν ∧ ν ≪ μ ∧
      ∀ φ : C(AddCircle T, ℂ),
        (∫ x, φ x • F x ∂μ) = (∫ x, φ x ∂ν) • (1 : Matrix m m ℂ) := by
  let i : m := Classical.arbitrary m
  let g : AddCircle T → ℝ := fun x => (F x i i).re
  have hentry : Integrable (fun x => F x i i) μ := (matrixEntryCLM i i).integrable_comp hF
  have hg : Integrable g μ := Complex.reCLM.integrable_comp hentry
  let w : AddCircle T → ℝ≥0∞ := fun x => ENNReal.ofReal (g x)
  let ν := μ.withDensity w
  have hfinite : IsFiniteMeasure ν := by
    apply isFiniteMeasure_withDensity
    exact ((hasFiniteIntegral_iff_ofReal
      (hdiag.mono (fun x hx => (hx i).1))).mp hg.hasFiniteIntegral).ne
  obtain ⟨l, hl⟩ := isotropic_functional_of_scalar_fourier (densityTest μ F hF) hiso
  refine ⟨ν, hfinite, withDensity_absolutelyContinuous _ _, ?_⟩
  intro φ
  have hν : (∫ x, φ x ∂ν) = (∫ x, φ x • F x ∂μ) i i := by
    change (∫ x, φ x ∂μ.withDensity w) = _
    rw [integral_withDensity_eq_integral_toReal_smul₀ hg.aemeasurable.ennreal_ofReal
      (Eventually.of_forall (fun x => ENNReal.ofReal_lt_top))]
    calc
      _ = ∫ x, φ x * F x i i ∂μ := by
        apply integral_congr_ae
        filter_upwards [hdiag] with x hx
        have he : ((g x : ℝ) : ℂ) = F x i i := by
          apply Complex.ext <;> simp [g, (hx i).2]
        change (ENNReal.ofReal (g x)).toReal • φ x = _
        rw [ENNReal.toReal_ofReal (show 0 ≤ g x from (hx i).1)]
        change (g x : ℂ)*φ x = φ x*F x i i
        rw [he, mul_comm]
      _ = _ := (matrixEntryCLM i i).integral_comp_comm (integrable_test_smul μ F hF φ)
  have he := congrArg (fun L : C(AddCircle T, ℂ) →L[ℂ] Matrix m m ℂ => L φ) hl
  change (∫ x, φ x • F x ∂μ) = (l φ) • (1 : Matrix m m ℂ) at he
  have hd := congrArg (fun A : Matrix m m ℂ => A i i) he
  simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at hd
  rw [hν, hd]
  exact he

theorem scalar_measure_has_no_endpoint_atoms
    (μ ν : Measure (AddCircle T)) (hν : ν ≪ μ) (p0 ppi : AddCircle T)
    (h0 : μ {p0} = 0) (hpi : μ {ppi} = 0) : ν {p0}=0 ∧ ν {ppi}=0 :=
  ⟨hν h0, hν hpi⟩

end NoiseResponse.Classification

#print axioms NoiseResponse.Classification.scalar_spectrum_is_positive_measure
