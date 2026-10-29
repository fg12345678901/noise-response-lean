/- Added by cx on 2026-10-29: upgrade isotropy on all continuous
   tests to almost-everywhere scalar density and hence literal set masses. -/
module

public import NoiseResponse.ContinuousDensityUniqueness
public import NoiseResponse.SpectralIsotropy
public import Mathlib.Tactic

@[expose] public section
set_option maxRecDepth 1000
set_option maxHeartbeats 3000000
noncomputable section
open MeasureTheory Filter Set Matrix Complex
open scoped Topology Matrix.Norms.Elementwise
attribute [local instance] matrixNormTopology
namespace NoiseResponse.Classification
variable {m : Type*} [Fintype m] [DecidableEq m] [Nonempty m]
variable {T : ℝ} [Fact (0 < T)]

theorem isotropic_density_of_continuous_tests
    (μ : Measure (AddCircle T)) (F : AddCircle T → Matrix m m ℂ)
    (hF : Integrable F μ) (l : C(AddCircle T, ℂ) →L[ℂ] ℂ)
    (htest : ∀ φ : C(AddCircle T, ℂ), (∫ x, φ x • F x ∂μ)=l φ • (1 : Matrix m m ℂ))
    (i : m) : F =ᵐ[μ] (fun x => F x i i • (1 : Matrix m m ℂ)) := by
  let Q : ℂ →L[ℝ] Matrix m m ℂ := scalarMatrixCLM.restrictScalars ℝ
  have hi : Integrable (fun x => F x i i) μ := (matrixEntryCLM i i).integrable_comp hF
  have hQ := Q.integrable_comp hi
  have hzero : (fun x => F x-Q (F x i i)) =ᵐ[μ] 0 := by
    apply density_zero_of_continuous_tests μ _ (hF.sub hQ)
    intro φ
    let ψ : C(AddCircle T, ℂ) := ⟨fun x => (φ x : ℂ), Complex.continuous_ofReal.comp φ.continuous⟩
    have hr : (∫ x, φ x • F x ∂μ)=l ψ • (1 : Matrix m m ℂ) := htest ψ
    have hφF : Integrable (fun x => φ x • F x) μ :=
      hF.bdd_smul ‖φ‖ φ.continuous.measurable.aestronglyMeasurable
        (Eventually.of_forall (fun x => φ.norm_coe_le_norm x))
    have hφi := (matrixEntryCLM i i).integrable_comp hφF
    change Integrable (fun x => φ x • (F x i i)) μ at hφi
    have hdi := congrArg (fun A : Matrix m m ℂ => A i i) hr
    have hentry : (∫ x, φ x • F x i i ∂μ)=l ψ := by
      have hm := (matrixEntryCLM i i).integral_comp_comm hφF
      change (∫ x, (φ x • F x) i i ∂μ) = (∫ x, φ x • F x ∂μ) i i at hm
      simp only [Matrix.smul_apply] at hm
      rw [hm]
      simpa only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] using hdi
    have hsplit : (fun x => φ x • (F x-Q (F x i i))) =
        (fun x => φ x • F x-Q (φ x • (F x i i))) := by
      funext x
      rw [smul_sub, Q.map_smul]
    change (∫ x, φ x • (F x-Q (F x i i)) ∂μ)=0
    rw [hsplit]
    rw [integral_sub hφF (Q.integrable_comp hφi), Q.integral_comp_comm hφi, hr, hentry]
    change _-l ψ • (1 : Matrix m m ℂ)=0
    exact sub_self _
  filter_upwards [hzero] with x hx
  exact sub_eq_zero.mp hx

end NoiseResponse.Classification

#print axioms NoiseResponse.Classification.isotropic_density_of_continuous_tests
