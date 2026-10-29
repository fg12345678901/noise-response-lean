/- Added by cx on 2026-10-29: connect Fourier uniqueness to actual
   integrals and finite Borel measures on the circle. -/
module

public import NoiseResponse.FourierIdentification
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
public import Mathlib.Tactic

@[expose] public section

set_option maxRecDepth 1000
set_option maxHeartbeats 1000000
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace NoiseResponse.Classification
variable {T : ℝ} [Fact (0 < T)]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem integrable_test_smul (μ : Measure (AddCircle T))
    (f : AddCircle T → E) (hf : Integrable f μ) (g : C(AddCircle T, ℂ)) :
    Integrable (fun x => g x • f x) μ := by
  exact hf.bdd_smul ‖g‖ g.continuous.measurable.aestronglyMeasurable
    (Eventually.of_forall (fun x => g.norm_coe_le_norm x))

/-- A genuine vector-valued spectral density defines a continuous
    integration functional, with its explicit L1 norm bound. -/
def densityTest (μ : Measure (AddCircle T)) (f : AddCircle T → E)
    (hf : Integrable f μ) : C(AddCircle T, ℂ) →L[ℂ] E :=
  LinearMap.mkContinuous
    { toFun := fun g => ∫ x, g x • f x ∂μ
      map_add' := by
        intro g h
        simp only [ContinuousMap.add_apply, add_smul]
        exact integral_add (integrable_test_smul μ f hf g) (integrable_test_smul μ f hf h)
      map_smul' := by
        intro a g
        simp only [ContinuousMap.smul_apply, RingHom.id_apply, smul_eq_mul,
          ← smul_smul, integral_smul] }
    (∫ x, ‖f x‖ ∂μ) (by
      intro g
      have h := norm_integral_le_of_norm_le (f := fun x => g x • f x) (hf.norm.const_mul ‖g‖)
        (Eventually.of_forall (fun x => by
          rw [norm_smul]
          exact mul_le_mul_of_nonneg_right (g.norm_coe_le_norm x) (norm_nonneg _)))
      change ‖∫ x, g x • f x ∂μ‖ ≤ (∫ x, ‖f x‖ ∂μ) * ‖g‖
      calc
        _ ≤ ∫ x, ‖g‖ * ‖f x‖ ∂μ := h
        _ = ‖g‖ * (∫ x, ‖f x‖ ∂μ) := integral_const_mul _ _
        _ = _ := mul_comm _ _)

@[simp] theorem densityTest_apply (μ : Measure (AddCircle T))
    (f : AddCircle T → E) (hf : Integrable f μ) (g : C(AddCircle T, ℂ)) :
    densityTest μ f hf g = ∫ x, g x • f x ∂μ := rfl

/-- Fourier coefficients determine all continuous test integrals for
    arbitrary integrable vector densities and arbitrary base measures. -/
theorem spectral_integrals_eq_of_fourier
    (μ ν : Measure (AddCircle T)) (f g : AddCircle T → E)
    (hf : Integrable f μ) (hg : Integrable g ν)
    (h : ∀ k : ℤ, (∫ x, fourier k x • f x ∂μ) = ∫ x, fourier k x • g x ∂ν)
    (φ : C(AddCircle T, ℂ)) :
    (∫ x, φ x • f x ∂μ) = ∫ x, φ x • g x ∂ν := by
  have he := continuousLinearMap_eq_of_fourier (densityTest μ f hf) (densityTest ν g hg) h
  exact congrArg (fun L : C(AddCircle T, ℂ) →L[ℂ] E => L φ) he

/-- Actual finite positive Borel measures are identified by every integer
    Fourier coefficient, including the zero coefficient. -/
theorem finite_measure_eq_of_fourier
    (μ ν : Measure (AddCircle T)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ k : ℤ, (∫ x, fourier k x ∂μ) = ∫ x, fourier k x ∂ν) : μ = ν := by
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  let φ : C(AddCircle T, ℂ) :=
    ⟨fun x => (f x : ℂ), Complex.continuous_ofReal.comp f.continuous⟩
  have hi := spectral_integrals_eq_of_fourier μ ν (fun _ => (1 : ℂ))
    (fun _ => (1 : ℂ)) (integrable_const 1) (integrable_const 1)
    (by simpa using h) φ
  have hc : (∫ x, (f x : ℂ) ∂μ) = ∫ x, (f x : ℂ) ∂ν := by
    simpa only [φ, ContinuousMap.coe_mk, smul_eq_mul, mul_one] using hi
  exact Complex.ofReal_injective (by simpa only [integral_complex_ofReal] using hc)

end NoiseResponse.Classification

#print axioms NoiseResponse.Classification.spectral_integrals_eq_of_fourier
#print axioms NoiseResponse.Classification.finite_measure_eq_of_fourier
