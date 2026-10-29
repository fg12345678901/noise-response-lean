/- Added by cx on 2026-10-29: positivity on every measurable set
   forces an integrable matrix density to be PSD almost everywhere. -/
module

public import NoiseResponse.MatrixPositiveIntegral
public import Mathlib.MeasureTheory.Function.AEEqOfIntegral
public import Mathlib.Tactic

@[expose] public section
set_option maxRecDepth 1000
set_option maxHeartbeats 3000000
noncomputable section
open MeasureTheory Filter Set Matrix Complex TopologicalSpace
open scoped Topology Matrix.Norms.Elementwise ComplexOrder
attribute [local instance] matrixNormTopology
namespace NoiseResponse.Classification
variable {Ω m : Type*} [MeasurableSpace Ω] [Fintype m] [DecidableEq m] [Nonempty m]

def vectorQuadraticTest (w : m → ℂ) : Matrix m m ℂ →L[ℂ] ℂ :=
  ∑ i, ∑ j, (star (w i)*w j) • matrixEntryCLM i j

theorem vectorQuadraticTest_apply (w : m → ℂ) (A : Matrix m m ℂ) :
    vectorQuadraticTest w A = star w ⬝ᵥ (A *ᵥ w) := by
  simp only [vectorQuadraticTest, _root_.sum_apply, _root_.smul_apply,
    matrixEntryCLM, smul_eq_mul]
  change (∑ i, ∑ j, (star (w i)*w j)*A i j) = ∑ i, star (w i)*(∑ j, A i j*w j)
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem density_positive_of_setIntegrals
    (μ : Measure Ω) (F : Ω → Matrix m m ℂ) (hF : Integrable F μ)
    (hsets : ∀ s : Set Ω, MeasurableSet s → (∫ x in s, F x ∂μ).PosSemidef) :
    ∀ᵐ x ∂μ, (F x).PosSemidef := by
  have hH : (fun x => (F x)ᴴ) =ᵐ[μ] F := by
    have hi := NoiseResponse.MatrixCalculus.adjCLM.integrable_comp hF
    change (fun x => NoiseResponse.MatrixCalculus.adjCLM (F x)) =ᵐ[μ] F
    apply Integrable.ae_eq_of_forall_setIntegral_eq _ _ hi hF
    intro s hs hfin
    rw [NoiseResponse.MatrixCalculus.adjCLM.integral_comp_comm hF.integrableOn]
    exact (hsets s hs).isHermitian.eq
  have hq (w : m → ℂ) : ∀ᵐ x ∂μ, 0 ≤ vectorQuadraticTest w (F x) := by
    have hi := (vectorQuadraticTest w).integrable_comp hF
    have hre := Complex.reCLM.integrable_comp hi
    have him := Complex.imCLM.integrable_comp hi
    have hr : ∀ᵐ x ∂μ, 0 ≤ (vectorQuadraticTest w (F x)).re := by
      apply ae_nonneg_of_forall_setIntegral_nonneg hre
      intro s hs hfin
      rw [Complex.reCLM.integral_comp_comm hi.integrableOn,
        (vectorQuadraticTest w).integral_comp_comm hF.integrableOn,
        vectorQuadraticTest_apply]
      exact (Complex.nonneg_iff.mp ((hsets s hs).dotProduct_mulVec_nonneg w)).1
    have hz : (fun x => (vectorQuadraticTest w (F x)).im) =ᵐ[μ] 0 := by
      apply him.ae_eq_zero_of_forall_setIntegral_eq_zero
      intro s hs hfin
      rw [Complex.imCLM.integral_comp_comm hi.integrableOn,
        (vectorQuadraticTest w).integral_comp_comm hF.integrableOn,
        vectorQuadraticTest_apply]
      exact (Complex.nonneg_iff.mp ((hsets s hs).dotProduct_mulVec_nonneg w)).2.symm
    filter_upwards [hr, hz] with x hx hz
    exact Complex.nonneg_iff.mpr ⟨hx, hz.symm⟩
  let ds : ℕ → (m → ℂ) := denseSeq (m → ℂ)
  have hds : DenseRange ds := denseRange_denseSeq (m → ℂ)
  have hcount : ∀ᵐ x ∂μ, ∀ n : ℕ, 0 ≤ vectorQuadraticTest (ds n) (F x) :=
    ae_all_iff.mpr (fun n => hq (ds n))
  filter_upwards [hH, hcount] with x hx hn
  have hc : IsClosed {w : m → ℂ | 0 ≤ vectorQuadraticTest w (F x)} := by
    apply isClosed_le continuous_const
    simp only [vectorQuadraticTest_apply, dotProduct, Matrix.mulVec]
    fun_prop
  have hall (w : m → ℂ) : 0 ≤ vectorQuadraticTest w (F x) :=
    isClosed_property hds hc hn w
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hx
  intro w
  simpa only [vectorQuadraticTest_apply] using hall w

end NoiseResponse.Classification

#print axioms NoiseResponse.Classification.density_positive_of_setIntegrals
