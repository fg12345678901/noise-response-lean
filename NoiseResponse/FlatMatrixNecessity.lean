/- Added by cx on 2026-10-29: integrate the genuine A4 rectangular
   coefficient and connect its actual local potentials to classification. -/
module

public import NoiseResponse.RankOneResponseCoefficient
public import Mathlib.Tactic

@[expose] public section
set_option maxRecDepth 1500
set_option maxHeartbeats 5000000
noncomputable section
open MeasureTheory Filter Set Matrix Complex
open scoped Topology Matrix.Norms.Elementwise ComplexOrder ComplexConjugate Classical
attribute [local instance] matrixNormTopology
namespace NoiseResponse.Classification
variable {Ω m : Type*} [MeasurableSpace Ω] [Fintype m] [DecidableEq m] [Nonempty m]
variable {T : ℝ} [Fact (0 < T)]

theorem normal_power_integrable (μ : Measure Ω) (F : Ω → Matrix m m ℂ)
    (hF : Integrable F μ) (z : Ω → ℂ) (hz : Measurable z) (hu : ∀ x, ‖z x‖=1)
    (a : ℝ) (ha : ‖a‖<1) : Integrable (fun x => normalPowerKernel a (z x) • F x) μ := by
  apply hF.bdd_smul (φ := fun x => normalPowerKernel a (z x)) ((1/(1-‖a‖))^2)
  · apply Measurable.aestronglyMeasurable
    unfold normalPowerKernel
    fun_prop
  · apply Eventually.of_forall
    intro x
    rw [← normalTransfer_power a ha (z x) (hu x), norm_mul, norm_star]
    have hb : ‖normalTransfer a (z x)‖ ≤ 1/(1-‖a‖) := by
      rw [← norm_star (normalTransfer a (z x)), normalTransfer_star a ha (z x) (hu x)]
      exact causalCrossKernel_bound a ha (z x) (hu x)
    have hc : 0 ≤ 1/(1-‖a‖) := by positivity
    nlinarith [norm_nonneg (normalTransfer a (z x))]

theorem integral_rankOne_response (μ : Measure Ω) (F : Ω → Matrix m m ℂ)
    (hF : Integrable F μ) (hH : ∀ᵐ x ∂μ, (F x)ᴴ=F x)
    (z : Ω → ℂ) (hz : Measurable z) (hu : ∀ x, ‖z x‖=1)
    (η a : ℝ) (hη : η ≠ 0) (ha : ‖a‖<1) (u v : m → ℝ) :
    (∫ x, (Matrix.trace (NoiseResponse.Curvature.response η
        (rankOneTransfer η a (z x) u) (normalColumn v) (normalGramVariation u v)*F x)).re ∂μ)=
      probe (matrixRealCLM (∫ x, causalCrossKernel a (z x) • F x ∂μ)) v u-
        η*probe (matrixRealCLM (∫ x, normalPowerKernel a (z x) • F x ∂μ)) u u*probe 1 v u := by
  let L : Matrix m m ℂ →L[ℝ] ℝ := (realProbeCLM v u).comp matrixRealCLM
  let Q : Matrix m m ℂ →L[ℝ] ℝ := (realProbeCLM u u).comp matrixRealCLM
  have hk := cross_kernel_integrable μ F hF z hz hu a ha
  have hP := normal_power_integrable μ F hF z hz hu a ha
  have hL : Integrable (fun x => L (causalCrossKernel a (z x) • F x)) μ := L.integrable_comp hk
  have hQ : Integrable (fun x => Q (normalPowerKernel a (z x) • F x)) μ := Q.integrable_comp hP
  calc
    _ = ∫ x, L (causalCrossKernel a (z x) • F x)-
        η*Q (normalPowerKernel a (z x) • F x)*probe 1 v u ∂μ := by
      apply integral_congr_ae
      filter_upwards [hH] with x hx
      exact rankOne_response_readout η a hη ha (z x) (hu x) u v (F x) hx
    _ = _ := by
      rw [integral_sub hL ((hQ.const_mul η).mul_const _),
        integral_mul_const, integral_const_mul, L.integral_comp_comm hk, Q.integral_comp_comm hP]
      rfl

namespace RealMatrixSpectrum
variable (S : RealMatrixSpectrum T m)

/-- The frozen field defined by the manuscript's rectangular matrix
    coefficient, not by the reduced B1 expression. -/
def flatMatrixResponse (η : ℝ) (A : Plane → m → ℝ) (i : Fin 2) (p : Plane) : ℝ :=
  let u := A p
  let v := fderiv ℝ A p (planeAxis i)
  let a := 1-η*probe (1 : Matrix m m ℝ) u u
  ∫ x, (Matrix.trace (NoiseResponse.Curvature.response η
    (rankOneTransfer η a (fourier 1 x) u) (normalColumn v) (normalGramVariation u v)*S.F x)).re ∂S.μ

theorem flatMatrixResponse_eq_spectral (η : ℝ) (hη : η ≠ 0) (A : Plane → m → ℝ)
    (i : Fin 2) (p : Plane)
    (ha : (1-η*probe (1 : Matrix m m ℝ) (A p) (A p)) ∈ Ioo (-1 : ℝ) 1) :
    S.flatMatrixResponse η A i p=S.flatSpectralResponse η A i p := by
  have hn : ‖1-η*probe (1 : Matrix m m ℝ) (A p) (A p)‖<1 := by
    simpa only [Real.norm_eq_abs] using abs_lt.mpr ha
  unfold flatMatrixResponse flatSpectralResponse normalSpectralCovariance
  exact integral_rankOne_response S.μ S.F S.integrable S.hermitian _
    (fourier 1).continuous.measurable (fun x => Circle.norm_coe _) η _ hη hn _ _

def AllFlatMatrixPotentials (η : ℝ) : Prop :=
  ∀ (A : Plane → m → ℝ) (p : Plane), ContDiffAt ℝ 3 A p → A p ≠ 0 →
    (1-η*probe (1 : Matrix m m ℝ) (A p) (A p)) ∈ Ioo (-1 : ℝ) 1 →
      HasLocalPlanePotential (S.flatMatrixResponse η A 0) (S.flatMatrixResponse η A 1) p

theorem matrix_potentials_imply_spectral_potentials (η : ℝ) (hη : η ≠ 0)
    (hp : S.AllFlatMatrixPotentials η) : S.AllFlatSpectralPotentials η := by
  intro A p hA hnonzero ha
  obtain ⟨V,hV,hgrad⟩ := hp A p hA hnonzero ha
  refine ⟨V,hV,?_⟩
  have hcont : ContinuousAt (fun x => 1-η*probe (1 : Matrix m m ℝ) (A x) (A x)) p := by
    unfold probe
    fun_prop (disch := exact hA.continuousAt)
  have hstable : {x | (1-η*probe (1 : Matrix m m ℝ) (A x) (A x)) ∈ Ioo (-1 : ℝ) 1} ∈ 𝓝 p :=
    hcont.preimage_mem_nhds (isOpen_Ioo.mem_nhds ha)
  filter_upwards [hgrad,hstable] with x hx hs
  exact ⟨hx.1.trans (S.flatMatrixResponse_eq_spectral η hη A 0 x hs),
    hx.2.trans (S.flatMatrixResponse_eq_spectral η hη A 1 x hs)⟩

end RealMatrixSpectrum

namespace PSDMatrixMeasure
variable (M : PSDMatrixMeasure (AddCircle T) m)

theorem matrix_flat_necessity (hr : M.RealReflection) (η : ℝ) (hη : 0 < η)
    (hp : (M.toRealMatrixSpectrum hr).AllFlatMatrixPotentials η) : M.HasClassifiedSpectrum :=
  M.flat_spectral_necessity_complete hr η hη
    ((M.toRealMatrixSpectrum hr).matrix_potentials_imply_spectral_potentials η (ne_of_gt hη) hp)

end PSDMatrixMeasure
end NoiseResponse.Classification

#print axioms NoiseResponse.Classification.PSDMatrixMeasure.matrix_flat_necessity
