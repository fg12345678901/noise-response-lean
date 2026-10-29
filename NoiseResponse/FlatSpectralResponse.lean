/- Added by cx on 2026-10-29: actual frequency-kernel moments of the
   stable rank-one normal filter give the general flat B1 response. -/
module

public import NoiseResponse.RankOneSpectralMoments
public import NoiseResponse.MeasurableSpectralNecessity
public import Mathlib.Tactic

@[expose] public section
set_option maxRecDepth 1200
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory Filter Set Matrix Complex
open scoped Topology Matrix.Norms.Elementwise ComplexOrder Classical
attribute [local instance] matrixNormTopology
namespace NoiseResponse.Classification
variable {m : Type*} [Fintype m] [DecidableEq m] [Nonempty m]
variable {T : ℝ} [Fact (0 < T)]
namespace RealMatrixSpectrum
variable (S : RealMatrixSpectrum T m)

/-- The cross and normal covariances are computed from the actual
    scalar transfer kernels, before using any covariance generating ODE. -/
def flatSpectralResponse (η : ℝ) (A : Plane → m → ℝ) (i : Fin 2) (p : Plane) : ℝ :=
  let z := A p
  let h := probe (1 : Matrix m m ℝ) z z
  let a := 1-η*h
  let zi := fderiv ℝ A p (planeAxis i)
  let R := matrixRealCLM (∫ x, causalCrossKernel a (fourier 1 x) • S.F x ∂S.μ)
  let P := S.normalSpectralCovariance a
  probe R zi z-η*probe P z z*probe 1 zi z

theorem flatSpectralResponse_eq_moment (η : ℝ) (A : Plane → m → ℝ)
    (i : Fin 2) (p : Plane)
    (ha : (1-η*probe (1 : Matrix m m ℝ) (A p) (A p)) ∈ Ioo (-1 : ℝ) 1) :
    S.flatSpectralResponse η A i p=S.rankOneResponse η A i p := by
  let h := probe (1 : Matrix m m ℝ) (A p) (A p)
  let a := 1-η*h
  have hab : a ∈ Ioo (-1 : ℝ) 1 := ha
  have hn : ‖a‖<1 := by simpa only [Real.norm_eq_abs] using abs_lt.mpr hab
  have hh : h ≠ 0 := by
    intro hz
    have he : a=1 := by dsimp [a]; rw [hz]; ring
    rw [he] at hab
    exact (lt_irrefl (1 : ℝ)) hab.2
  have hp : 1+a ≠ 0 := ne_of_gt (by linarith [hab.1])
  have hm : 1-a ≠ 0 := ne_of_gt (sub_pos.mpr hab.2)
  have hsq : 1-a^2 ≠ 0 := by
    rw [show 1-a^2=(1-a)*(1+a) by ring]
    exact mul_ne_zero hm hp
  have hcoeff : η*(1-a^2)⁻¹=(h*(1+a))⁻¹ := by
    have he : η*h=1-a := by dsimp [a]; ring
    field_simp [hsq, hh, hp]
    nlinarith [he]
  dsimp only [flatSpectralResponse, rankOneResponse]
  change probe (matrixRealCLM (∫ x, causalCrossKernel a (fourier 1 x) • S.F x ∂S.μ))
      (fderiv ℝ A p (planeAxis i)) (A p) -
      η*probe (S.normalSpectralCovariance a) (A p) (A p)*
        probe 1 (fderiv ℝ A p (planeAxis i)) (A p) = _
  rw [S.cross_spectral_moment a hn, S.normal_spectral_covariance a hn, probe_matrix_smul]
  change _ = probe (S.rankOneK a) _ _ - probe (S.rankOneC a) _ _/(h*(1+a))*probe 1 _ _
  rw [show η*((1-a^2)⁻¹*probe (S.rankOneC a) (A p) (A p))=
    (h*(1+a))⁻¹*probe (S.rankOneC a) (A p) (A p) by rw [← mul_assoc, hcoeff]]
  ring

def AllFlatSpectralPotentials (η : ℝ) : Prop :=
  ∀ (A : Plane → m → ℝ) (p : Plane), ContDiffAt ℝ 3 A p → A p ≠ 0 →
    (1-η*probe (1 : Matrix m m ℝ) (A p) (A p)) ∈ Ioo (-1 : ℝ) 1 →
      HasLocalPlanePotential (S.flatSpectralResponse η A 0) (S.flatSpectralResponse η A 1) p

theorem spectral_potentials_imply_moment_potentials (η : ℝ)
    (hp : S.AllFlatSpectralPotentials η) : S.AllFlatLocalPotentials η := by
  intro A p hA hnonzero ha
  obtain ⟨V,hV,hgrad⟩ := hp A p hA hnonzero ha
  refine ⟨V,hV,?_⟩
  have hcont : ContinuousAt (fun x => 1-η*probe (1 : Matrix m m ℝ) (A x) (A x)) p := by
    unfold probe
    fun_prop (disch := exact hA.continuousAt)
  have hstable : {x | (1-η*probe (1 : Matrix m m ℝ) (A x) (A x)) ∈ Ioo (-1 : ℝ) 1} ∈ 𝓝 p :=
    hcont.preimage_mem_nhds (isOpen_Ioo.mem_nhds ha)
  filter_upwards [hgrad, hstable] with x hx hs
  exact ⟨hx.1.trans (S.flatSpectralResponse_eq_moment η A 0 x hs),
    hx.2.trans (S.flatSpectralResponse_eq_moment η A 1 x hs)⟩

end RealMatrixSpectrum

namespace PSDMatrixMeasure
variable (M : PSDMatrixMeasure (AddCircle T) m)

theorem flat_spectral_measure_necessity (hr : M.RealReflection) (η : ℝ) (hη : 0 < η)
    (hp : (M.toRealMatrixSpectrum hr).AllFlatSpectralPotentials η) :
    ∃ ν : Measure (AddCircle T), IsFiniteMeasure ν ∧ ν {(0 : AddCircle T)}=0 ∧
      ν {nyquistPoint T}=0 ∧ ν.map (fun x => -x)=ν ∧
      ∀ s : Set (AddCircle T), MeasurableSet s →
        M.value s=(ν.real s : ℂ) • (1 : Matrix m m ℂ)+
          (if (0 : AddCircle T) ∈ s then M.value {0} else 0)+
          (if nyquistPoint T ∈ s then M.value {nyquistPoint T} else 0) :=
  M.flat_potential_measure_necessity hr η hη
    ((M.toRealMatrixSpectrum hr).spectral_potentials_imply_moment_potentials η hp)

end PSDMatrixMeasure
end NoiseResponse.Classification

#print axioms NoiseResponse.Classification.PSDMatrixMeasure.flat_spectral_measure_necessity
