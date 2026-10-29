/- Added by cx on 2026-10-29: genuine clean constant-rank flat charts
   with a uniform normal gap, and their classification necessity. -/
module

public import NoiseResponse.FlatMatrixNecessity
public import Mathlib.Tactic

@[expose] public section
set_option maxRecDepth 1500
set_option maxHeartbeats 5000000
noncomputable section
open MeasureTheory Filter Set Matrix Complex
open scoped Topology Matrix.Norms.Elementwise ComplexOrder Classical
attribute [local instance] matrixNormTopology
namespace NoiseResponse.Classification
variable {m : Type*} [Fintype m] [DecidableEq m] [Nonempty m]
variable {T : ℝ} [Fact (0 < T)]

/-- Actual open-chart conditions for the residual f(x,y)=A(x)y:
    clean branch, constant rank one, its exact tangent kernel, and a
    uniform contraction on the normal line. No response equation or
    potential condition is part of admissibility. -/
def AdmissibleFlatAt (η : ℝ) (A : Plane → m → ℝ) (p : Plane) : Prop :=
  ∃ (U : Set Plane) (q : ℝ), IsOpen U ∧ p ∈ U ∧ 0 ≤ q ∧ q<1 ∧
    ∀ x ∈ U, ContDiffAt ℝ 3 A x ∧ ContDiffAt ℝ 3 (flatResidual A) (x,0) ∧
      flatResidual A (x,0)=0 ∧
      Module.finrank ℝ (LinearMap.range (fderiv ℝ (flatResidual A) (x,0)).toLinearMap)=1 ∧
      (∀ w : Plane × ℝ, fderiv ℝ (flatResidual A) (x,0) w=0 ↔ w.2=0) ∧
      |1-η*probe (1 : Matrix m m ℝ) (A x) (A x)| ≤ q

theorem flat_admissible_chart (η : ℝ) (A : Plane → m → ℝ) (p : Plane)
    (hA : ContDiffAt ℝ 3 A p) (hz : A p ≠ 0)
    (ha : (1-η*probe (1 : Matrix m m ℝ) (A p) (A p)) ∈ Ioo (-1 : ℝ) 1) :
    AdmissibleFlatAt η A p := by
  let a : Plane → ℝ := fun x => 1-η*probe (1 : Matrix m m ℝ) (A x) (A x)
  have hcont : ContinuousAt a p := by
    unfold a probe
    fun_prop (disch := exact hA.continuousAt)
  let q := (|a p|+1)/2
  have habs : |a p|<1 := abs_lt.mpr ha
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hq1 : q<1 := by dsimp [q]; linarith
  have hpeq : |a p|<q := by dsimp [q]; linarith
  have hsmooth : ∀ᶠ x in 𝓝 p, ContDiffAt ℝ 3 A x := hA.eventually (by norm_num)
  have hnonzero : ∀ᶠ x in 𝓝 p, A x ≠ 0 :=
    hA.continuousAt.preimage_mem_nhds (isOpen_compl_singleton.mem_nhds hz)
  have hpq : ‖a p‖ ∈ Iio q := by
    change ‖a p‖<q
    simpa only [Real.norm_eq_abs] using hpeq
  have hbound : {x | |a x|<q} ∈ 𝓝 p := by
    have he := hcont.norm.preimage_mem_nhds (isOpen_Iio.mem_nhds hpq)
    change {x | ‖a x‖<q} ∈ 𝓝 p at he
    simpa only [Real.norm_eq_abs] using he
  have he : {x | ContDiffAt ℝ 3 A x ∧ A x ≠ 0 ∧ |a x|<q} ∈ 𝓝 p := by
    filter_upwards [hsmooth,hnonzero,hbound] with x h₁ h₂ h₃
    exact ⟨h₁,h₂,h₃⟩
  obtain ⟨U,hUs,hU,hpU⟩ := mem_nhds_iff.mp he
  refine ⟨U,q,hU,hpU,hq0,hq1,?_⟩
  intro x hx
  obtain ⟨hAx,hzx,hbx⟩ := hUs hx
  have hd := hAx.differentiableAt (by norm_num)
  exact ⟨hAx,flatResidual_contDiffAt A x 0 hAx,flatResidual_clean A x,flatResidual_clean_rank A x hd hzx,
    flatResidual_clean_kernel A x hd hzx,hbx.le⟩

theorem admissible_flat_parameters (η : ℝ) (A : Plane → m → ℝ) (p : Plane)
    (h : AdmissibleFlatAt η A p) :
    ContDiffAt ℝ 3 A p ∧ A p ≠ 0 ∧
      (1-η*probe (1 : Matrix m m ℝ) (A p) (A p)) ∈ Ioo (-1 : ℝ) 1 := by
  obtain ⟨U,q,hU,hp,hq0,hq1,hall⟩ := h
  obtain ⟨hA,hf,hclean,hrank,hker,hb⟩ := hall p hp
  have hn : A p ≠ 0 := by
    intro hz
    have he := (hker (0,1)).mp (by
      rw [(flatResidual_derivative A p (hA.differentiableAt (by norm_num))).fderiv]
      change (1 : ℝ) • A p=0
      simp only [hz, smul_zero])
    norm_num at he
  exact ⟨hA,hn,abs_lt.mp (lt_of_le_of_lt hb hq1)⟩

namespace RealMatrixSpectrum
variable (S : RealMatrixSpectrum T m)

def AllAdmissibleFlatPotentials (η : ℝ) : Prop :=
  ∀ (A : Plane → m → ℝ) (p : Plane), AdmissibleFlatAt η A p →
    HasLocalPlanePotential (S.flatMatrixResponse η A 0) (S.flatMatrixResponse η A 1) p

theorem admissible_flat_iff_matrix_potentials (η : ℝ) :
    S.AllAdmissibleFlatPotentials η ↔ S.AllFlatMatrixPotentials η := by
  constructor
  · intro h A p hA hn ha
    exact h A p (flat_admissible_chart η A p hA hn ha)
  · intro h A p hgood
    obtain ⟨hA,hn,ha⟩ := admissible_flat_parameters η A p hgood
    exact h A p hA hn ha

end RealMatrixSpectrum

namespace PSDMatrixMeasure
variable (M : PSDMatrixMeasure (AddCircle T) m)

/-- Complete necessity from actual clean admissible flat geometries
    and the original spectral matrix coefficient, for an arbitrary
    finite PSD real-process matrix measure. -/
theorem admissible_flat_spectral_necessity (hr : M.RealReflection) (η : ℝ) (hη : 0 < η)
    (hp : (M.toRealMatrixSpectrum hr).AllAdmissibleFlatPotentials η) :
    M.HasClassifiedSpectrum :=
  M.matrix_flat_necessity hr η hη
    (((M.toRealMatrixSpectrum hr).admissible_flat_iff_matrix_potentials η).mp hp)

end PSDMatrixMeasure
end NoiseResponse.Classification

#print axioms NoiseResponse.Classification.PSDMatrixMeasure.admissible_flat_spectral_necessity
