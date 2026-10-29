/- Added by cx on 2026-10-29: end-to-end spectral classification for
   arbitrary constant-rank Jacobian fields, with the original admissible
   rank-one flat response as the actual necessity subfamily. -/
module

public import NoiseResponse.FlatFieldBridge
public import Mathlib.Tactic

@[expose] public section
set_option maxRecDepth 2200
set_option maxHeartbeats 9000000
noncomputable section
open Matrix Filter Set MeasureTheory
open scoped Topology Matrix.Norms.L2Operator
namespace NoiseResponse.FlatBridge
open NoiseResponse.Classification NoiseResponse.Geometry NoiseResponse.RankSafe
open NoiseResponse.Sufficiency NoiseResponse.IsotropicSpectrum
variable {m : Type*} [Fintype m] [DecidableEq m] [Nonempty m]

def normalColumnCLM : (m → ℝ) →L[ℝ] Matrix m Unit ℂ := complexifyCLM.comp realColumnCLM

@[simp] theorem normalColumnCLM_apply (u : m → ℝ) : normalColumnCLM u=normalColumn u := rfl

@[simp] theorem complexify_realColumn (u : m → ℝ) : complexify (realColumn u)=normalColumn u := rfl

theorem normalColumn_fderiv (A : Plane → m → ℝ) (p v : Plane)
    (hA : DifferentiableAt ℝ A p) :
    fderiv ℝ (fun q => normalColumn (A q)) p v=normalColumn (fderiv ℝ A p v) := by
  have hh := normalColumnCLM.hasFDerivAt.comp p hA.hasFDerivAt
  have he := congrArg (fun L : Plane →L[ℝ] Matrix m Unit ℂ => L v) hh.fderiv
  simpa only [Function.comp_def,ContinuousLinearMap.comp_apply,normalColumnCLM_apply] using! he

variable {T : ℝ} [Fact (0 < T)]

theorem measured_column_eq_flat (M : PSDMatrixMeasure (AddCircle T) m) (hr : M.RealReflection)
    (η : ℝ) (A : Plane → m → ℝ) (p : Plane) (i : Fin 2)
    (hA : DifferentiableAt ℝ A p) (hn : A p ≠ 0)
    (ha : (1-η*probe (1 : Matrix m m ℝ) (A p) (A p)) ∈ Ioo (-1 : ℝ) 1) :
    measuredFrozenResponse M η (fun q => complexify (realColumn (A q)))
      (fun q => NoiseResponse.Geometry.normalProjector (realColumn (A q))) p (planeAxis i)=
      (M.toRealMatrixSpectrum hr).flatMatrixResponse η A i p := by
  have ha' : ‖1-η*probe (1 : Matrix m m ℝ) (A p) (A p)‖<1 := by
    simpa only [Real.norm_eq_abs] using abs_lt.mpr ha
  unfold measuredFrozenResponse RealMatrixSpectrum.flatMatrixResponse
  simp only [frequencyCoefficient,complexify_realColumn,normalColumn_fderiv A p _ hA,
    column_projector _ hn]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro w
  dsimp only
  rw [column_transfer η (A p) ha' (fourier 1 w) (Circle.norm_coe _),← normalGramVariation_actual]
  rfl

end NoiseResponse.FlatBridge

namespace NoiseResponse.Sufficiency
open NoiseResponse.Classification
variable {m : Type*} [Fintype m] [DecidableEq m] [Nonempty m]
variable {T : ℝ} [Fact (0 < T)]

def AllJacobianPotentials (M : PSDMatrixMeasure (AddCircle T) m) (η : ℝ) : Prop :=
  ∀ (d : ℕ) (n : Type) [Fintype n] [DecidableEq n] [Nonempty n]
    (A : (Fin d → ℝ) → Matrix m n ℝ) (x : Fin d → ℝ), AdmissibleJacobianAt η A x →
      HasLocalPotential (measuredFrozenResponse M η (fun y => NoiseResponse.Geometry.complexify (A y))
        (fun y => NoiseResponse.Geometry.normalProjector (A y))) x

theorem classified_implies_all_jacobians (M : PSDMatrixMeasure (AddCircle T) m)
    (η : ℝ) (hη : 0 < η) (hclass : M.HasClassifiedSpectrum) : AllJacobianPotentials M η := by
  intro d n _ _ _ A x hgood
  exact classified_local_potential M hclass η hη A x hgood

theorem all_jacobians_implies_admissible_flat (M : PSDMatrixMeasure (AddCircle T) m)
    (hr : M.RealReflection) (η : ℝ) (hall : AllJacobianPotentials M η) :
    (M.toRealMatrixSpectrum hr).AllAdmissibleFlatPotentials η := by
  intro A p hgood
  have hg := admissible_flat_parameters η A p hgood
  have hfield := NoiseResponse.FlatBridge.column_admissible η A p hg.1 hg.2.1 hg.2.2
  obtain ⟨V,hV,hgrad⟩ := hall 2 Unit (fun q => NoiseResponse.FlatBridge.realColumn (A q)) p hfield
  refine ⟨V,hV,?_⟩
  have hnear : ∀ᶠ q in 𝓝 p, AdmissibleFlatAt η A q := by
    obtain ⟨U,c,hU,hp,hc0,hc1,hdata⟩ := hgood
    filter_upwards [hU.mem_nhds hp] with q hq
    exact ⟨U,c,hU,hq,hc0,hc1,hdata⟩
  filter_upwards [hgrad,hnear] with q hq hgoodq
  have hh := admissible_flat_parameters η A q hgoodq
  have hd := hh.1.differentiableAt (by norm_num)
  exact ⟨(hq (planeAxis 0)).trans (NoiseResponse.FlatBridge.measured_column_eq_flat
    M hr η A q 0 hd hh.2.1 hh.2.2),
    (hq (planeAxis 1)).trans (NoiseResponse.FlatBridge.measured_column_eq_flat
      M hr η A q 1 hd hh.2.1 hh.2.2)⟩

/-- The original matrix measure, actual A4 response, all finite chart
    dimensions, and genuine local C2 potentials are connected in both directions. -/
theorem universal_jacobian_classification (M : PSDMatrixMeasure (AddCircle T) m)
    (hr : M.RealReflection) (η : ℝ) (hη : 0 < η) :
    (AllJacobianPotentials M η ↔ (M.toRealMatrixSpectrum hr).AllAdmissibleFlatPotentials η) ∧
      ((M.toRealMatrixSpectrum hr).AllAdmissibleFlatPotentials η ↔ M.HasClassifiedSpectrum) := by
  have hn := M.admissible_flat_spectral_necessity hr η hη
  have hs := classified_implies_all_jacobians M η hη
  have hf := all_jacobians_implies_admissible_flat M hr η
  exact ⟨⟨hf,fun h => hs (hn h)⟩,⟨hn,fun h => hf (hs h)⟩⟩

end NoiseResponse.Sufficiency
