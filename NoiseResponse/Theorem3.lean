/- Added by cx on 2026-10-29: the complete three-way classification
   for genuine clean constant-rank residual charts and original matrix measures. -/
module

public import NoiseResponse.ResidualGeometry
public import NoiseResponse.FlatAmbientResponse
public import Mathlib.Tactic

@[expose] public section
set_option maxRecDepth 2300
set_option maxHeartbeats 10000000
noncomputable section
open Matrix Filter Set MeasureTheory
open scoped Topology Matrix.Norms.L2Operator
namespace NoiseResponse.ResidualGeometry
open NoiseResponse.Sufficiency NoiseResponse.Geometry NoiseResponse.RankSafe
open NoiseResponse.Classification
variable {m n : Type*} [Fintype m] [DecidableEq m] [Nonempty m]
variable [Fintype n] [DecidableEq n] [Nonempty n]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {T : ℝ} [Fact (0 < T)]

theorem measured_real_field_congr (M : PSDMatrixMeasure (AddCircle T) m) (η : ℝ)
    (A B : E → Matrix m n ℝ) (x v : E) (hAB : A=ᶠ[𝓝 x] B) :
    measuredFrozenResponse M η (fun y => complexify (A y)) (fun y => normalProjector (A y)) x v=
      measuredFrozenResponse M η (fun y => complexify (B y)) (fun y => normalProjector (B y)) x v := by
  have hc : (fun y => complexify (A y))=ᶠ[𝓝 x] (fun y => complexify (B y)) :=
    hAB.mono (fun y hy => congrArg complexify hy)
  unfold measuredFrozenResponse
  rw [hc.fderiv_eq]
  simp only [hc.self_of_nhds,hAB.self_of_nhds]

end NoiseResponse.ResidualGeometry

namespace NoiseResponse.AmbientFlat
open NoiseResponse.Sufficiency NoiseResponse.Geometry NoiseResponse.RankSafe
open NoiseResponse.Classification
variable {m : Type*} [Fintype m] [DecidableEq m] [Nonempty m]

theorem admissible_residual (η : ℝ) (A : Plane → m → ℝ) (p : Plane)
    (hA : ContDiffAt ℝ 3 A p) (hn : A p ≠ 0)
    (ha : (1-η*probe (1 : Matrix m m ℝ) (A p) (A p)) ∈ Ioo (-1 : ℝ) 1) :
    NoiseResponse.ResidualGeometry.AdmissibleAt η (residual A) branchCLM p := by
  have hnnear : ∀ᶠ q in 𝓝 p, A q ≠ 0 :=
    hA.continuousAt.preimage_mem_nhds (isOpen_compl_singleton.mem_nhds hn)
  have hAnear := hA.eventually (by norm_num)
  have hJp : NoiseResponse.ResidualGeometry.jacobian (residual A) branchCLM p=column (A p) :=
    residual_jacobian A p (hA.differentiableAt (by norm_num))
  refine ⟨branchCLM.contDiff.contDiffAt,?_,?_,?_⟩
  · filter_upwards [hAnear,hnnear] with q hqA hqn
    refine ⟨residual_contDiffAt A q hqA,residual_clean A q,?_,
      branch_tangent_kernel A q (hqA.differentiableAt (by norm_num)) hqn⟩
    rw [branchCLM.hasFDerivAt.fderiv]
    exact (show Function.LeftInverse tangentCLM branchCLM from tangent_branch).injective
  · filter_upwards [hAnear,hnnear] with q hqA hqn
    have hJq : NoiseResponse.ResidualGeometry.jacobian (residual A) branchCLM q=column (A q) :=
      residual_jacobian A q (hqA.differentiableAt (by norm_num))
    rw [hJq,hJp,column_rank _ hqn,column_rank _ hn]
  · rw [hJp,canonical_projector _ hn]
    exact column_stable η (A p) (by simpa only [Real.norm_eq_abs] using abs_lt.mpr ha)

end NoiseResponse.AmbientFlat

namespace NoiseResponse.ResidualGeometry
open NoiseResponse.Sufficiency NoiseResponse.Geometry NoiseResponse.RankSafe
open NoiseResponse.Classification
variable {m : Type*} [Fintype m] [DecidableEq m] [Nonempty m]
variable {T : ℝ} [Fact (0 < T)]

theorem all_residuals_implies_admissible_flat (M : PSDMatrixMeasure (AddCircle T) m)
    (hr : M.RealReflection) (η : ℝ) (hall : AllResidualPotentials M η) :
    (M.toRealMatrixSpectrum hr).AllAdmissibleFlatPotentials η := by
  intro A p hgood
  have hg := admissible_flat_parameters η A p hgood
  have hres := NoiseResponse.AmbientFlat.admissible_residual η A p hg.1 hg.2.1 hg.2.2
  obtain ⟨V,hV,hgrad⟩ := hall 2 3 (NoiseResponse.AmbientFlat.residual A)
    NoiseResponse.AmbientFlat.branchCLM p hres
  refine ⟨V,hV,?_⟩
  have heq : jacobian (NoiseResponse.AmbientFlat.residual A) NoiseResponse.AmbientFlat.branchCLM
      =ᶠ[𝓝 p] (fun q => NoiseResponse.AmbientFlat.column (A q)) := by
    filter_upwards [hg.1.eventually (by norm_num)] with q hq
    exact NoiseResponse.AmbientFlat.residual_jacobian A q (hq.differentiableAt (by norm_num))
  have heqnear := eventually_eventually_nhds.mpr heq
  have hnear : ∀ᶠ q in 𝓝 p, AdmissibleFlatAt η A q := by
    obtain ⟨U,c,hU,hp,hc0,hc1,hdata⟩ := hgood
    filter_upwards [hU.mem_nhds hp] with q hq
    exact ⟨U,c,hU,hq,hc0,hc1,hdata⟩
  filter_upwards [hgrad,heqnear,hnear] with q hq hEq hgoodq
  have hh := admissible_flat_parameters η A q hgoodq
  have hd := hh.1.differentiableAt (by norm_num)
  have hresponse (i : Fin 2) :
      response M η (NoiseResponse.AmbientFlat.residual A) NoiseResponse.AmbientFlat.branchCLM q (planeAxis i)=
        (M.toRealMatrixSpectrum hr).flatMatrixResponse η A i q := by
    exact (measured_real_field_congr M η _ _ q (planeAxis i) hEq).trans
      (NoiseResponse.AmbientFlat.measured_ambient_eq_flat M hr η A q i hd hh.2.1 hh.2.2)
  exact ⟨(hq (planeAxis 0)).trans (hresponse 0),(hq (planeAxis 1)).trans (hresponse 1)⟩

/-- The manuscript's three numbered conditions, with actual residual
    functions, clean immersed charts, arbitrary finite parameter dimensions
    (including zero), the original A4 response and literal PSD matrix measures. -/
theorem theorem3_universal_spectral_classification
    (M : PSDMatrixMeasure (AddCircle T) m) (hr : M.RealReflection) (η : ℝ) (hη : 0 < η) :
    (AllResidualPotentials M η ↔ (M.toRealMatrixSpectrum hr).AllAdmissibleFlatPotentials η) ∧
      ((M.toRealMatrixSpectrum hr).AllAdmissibleFlatPotentials η ↔ M.HasClassifiedSpectrum) := by
  have hn := M.admissible_flat_spectral_necessity hr η hη
  have hs := fun h => classified_implies_all_residuals M h η hη
  have hf := all_residuals_implies_admissible_flat M hr η
  exact ⟨⟨hf,fun h => hs (hn h)⟩,⟨hn,fun h => hf (hs h)⟩⟩

end NoiseResponse.ResidualGeometry

#print axioms NoiseResponse.ResidualGeometry.theorem3_universal_spectral_classification
