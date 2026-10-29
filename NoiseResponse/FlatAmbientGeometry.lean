/- Added by cx on 2026-10-29: actual three-parameter residual charts,
   retaining both tangent zero columns in the full ambient Jacobian. -/
module

public import NoiseResponse.JacobianClassificationEquivalence
public import Mathlib.Tactic

@[expose] public section
set_option maxRecDepth 2200
set_option maxHeartbeats 9000000
noncomputable section
open Matrix Filter Set MeasureTheory
open scoped Topology Matrix.Norms.L2Operator
namespace NoiseResponse.AmbientFlat
open NoiseResponse.Classification NoiseResponse.Geometry NoiseResponse.RankSafe
open NoiseResponse.Sufficiency NoiseResponse.IsotropicSpectrum
variable {m : Type*} [Fintype m] [DecidableEq m] [Nonempty m]

abbrev Ambient := Fin 3 → ℝ
def normalAxis : Ambient := Pi.single 2 1
def projector : Matrix (Fin 3) (Fin 3) ℝ := Matrix.diagonal normalAxis
def column (u : m → ℝ) : Matrix m (Fin 3) ℝ := Matrix.vecMulVec u normalAxis

theorem projector_properties : projectorᵀ=projector ∧ projector*projector=projector := by
  constructor
  · simp only [projector,Matrix.diagonal_transpose]
  · rw [projector,Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    fin_cases i <;> norm_num [normalAxis,Pi.single_apply,Matrix.vecMulVec_apply]

theorem projector_covers (u : m → ℝ) : projector*(column u)ᵀ=(column u)ᵀ := by
  ext i j
  fin_cases i <;> simp [projector,column,normalAxis,Matrix.mul_apply,Fin.sum_univ_three,Pi.single_apply,Matrix.vecMulVec_apply]

theorem projector_range (u : m → ℝ) (hu : u ≠ 0) :
    LinearMap.range projector.toLin'=LinearMap.range (column u)ᵀ.toLin' := by
  have hcover := projector_covers u
  apply le_antisymm
  · obtain ⟨k,hk⟩ : ∃ k, u k ≠ 0 := Function.ne_iff.mp hu
    intro v hv
    obtain ⟨w,rfl⟩ := hv
    refine ⟨Pi.single k (w 2/u k),?_⟩
    rw [Matrix.toLin'_apply,Matrix.mulVec_single]
    apply funext
    intro i
    fin_cases i <;> simp [projector,column,normalAxis,Matrix.mulVec,Matrix.mul_apply,
      dotProduct,Fin.sum_univ_three,Pi.single_apply,hk,mul_div_cancel₀,Matrix.vecMulVec_apply]
    field_simp
  · intro v hv
    obtain ⟨w,rfl⟩ := hv
    refine ⟨(column u)ᵀ.toLin' w,?_⟩
    have hh := congrArg (fun D : Matrix (Fin 3) m ℝ => D.toLin' w) hcover
    simpa only [Matrix.toLin'_mul,LinearMap.comp_apply] using hh

theorem canonical_projector (u : m → ℝ) (hu : u ≠ 0) :
    NoiseResponse.Geometry.normalProjector (column u)=complexify projector := by
  have hcan := NoiseResponse.ConstantRank.normalProjector_properties (column u)
  have hp := projector_properties
  have he := NoiseResponse.ConstantRank.symmetric_projector_unique
    (NoiseResponse.ConstantRank.normalProjector (column u)) projector hcan.1 hp.1 hcan.2.1 hp.2
      (hcan.2.2.2.2.trans (projector_range u hu).symm)
  exact congrArg complexify he

theorem projector_rank : projector.rank=1 := by
  simp [projector,Matrix.rank_diagonal,normalAxis,Pi.single_apply,Matrix.vecMulVec_apply]

theorem column_rank (u : m → ℝ) (hu : u ≠ 0) : (column u)ᵀ.rank=1 := by
  have he := congrArg (fun S : Submodule ℝ Ambient => Module.finrank ℝ S) (projector_range u hu)
  have he' : (column u)ᵀ.rank=projector.rank := by
    simpa only [Matrix.rank,← Matrix.toLin'_apply'] using! he.symm
  exact he'.trans projector_rank

theorem projector_norm : ‖complexify projector‖=1 := by
  have he : complexify projector=Matrix.diagonal (Pi.single (2 : Fin 3) (1 : ℂ)) := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [projector,normalAxis,complexify,Pi.single_apply,Matrix.vecMulVec_apply]
  rw [he,Matrix.l2_opNorm_diagonal,Pi.norm_single,norm_one]

theorem column_gram (u : m → ℝ) :
    (complexify (column u))ᴴ*complexify (column u)=
      (probe (1 : Matrix m m ℝ) u u : ℂ) • complexify projector := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [complexify,column,projector,normalAxis,Matrix.mul_apply,Matrix.conjTranspose_apply,
      Pi.single_apply,probe_identity_sum,← Complex.ofReal_mul,← Complex.ofReal_sum,Matrix.vecMulVec_apply]

theorem column_filter (η : ℝ) (u : m → ℝ) :
    normalFilter η (complexify (column u)) (complexify projector)=
      ((1-η*probe (1 : Matrix m m ℝ) u u : ℝ) : ℂ) • complexify projector := by
  rw [normalFilter,column_gram]
  simp only [Complex.real_smul,smul_smul,Complex.ofReal_sub,Complex.ofReal_one,Complex.ofReal_mul]
  module

theorem column_stable (η : ℝ) (u : m → ℝ)
    (ha : ‖1-η*probe (1 : Matrix m m ℝ) u u‖<1) :
    ‖normalFilter η (complexify (column u)) (complexify projector)‖<1 := by
  simpa only [column_filter,norm_smul,Complex.norm_real,projector_norm,mul_one] using ha

def columnCLM : (m → ℝ) →L[ℝ] Matrix m (Fin 3) ℝ :=
  (show (m → ℝ) →ₗ[ℝ] Matrix m (Fin 3) ℝ from
    { toFun := column
      map_add' := by intro u v; ext i j; simp [column,Matrix.vecMulVec,add_mul]
      map_smul' := by intro c u; ext i j; simp [column,Matrix.vecMulVec,mul_assoc] }).toContinuousLinearMap

@[simp] theorem columnCLM_apply (u : m → ℝ) : columnCLM u=column u := rfl

def tangentCLM : Ambient →L[ℝ] Plane :=
  (show Ambient →ₗ[ℝ] Plane from
    { toFun := fun w => ![w 0,w 1]
      map_add' := by intro u v; ext i; fin_cases i <;> rfl
      map_smul' := by intro c u; ext i; fin_cases i <;> rfl }).toContinuousLinearMap

def branchCLM : Plane →L[ℝ] Ambient :=
  (show Plane →ₗ[ℝ] Ambient from
    { toFun := fun x => ![x 0,x 1,0]
      map_add' := by intro u v; ext i; fin_cases i <;> simp
      map_smul' := by intro c u; ext i; fin_cases i <;> simp }).toContinuousLinearMap

@[simp] theorem tangent_branch (x : Plane) : tangentCLM (branchCLM x)=x := by
  ext i
  fin_cases i <;> rfl

@[simp] theorem branch_normal (x : Plane) : branchCLM x 2=0 := rfl

def residual (A : Plane → m → ℝ) (w : Ambient) : m → ℝ := w 2 • A (tangentCLM w)

theorem residual_clean (A : Plane → m → ℝ) (x : Plane) : residual A (branchCLM x)=0 := by
  simp only [residual,branch_normal,zero_smul]

theorem residual_contDiffAt (A : Plane → m → ℝ) (x : Plane) (hA : ContDiffAt ℝ 3 A x) :
    ContDiffAt ℝ 3 (residual A) (branchCLM x) := by
  unfold residual
  have hAx : ContDiffAt ℝ 3 A (tangentCLM (branchCLM x)) := by rw [tangent_branch]; exact hA
  have ht := hAx.comp (branchCLM x) tangentCLM.contDiff.contDiffAt
  simpa only [tangent_branch] using!
    (ContinuousLinearMap.proj (2 : Fin 3) : Ambient →L[ℝ] ℝ).contDiff.contDiffAt.smul ht

theorem residual_hasFDerivAt (A : Plane → m → ℝ) (x : Plane) (hA : DifferentiableAt ℝ A x) :
    HasFDerivAt (residual A)
      ((ContinuousLinearMap.proj (2 : Fin 3) : Ambient →L[ℝ] ℝ).smulRight (A x)) (branchCLM x) := by
  have hT : HasFDerivAt (fun w => A (tangentCLM w))
      ((fderiv ℝ A x).comp tangentCLM) (branchCLM x) := by
    have hAx : HasFDerivAt A (fderiv ℝ A x) (tangentCLM (branchCLM x)) := by
      rw [tangent_branch]; exact hA.hasFDerivAt
    exact hAx.comp (branchCLM x) tangentCLM.hasFDerivAt
  have hp := (ContinuousLinearMap.proj (2 : Fin 3) : Ambient →L[ℝ] ℝ).hasFDerivAt (x := branchCLM x)
  simpa only [residual,ContinuousLinearMap.proj_apply,branch_normal,tangent_branch,
    Pi.smul_apply,zero_smul,zero_add] using! hp.smul hT

theorem residual_jacobian (A : Plane → m → ℝ) (x : Plane) (hA : DifferentiableAt ℝ A x) :
    LinearMap.toMatrix' (fderiv ℝ (residual A) (branchCLM x)).toLinearMap=column (A x) := by
  rw [(residual_hasFDerivAt A x hA).fderiv]
  ext i j
  fin_cases j <;>
    simp [LinearMap.toMatrix'_apply,ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.proj_apply,
      column,normalAxis,Matrix.vecMulVec,Pi.single_apply,Matrix.vecMulVec_apply]

theorem residual_kernel (A : Plane → m → ℝ) (x : Plane)
    (hA : DifferentiableAt ℝ A x) (hn : A x ≠ 0) (w : Ambient) :
    fderiv ℝ (residual A) (branchCLM x) w=0 ↔ w 2=0 := by
  rw [(residual_hasFDerivAt A x hA).fderiv]
  change w 2 • A x=0 ↔ w 2=0
  rw [smul_eq_zero]
  simp only [hn,or_false]

theorem branch_tangent_kernel (A : Plane → m → ℝ) (x : Plane)
    (hA : DifferentiableAt ℝ A x) (hn : A x ≠ 0) :
    LinearMap.range (fderiv ℝ branchCLM x).toLinearMap=
      LinearMap.ker (fderiv ℝ (residual A) (branchCLM x)).toLinearMap := by
  rw [branchCLM.hasFDerivAt.fderiv]
  ext w
  constructor
  · rintro ⟨v,rfl⟩
    exact (residual_kernel A x hA hn _).mpr (branch_normal v)
  · intro hw
    have hnw : w 2=0 := (residual_kernel A x hA hn w).mp hw
    refine ⟨tangentCLM w,?_⟩
    ext i
    fin_cases i <;> simp [branchCLM,tangentCLM,hnw]

end NoiseResponse.AmbientFlat
