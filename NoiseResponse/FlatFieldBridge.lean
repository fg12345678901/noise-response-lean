/- Added by cx on 2026-10-29: the general canonical Jacobian response
   specializes to the manuscript's actual one-normal, two-tangent probes. -/
module

public import NoiseResponse.MeasuredFieldSufficiency
public import Mathlib.Tactic

@[expose] public section
set_option maxRecDepth 2100
set_option maxHeartbeats 8000000
noncomputable section
open Matrix Filter Set MeasureTheory
open scoped Topology Matrix.Norms.L2Operator
namespace NoiseResponse.FlatBridge
open NoiseResponse.Classification NoiseResponse.Geometry NoiseResponse.RankSafe
open NoiseResponse.Sufficiency NoiseResponse.IsotropicSpectrum
variable {m : Type*} [Fintype m] [DecidableEq m] [Nonempty m]

def realColumn (u : m → ℝ) : Matrix m Unit ℝ := fun i _ => u i

def realColumnCLM : (m → ℝ) →L[ℝ] Matrix m Unit ℝ :=
  (show (m → ℝ) →ₗ[ℝ] Matrix m Unit ℝ from
    { toFun := realColumn
      map_add' := by intro u v; rfl
      map_smul' := by intro c u; rfl }).toContinuousLinearMap

@[simp] theorem realColumnCLM_apply (u : m → ℝ) : realColumnCLM u=realColumn u := rfl

theorem full_column_projector {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix m n ℝ) (hli : LinearIndependent ℝ A.col) :
    NoiseResponse.ConstantRank.normalProjector A=1 := by
  have hAP := (NoiseResponse.ConstantRank.normalProjector_properties A).2.2.2.1
  have hinj := Matrix.mulVec_injective_iff.mpr hli
  apply Matrix.ext
  intro i j
  have he := congrArg (fun B : Matrix m n ℝ => B*ᵥPi.single j 1) hAP
  rw [← Matrix.mulVec_mulVec] at he
  have hv := congrFun (hinj he) i
  simpa [Matrix.mulVec_single_one,Pi.single_apply,Matrix.one_apply,eq_comm] using hv

theorem column_projector (u : m → ℝ) (hu : u ≠ 0) :
    NoiseResponse.Geometry.normalProjector (realColumn u)=1 := by
  have hli : LinearIndependent ℝ (realColumn u).col := linearIndependent_unique_iff.mpr hu
  rw [NoiseResponse.Geometry.normalProjector,full_column_projector _ hli,complexify_one]

theorem column_rank (u : m → ℝ) (hu : u ≠ 0) : (realColumn u)ᵀ.rank=1 := by
  have hli : LinearIndependent ℝ (realColumn u).col := linearIndependent_unique_iff.mpr hu
  have ht : LinearIndependent ℝ (realColumn u)ᵀ.row := by
    simpa only [Matrix.row_transpose] using hli
  simpa only [Fintype.card_unique] using ht.rank_matrix

theorem normalColumn_gram (u : m → ℝ) :
    (normalColumn u)ᴴ*normalColumn u=(probe (1 : Matrix m m ℝ) u u : ℂ) • (1 : Matrix Unit Unit ℂ) := by
  ext i j
  simp [normalColumn,Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.one_apply,
    probe_identity_sum,← Complex.ofReal_mul,← Complex.ofReal_sum]

theorem column_normalFilter (η : ℝ) (u : m → ℝ) :
    normalFilter η (normalColumn u) 1=
      ((1-η*probe (1 : Matrix m m ℝ) u u : ℝ) : ℂ) • (1 : Matrix Unit Unit ℂ) := by
  rw [normalFilter,normalColumn_gram]
  simp only [Complex.real_smul,smul_smul,Complex.ofReal_sub,Complex.ofReal_one,Complex.ofReal_mul]
  module

theorem column_filter_stable (η : ℝ) (u : m → ℝ)
    (ha : ‖1-η*probe (1 : Matrix m m ℝ) u u‖<1) :
    ‖normalFilter η (normalColumn u) 1‖<1 := by
  simpa only [column_normalFilter,norm_smul,Complex.norm_real,norm_one,mul_one] using ha

theorem column_transfer (η : ℝ) (u : m → ℝ)
    (ha : ‖1-η*probe (1 : Matrix m m ℝ) u u‖<1)
    (z : ℂ) (hz : ‖z‖=1) :
    transfer η (normalColumn u) 1 z=
      rankOneTransfer η (1-η*probe (1 : Matrix m m ℝ) u u) z u := by
  let a : ℝ := 1-η*probe (1 : Matrix m m ℝ) u u
  let B := normalFilter η (normalColumn u) 1
  let R := matrixResolvent B (star z)
  have hR := congrArg (fun D : Matrix Unit Unit ℂ => D () ())
    (matrixResolvent_inverse B (column_filter_stable η u ha) (star z)
      (by simpa only [norm_star] using hz)).1
  have hd : 1-star z*(a : ℂ) ≠ 0 := by
    simpa only [mul_comm] using stable_kernel_den_ne_zero a ha (star z)
      (by simpa only [norm_star] using hz)
  have he : (1-star z*(a : ℂ))*R () ()=1 := by
    simpa only [B,R,column_normalFilter,Matrix.mul_apply,Fintype.sum_unique,Matrix.sub_apply,
      Matrix.one_apply_eq,Matrix.smul_apply,smul_eq_mul,mul_one,a] using! hR
  have hr : R () ()=(1-star z*(a : ℂ))⁻¹ := by
    apply mul_left_cancel₀ hd
    rw [he,mul_inv_cancel₀ hd]
  have hs : normalTransfer a z=star z/(1-(a : ℂ)*star z) := by
    have hh := congrArg star (normalTransfer_star a ha z hz)
    simpa [star_star,causalCrossKernel] using hh
  ext i j
  simp only [transfer,Matrix.smul_apply,Matrix.mul_apply,Fintype.sum_unique,
    Matrix.conjTranspose_apply,normalColumn,Complex.star_def,Complex.conj_ofReal,
    rankOneTransfer,← Complex.real_smul]
  change (η : ℂ)*(star z*R () ()*(u j : ℂ))=(η : ℂ)*normalTransfer a z*(u j : ℂ)
  rw [hr,hs]
  simp only [div_eq_mul_inv,mul_comm (star z) (a : ℂ)]
  ring

variable {T : ℝ} [Fact (0 < T)]

theorem column_admissible (η : ℝ) (A : Plane → m → ℝ) (p : Plane)
    (hA : ContDiffAt ℝ 3 A p) (hn : A p ≠ 0)
    (ha : (1-η*probe (1 : Matrix m m ℝ) (A p) (A p)) ∈ Ioo (-1 : ℝ) 1) :
    AdmissibleJacobianAt η (fun q => realColumn (A q)) p := by
  have hcol : ContDiffAt ℝ 2 (fun q => realColumn (A q)) p := by
    simpa only [Function.comp_def,realColumnCLM_apply] using!
      realColumnCLM.contDiff.contDiffAt.comp p (hA.of_le (by norm_num))
  have hnnear : ∀ᶠ q in 𝓝 p, A q ≠ 0 :=
    hA.continuousAt.preimage_mem_nhds (isOpen_compl_singleton.mem_nhds hn)
  refine ⟨hcol,?_,?_⟩
  · filter_upwards [hnnear] with q hq
    rw [column_rank _ hq,column_rank _ hn]
  · rw [column_projector _ hn]
    exact column_filter_stable η (A p) (by simpa only [Real.norm_eq_abs] using abs_lt.mpr ha)

end NoiseResponse.FlatBridge
