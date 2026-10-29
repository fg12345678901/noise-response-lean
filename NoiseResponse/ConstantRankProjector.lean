/- Added by cx on 2026-10-29: a smooth normal projector is constructed
   from an arbitrary constant-rank real matrix field by a fixed local frame. -/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Bilinear
public import Mathlib.Tactic

@[expose] public section
set_option maxRecDepth 1800
set_option maxHeartbeats 7000000
noncomputable section
open Matrix Filter Set Module
open scoped Topology Matrix.Norms.L2Operator
namespace NoiseResponse.ConstantRank
variable {m n r : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
variable [Fintype r] [DecidableEq r]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem gram_isUnit (B : Matrix n r ℝ) (hB : LinearIndependent ℝ B.col) :
    IsUnit (Bᵀ*B) := by
  apply Matrix.mulVec_surjective_iff_isUnit.mp
  apply Matrix.mulVec_surjective_iff_rank_eq_card.mpr
  rw [Matrix.rank_transpose_mul_self,← Matrix.rank_transpose B]
  have ht : LinearIndependent ℝ Bᵀ.row := by simpa only [Matrix.row_transpose] using hB
  exact ht.rank_matrix

def rangeProjector (B : Matrix n r ℝ) : Matrix n n ℝ := B*(Bᵀ*B)⁻¹*Bᵀ

theorem rangeProjector_properties (B : Matrix n r ℝ) (hB : LinearIndependent ℝ B.col) :
    (rangeProjector B)ᵀ=rangeProjector B ∧
      rangeProjector B*rangeProjector B=rangeProjector B ∧
      LinearMap.range (rangeProjector B).toLin'=LinearMap.range B.toLin' := by
  have hu := gram_isUnit B hB
  have hleft : (Bᵀ*B)*(Bᵀ*B)⁻¹=1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hu)
  have hright : (Bᵀ*B)⁻¹*(Bᵀ*B)=1 := mul_eq_one_comm.mp hleft
  have hG : ((Bᵀ*B)⁻¹)ᵀ=(Bᵀ*B)⁻¹ := by
    rw [Matrix.transpose_nonsing_inv,Matrix.transpose_mul,Matrix.transpose_transpose]
  have hPB : rangeProjector B*B=B := by
    change B*(Bᵀ*B)⁻¹*Bᵀ*B=B
    calc
      _ = B*((Bᵀ*B)⁻¹*(Bᵀ*B)) := by simp only [Matrix.mul_assoc]
      _ = B := by rw [hright,Matrix.mul_one]
  refine ⟨?_,?_,?_⟩
  · simp only [rangeProjector,Matrix.transpose_mul,Matrix.transpose_transpose,hG,Matrix.mul_assoc]
  · change rangeProjector B*(B*(Bᵀ*B)⁻¹*Bᵀ)=rangeProjector B
    rw [← Matrix.mul_assoc,← Matrix.mul_assoc,hPB]
    rfl
  · apply le_antisymm
    · rw [rangeProjector,Matrix.mul_assoc,Matrix.toLin'_mul]
      exact LinearMap.range_comp_le_range _ _
    · intro v hv
      obtain ⟨w,rfl⟩ := hv
      refine ⟨B.toLin' w,?_⟩
      have hh := congrArg (fun C : Matrix n r ℝ => C.toLin' w) hPB
      simpa only [Matrix.toLin'_mul,LinearMap.comp_apply] using hh

def transposeCLM : Matrix n r ℝ →L[ℝ] Matrix r n ℝ :=
  (Matrix.transposeLinearEquiv n r ℝ ℝ).toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem transposeCLM_apply (B : Matrix n r ℝ) : transposeCLM B=Bᵀ := rfl

def realMulCLM {l : Type*} [Fintype l] :
    Matrix l m ℝ →L[ℝ] Matrix m n ℝ →L[ℝ] Matrix l n ℝ :=
  ((LinearMap.toContinuousLinearMap :
      (Matrix m n ℝ →ₗ[ℝ] Matrix l n ℝ) ≃ₗ[ℝ]
        (Matrix m n ℝ →L[ℝ] Matrix l n ℝ)).toLinearMap.comp
      (mulLinearMap ℝ)).toContinuousLinearMap

@[simp] theorem realMulCLM_apply {l : Type*} [Fintype l]
    (A : Matrix l m ℝ) (B : Matrix m n ℝ) : realMulCLM A B=A*B := rfl

theorem realMul_contDiffAt {l : Type*} [Fintype l]
    (A : E → Matrix l m ℝ) (B : E → Matrix m n ℝ) (x : E)
    (hA : ContDiffAt ℝ 2 A x) (hB : ContDiffAt ℝ 2 B x) :
    ContDiffAt ℝ 2 (fun y => A y*B y) x := by
  simpa only [Function.comp_def,realMulCLM_apply] using!
    ((realMulCLM (l := l) (m := m) (n := n)).contDiff.contDiffAt.comp x hA).clm_apply hB

theorem rangeProjector_contDiffAt (B : E → Matrix n r ℝ) (x : E)
    (hB : ContDiffAt ℝ 2 B x) (hli : LinearIndependent ℝ (B x).col) :
    ContDiffAt ℝ 2 (fun y => rangeProjector (B y)) x := by
  have htr : ContDiffAt ℝ 2 (fun y => (B y)ᵀ) x :=
    by simpa only [Function.comp_def,transposeCLM_apply] using!
      (transposeCLM (n := n) (r := r)).contDiff.contDiffAt.comp x hB
  have hgram := realMul_contDiffAt _ _ x htr hB
  have hu := gram_isUnit (B x) hli
  have hinv : ContDiffAt ℝ 2 (fun y => ((B y)ᵀ*B y)⁻¹) x := by
    have hh := (contDiffAt_ringInverse ℝ hu.unit).comp x hgram
    simpa only [Matrix.nonsing_inv_eq_ringInverse,IsUnit.unit_spec] using! hh
  exact realMul_contDiffAt _ _ x (realMul_contDiffAt _ _ x hB hinv) htr

theorem frame_spans_near (A : E → Matrix m n ℝ) (x : E) (C : Matrix m r ℝ)
    (hA : ContinuousAt A x)
    (hli : LinearIndependent ℝ ((A x)ᵀ*C).col)
    (hrank : ∀ᶠ y in 𝓝 x, (A y)ᵀ.rank=Fintype.card r) :
    ∀ᶠ y in 𝓝 x, LinearIndependent ℝ ((A y)ᵀ*C).col ∧
      LinearMap.range ((A y)ᵀ*C).toLin'=LinearMap.range (A y)ᵀ.toLin' := by
  have hc : ContinuousAt (fun y => ((A y)ᵀ*C).col) x := by
    unfold Matrix.col
    fun_prop
  have he := hc.tendsto hli.eventually
  filter_upwards [he,hrank] with y hy hr
  refine ⟨hy,?_⟩
  apply Submodule.eq_of_le_of_finrank_eq
  · rw [Matrix.toLin'_mul]
    exact LinearMap.range_comp_le_range _ _
  · have hb : ((A y)ᵀ*C).rank=Fintype.card r := by
      rw [← Matrix.rank_transpose ((A y)ᵀ*C)]
      have ht : LinearIndependent ℝ (((A y)ᵀ*C)ᵀ).row := by
        simpa only [Matrix.row_transpose] using! hy
      exact ht.rank_matrix
    simpa only [Matrix.rank,← Matrix.toLin'_apply'] using! hb.trans hr.symm

theorem exists_fixed_frame (A : Matrix m n ℝ) :
    ∃ C : Matrix m (Fin Aᵀ.rank) ℝ, LinearIndependent ℝ (Aᵀ*C).col := by
  classical
  let R := LinearMap.range Aᵀ.toLin'
  have hdim : finrank ℝ R=Aᵀ.rank := by rw [Matrix.rank,← Matrix.toLin'_apply']
  let b := Module.finBasisOfFinrankEq ℝ R hdim
  have hb (i : Fin Aᵀ.rank) : ∃ v : m → ℝ, Aᵀ.toLin' v=(b i : n → ℝ) := (b i).property
  choose v hv using hb
  let C : Matrix m (Fin Aᵀ.rank) ℝ := fun j i => v i j
  refine ⟨C,?_⟩
  have he : (Aᵀ*C).col=fun i => (b i : n → ℝ) := by
    funext i
    rw [Matrix.col_mul_eq_mulVec_col]
    exact hv i
  rw [he]
  exact b.linearIndependent.map' R.subtype (LinearMap.ker_eq_bot.mpr R.subtype_injective)

theorem idempotent_covers_matrix (P : Matrix n n ℝ) (D : Matrix n m ℝ)
    (hPP : P*P=P) (hcover : LinearMap.range D.toLin' ≤ LinearMap.range P.toLin') : P*D=D := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  rw [Matrix.toLin'_mul,LinearMap.comp_apply]
  obtain ⟨w,hw⟩ := hcover (show D.toLin' v ∈ LinearMap.range D.toLin' from ⟨v,rfl⟩)
  rw [← hw]
  have hh := congrArg (fun B : Matrix n n ℝ => B.toLin' w) hPP
  simpa only [Matrix.toLin'_mul,LinearMap.comp_apply] using hh

theorem exists_smooth_normal_projector (A : E → Matrix m n ℝ) (x : E)
    (hA : ContDiffAt ℝ 2 A x)
    (hrank : ∀ᶠ y in 𝓝 x, (A y)ᵀ.rank=(A x)ᵀ.rank) :
    ∃ P : E → Matrix n n ℝ, ContDiffAt ℝ 2 P x ∧
      ∀ᶠ y in 𝓝 x, (P y)ᵀ=P y ∧ P y*P y=P y ∧
        P y*(A y)ᵀ=(A y)ᵀ ∧ A y*P y=A y ∧
        LinearMap.range (P y).toLin'=LinearMap.range (A y)ᵀ.toLin' := by
  classical
  obtain ⟨C,hC⟩ := exists_fixed_frame (A x)
  let B : E → Matrix n (Fin (A x)ᵀ.rank) ℝ := fun y => (A y)ᵀ*C
  let P : E → Matrix n n ℝ := fun y => rangeProjector (B y)
  have hAt : ContDiffAt ℝ 2 (fun y => (A y)ᵀ) x := by
    simpa only [Function.comp_def,transposeCLM_apply] using!
      (transposeCLM (n := m) (r := n)).contDiff.contDiffAt.comp x hA
  have hB : ContDiffAt ℝ 2 B x := realMul_contDiffAt _ _ x hAt contDiffAt_const
  refine ⟨P,rangeProjector_contDiffAt B x hB hC,?_⟩
  have he := frame_spans_near A x C hA.continuousAt hC
    (by simpa only [Fintype.card_fin] using! hrank)
  filter_upwards [he] with y hy
  obtain ⟨ht,hpp,hr⟩ := rangeProjector_properties (B y) hy.1
  have hr' : LinearMap.range (P y).toLin'=LinearMap.range (A y)ᵀ.toLin' := hr.trans hy.2
  have hpa : P y*(A y)ᵀ=(A y)ᵀ := idempotent_covers_matrix (P y) (A y)ᵀ hpp hr'.symm.le
  have hap : A y*P y=A y := by
    have htP : (P y)ᵀ=P y := ht
    have hh := congrArg Matrix.transpose hpa
    simpa only [Matrix.transpose_mul,Matrix.transpose_transpose,htP] using! hh
  exact ⟨ht,hpp,hpa,hap,hr'⟩

theorem symmetric_projector_unique (P Q : Matrix n n ℝ)
    (hPt : Pᵀ=P) (hQt : Qᵀ=Q) (hPP : P*P=P) (hQQ : Q*Q=Q)
    (hr : LinearMap.range P.toLin'=LinearMap.range Q.toLin') : P=Q := by
  have hPQ := idempotent_covers_matrix P Q hPP hr.symm.le
  have hQP := idempotent_covers_matrix Q P hQQ hr.le
  have ht : Q*P=Q := by
    simpa only [Matrix.transpose_mul,hPt,hQt] using congrArg Matrix.transpose hPQ
  exact hQP.symm.trans ht

def normalProjector (A : Matrix m n ℝ) : Matrix n n ℝ :=
  rangeProjector (Aᵀ*Classical.choose (exists_fixed_frame A))

theorem normalProjector_properties (A : Matrix m n ℝ) :
    (normalProjector A)ᵀ=normalProjector A ∧ normalProjector A*normalProjector A=normalProjector A ∧
      normalProjector A*Aᵀ=Aᵀ ∧ A*normalProjector A=A ∧
      LinearMap.range (normalProjector A).toLin'=LinearMap.range Aᵀ.toLin' := by
  classical
  let C := Classical.choose (exists_fixed_frame A)
  have hC := Classical.choose_spec (exists_fixed_frame A)
  have he := (frame_spans_near (fun _ : ℝ => A) 0 C continuousAt_const hC
    (by filter_upwards with y; simp only [Fintype.card_fin])).self_of_nhds
  obtain ⟨ht,hpp,hr⟩ := rangeProjector_properties (Aᵀ*C) hC
  have hr' : LinearMap.range (normalProjector A).toLin'=LinearMap.range Aᵀ.toLin' := hr.trans he.2
  have hPA := idempotent_covers_matrix (normalProjector A) Aᵀ hpp hr'.symm.le
  have hAP : A*normalProjector A=A := by
    have htP : (normalProjector A)ᵀ=normalProjector A := ht
    simpa only [Matrix.transpose_mul,Matrix.transpose_transpose,htP] using!
      congrArg Matrix.transpose hPA
  exact ⟨ht,hpp,hPA,hAP,hr'⟩

theorem normalProjector_contDiffAt (A : E → Matrix m n ℝ) (x : E)
    (hA : ContDiffAt ℝ 2 A x)
    (hrank : ∀ᶠ y in 𝓝 x, (A y)ᵀ.rank=(A x)ᵀ.rank) :
    ContDiffAt ℝ 2 (fun y => normalProjector (A y)) x := by
  obtain ⟨P,hP,hprops⟩ := exists_smooth_normal_projector A x hA hrank
  have he : (fun y => normalProjector (A y))=ᶠ[𝓝 x] P := by
    filter_upwards [hprops] with y hy
    obtain ⟨ht,hpp,hpa,hap,hr⟩ := normalProjector_properties (A y)
    exact symmetric_projector_unique _ _ ht hy.1 hpp hy.2.1 (hr.trans hy.2.2.2.2.symm)
  exact hP.congr_of_eventuallyEq he

end NoiseResponse.ConstantRank
