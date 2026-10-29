/- Added by cx on 2026-10-29: actual stable transfers, the zero
   pseudoinverse, and the output range projector for a constant-rank field. -/
module

public import NoiseResponse.IsotropicPotentialCalculus
public import NoiseResponse.GeneralZeroEndpoint
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Tactic

@[expose] public section
set_option maxRecDepth 1900
set_option maxHeartbeats 7000000
noncomputable section
open Matrix Filter
open scoped Topology Matrix.Norms.L2Operator
namespace NoiseResponse.RankSafe
open NoiseResponse.IsotropicSpectrum
variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] [Nonempty n]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
local instance : NormedAlgebra ℝ (Matrix n n ℂ) where
  norm_smul_le := norm_smul_le

def normalFilter (η : ℝ) (A : Matrix m n ℂ) (P : Matrix n n ℂ) : Matrix n n ℂ := P-η • (Aᴴ*A)

def transfer (η : ℝ) (A : Matrix m n ℂ) (P : Matrix n n ℂ) (z : ℂ) : Matrix n m ℂ :=
  η • ((star z • matrixResolvent (normalFilter η A P) (star z))*Aᴴ)

def outputProjector (η : ℝ) (A : Matrix m n ℂ) (P : Matrix n n ℂ) : Matrix m m ℂ :=
  A*transfer η A P 1

theorem matrixResolvent_contDiffAt (B : E → Matrix n n ℂ) (x : E)
    (hB : ContDiffAt ℝ 2 B x) (hb : ‖B x‖<1) (z : ℂ) (hz : ‖z‖=1) :
    ContDiffAt ℝ 2 (fun y => matrixResolvent (B y) z) x := by
  have hu : IsUnit (1-z • B x) := isUnit_one_sub_of_norm_lt_one
    (by simpa only [norm_smul,hz,one_mul] using hb)
  have hh := (contDiffAt_ringInverse ℝ hu.unit).comp x (contDiffAt_const.sub (hB.const_smul z))
  simpa only [matrixResolvent,IsUnit.unit_spec] using! hh

theorem normalFilter_contDiffAt (η : ℝ) (A : E → Matrix m n ℂ) (P : E → Matrix n n ℂ)
    (x : E) (hA : ContDiffAt ℝ 2 A x) (hP : ContDiffAt ℝ 2 P x) :
    ContDiffAt ℝ 2 (fun y => normalFilter η (A y) (P y)) x := by
  have hAH := (adjointRealCLM (m := m) (n := n)).contDiff.contDiffAt.comp x hA
  have hgram := ((complexMulCLM (l := n) (m := m) (n := n)).contDiff.contDiffAt.comp x hAH).clm_apply hA
  simpa only [Function.comp_def,adjointRealCLM_apply,complexMulCLM_apply,normalFilter] using!
    hP.sub (hgram.const_smul η)

theorem transfer_contDiffAt (η : ℝ) (A : E → Matrix m n ℂ) (P : E → Matrix n n ℂ)
    (x : E) (hA : ContDiffAt ℝ 2 A x) (hP : ContDiffAt ℝ 2 P x)
    (hb : ‖normalFilter η (A x) (P x)‖<1) (z : ℂ) (hz : ‖z‖=1) :
    ContDiffAt ℝ 2 (fun y => transfer η (A y) (P y) z) x := by
  have hr := matrixResolvent_contDiffAt _ x (normalFilter_contDiffAt η A P x hA hP) hb
    (star z) (by simpa only [norm_star] using hz)
  have hAH := (adjointRealCLM (m := m) (n := n)).contDiff.contDiffAt.comp x hA
  have hm := ((complexMulCLM (l := n) (m := n) (n := m)).contDiff.contDiffAt.comp x
    (hr.const_smul (star z))).clm_apply hAH
  simpa only [Function.comp_def,complexMulCLM_apply,adjointRealCLM_apply,transfer] using! hm.const_smul η

theorem zero_transfer_right (η : ℝ) (A : Matrix m n ℂ) (P : Matrix n n ℂ)
    (hPP : P*P=P) (hAP : A*P=A) (hPA : P*Aᴴ=Aᴴ)
    (hb : ‖normalFilter η A P‖<1) : transfer η A P 1*A=P := by
  let B := normalFilter η A P
  let R := matrixResolvent B 1
  have hPK : P*(Aᴴ*A)=Aᴴ*A := by rw [← Matrix.mul_assoc,hPA]
  have hKP : (Aᴴ*A)*P=Aᴴ*A := by rw [Matrix.mul_assoc,hAP]
  have hBN : B*(1-P)=0 := by
    simp only [B,normalFilter,Matrix.sub_mul,Matrix.mul_sub,Matrix.smul_mul,Matrix.mul_one,
      hPP,hKP,sub_self]
  have hRN : R*(1-P)=1-P := matrixResolvent_kernel B (1-P) hb hBN 1 (by simp)
  have hR : R*(1-B)=1 := by
    simpa only [one_smul] using (matrixResolvent_inverse B hb 1 (by simp)).2
  have hden : 1-B=1-P+η • (Aᴴ*A) := by dsimp only [B,normalFilter]; abel
  have hh : η • (R*(Aᴴ*A))=P := by
    rw [hden,Matrix.mul_add,Matrix.mul_smul,hRN] at hR
    have he : η • (R*(Aᴴ*A))=1-(1-P) :=
      eq_sub_of_add_eq (by simpa only [add_comm] using hR)
    simpa only [sub_sub_cancel] using he
  simpa only [transfer,star_one,one_smul,Matrix.smul_mul,Matrix.mul_assoc,R,B] using! hh

theorem zero_output_projector (η : ℝ) (A : Matrix m n ℂ) (P : Matrix n n ℂ)
    (hPP : P*P=P) (hPH : Pᴴ=P) (hAP : A*P=A) (hPA : P*Aᴴ=Aᴴ)
    (hb : ‖normalFilter η A P‖<1) :
    (outputProjector η A P)ᴴ=outputProjector η A P ∧
      outputProjector η A P*outputProjector η A P=outputProjector η A P ∧
      outputProjector η A P*A=A ∧
      LinearMap.range (outputProjector η A P).toLin'=LinearMap.range A.toLin' := by
  have hBH : (normalFilter η A P)ᴴ=normalFilter η A P := by
    simp only [normalFilter,Matrix.conjTranspose_sub,Matrix.conjTranspose_smul,
      star_trivial,Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,hPH]
  have hRH : (matrixResolvent (normalFilter η A P) 1)ᴴ=matrixResolvent (normalFilter η A P) 1 := by
    simpa only [star_one] using matrixResolvent_adjoint _ hBH 1
  have hEA : outputProjector η A P*A=A := by
    rw [outputProjector,Matrix.mul_assoc,zero_transfer_right η A P hPP hAP hPA hb,hAP]
  refine ⟨?_,?_,hEA,?_⟩
  · simp only [outputProjector,transfer,star_one,one_smul,Matrix.mul_smul,
      Matrix.conjTranspose_smul,star_trivial,Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose,hRH,Matrix.mul_assoc]
  · change outputProjector η A P*(A*transfer η A P 1)=outputProjector η A P
    rw [← Matrix.mul_assoc,hEA]
    rfl
  · apply le_antisymm
    · rw [outputProjector,Matrix.toLin'_mul]
      exact LinearMap.range_comp_le_range _ _
    · intro v hv
      obtain ⟨w,rfl⟩ := hv
      refine ⟨A.toLin' w,?_⟩
      have hh := congrArg (fun D : Matrix m n ℂ => D.toLin' w) hEA
      simpa only [Matrix.toLin'_mul,LinearMap.comp_apply] using hh

def nyquistOutputInverse (η : ℝ) (A : Matrix m n ℂ) (P : Matrix n n ℂ) : Matrix m m ℂ :=
  (1/2 : ℝ) • 1+(η/2 : ℝ) • (A*matrixResolvent (normalFilter η A P) (-1)*Aᴴ)

theorem nyquistOutputInverse_right (η : ℝ) (A : Matrix m n ℂ) (P : Matrix n n ℂ)
    (hAP : A*P=A) (hb : ‖normalFilter η A P‖<1) :
    NoiseResponse.Classification.nyquistResolventDen η (A*Aᴴ)*nyquistOutputInverse η A P=1 := by
  let B := normalFilter η A P
  let R := matrixResolvent B (-1)
  have hR : (1+B)*R=1 := by
    simpa only [neg_smul,one_smul,sub_neg_eq_add] using
      (matrixResolvent_inverse B hb (-1) (by norm_num)).1
  have hk : NoiseResponse.Classification.nyquistResolventDen η (A*Aᴴ)*(A*R*Aᴴ)=A*Aᴴ := by
    calc
      _ = A*((1+B)*R)*Aᴴ := by
        simp only [NoiseResponse.Classification.nyquistResolventDen,B,normalFilter,
          Matrix.sub_mul,Matrix.add_mul,Matrix.mul_sub,Matrix.mul_add,Matrix.smul_mul,
          Matrix.mul_smul,Matrix.one_mul,Matrix.mul_one,← Matrix.mul_assoc,hAP]
        module
      _ = _ := by rw [hR,Matrix.mul_one]
  unfold nyquistOutputInverse
  rw [Matrix.mul_add,Matrix.mul_smul,Matrix.mul_smul,Matrix.mul_one,hk]
  simp only [NoiseResponse.Classification.nyquistResolventDen,smul_sub,smul_smul]
  module

theorem nyquist_transfer_eq (η : ℝ) (A : Matrix m n ℂ) (P : Matrix n n ℂ)
    (hAP : A*P=A) (hPA : P*Aᴴ=Aᴴ) (hb : ‖normalFilter η A P‖<1) :
    transfer η A P (-1)=-η • (Aᴴ*nyquistOutputInverse η A P) := by
  let B := normalFilter η A P
  let R := matrixResolvent B (-1)
  let T := nyquistOutputInverse η A P
  have hR : R*(1+B)=1 := by
    simpa only [neg_smul,one_smul,sub_neg_eq_add] using
      (matrixResolvent_inverse B hb (-1) (by norm_num)).2
  have hi : (1+B)*Aᴴ=Aᴴ*NoiseResponse.Classification.nyquistResolventDen η (A*Aᴴ) := by
    simp only [B,normalFilter,NoiseResponse.Classification.nyquistResolventDen,
      Matrix.add_mul,Matrix.sub_mul,Matrix.mul_sub,Matrix.smul_mul,Matrix.mul_smul,
      Matrix.one_mul,Matrix.mul_one,hPA,Matrix.mul_assoc]
    module
  have he : R*Aᴴ=Aᴴ*T := by
    calc
      _ = R*(Aᴴ*(NoiseResponse.Classification.nyquistResolventDen η (A*Aᴴ)*T)) := by
        rw [nyquistOutputInverse_right η A P hAP hb,Matrix.mul_one]
      _ = R*((1+B)*Aᴴ)*T := by rw [hi]; simp only [Matrix.mul_assoc]
      _ = Aᴴ*T := by rw [← Matrix.mul_assoc R (1+B),hR,Matrix.one_mul]
  simp only [transfer,star_neg,star_one,neg_smul,one_smul,Matrix.neg_mul,smul_neg]
  simpa only [R,T,B] using! congrArg (fun D : Matrix n m ℂ => -(η • D)) he

theorem nyquistOutputInverse_contDiffAt (η : ℝ) (A : E → Matrix m n ℂ)
    (P : E → Matrix n n ℂ) (x : E)
    (hA : ContDiffAt ℝ 2 A x) (hP : ContDiffAt ℝ 2 P x)
    (hb : ‖normalFilter η (A x) (P x)‖<1) :
    ContDiffAt ℝ 2 (fun y => nyquistOutputInverse η (A y) (P y)) x := by
  have hr := matrixResolvent_contDiffAt _ x (normalFilter_contDiffAt η A P x hA hP) hb
    (-1) (by norm_num)
  have hAH := (adjointRealCLM (m := m) (n := n)).contDiff.contDiffAt.comp x hA
  have hAR := ((complexMulCLM (l := m) (m := n) (n := n)).contDiff.contDiffAt.comp x hA).clm_apply hr
  have hprod := ((complexMulCLM (l := m) (m := n) (n := m)).contDiff.contDiffAt.comp x hAR).clm_apply hAH
  simpa only [Function.comp_def,complexMulCLM_apply,adjointRealCLM_apply,nyquistOutputInverse] using!
    contDiffAt_const.add (hprod.const_smul (η/2))

end NoiseResponse.RankSafe
