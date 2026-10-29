/- Added by cx on 2026-10-29: exact A4 isotropic resolvent reduction,
   including the null-space term that disappears under a Gram derivative. -/
module

public import NoiseResponse.IsotropicResolventSeries
public import NoiseResponse.IsotropicResponseAlgebra
public import Mathlib.Algebra.GroupWithZero.Commute
public import Mathlib.Tactic

@[expose] public section
set_option maxRecDepth 1900
set_option maxHeartbeats 7000000
noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator
namespace NoiseResponse.IsotropicSpectrum
variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] [Nonempty n]

theorem inverse_commutes_of_commutes (X Y T : Matrix n n ℂ)
    (hXY : X*Y=Y*X) (hXT : X*T=1) (hTX : T*X=1) : T*Y=Y*T := by
  calc
    T*Y = T*Y*(X*T) := by rw [hXT,Matrix.mul_one]
    _ = T*(Y*X)*T := by simp only [Matrix.mul_assoc]
    _ = T*(X*Y)*T := by rw [hXY]
    _ = Y*T := by rw [← Matrix.mul_assoc T X Y,hTX,Matrix.one_mul]

theorem matrixResolvent_commutes (B Y : Matrix n n ℂ) (hB : ‖B‖<1)
    (hBY : B*Y=Y*B) (z : ℂ) (hz : ‖z‖=1) :
    matrixResolvent B z*Y=Y*matrixResolvent B z := by
  apply inverse_commutes_of_commutes (1-z • B) Y
  · simp only [Matrix.sub_mul,Matrix.mul_sub,Matrix.one_mul,Matrix.mul_one,
      Matrix.smul_mul,Matrix.mul_smul,hBY]
  · exact (matrixResolvent_inverse B hB z hz).1
  · exact (matrixResolvent_inverse B hB z hz).2

theorem matrixResolvent_kernel (B N : Matrix n n ℂ) (hB : ‖B‖<1)
    (hBN : B*N=0) (z : ℂ) (hz : ‖z‖=1) : matrixResolvent B z*N=N := by
  have hn : (1-z • B)*N=N := by
    simp only [Matrix.sub_mul,Matrix.one_mul,Matrix.smul_mul,hBN,smul_zero,sub_zero]
  calc
    _ = matrixResolvent B z*((1-z • B)*N) := by rw [hn]
    _ = N := by rw [← Matrix.mul_assoc,(matrixResolvent_inverse B hB z hz).2,Matrix.one_mul]

theorem matrixResolvent_pair_commutes (B : Matrix n n ℂ) (hB : ‖B‖<1)
    (z w : ℂ) (hz : ‖z‖=1) (hw : ‖w‖=1) :
    matrixResolvent B z*matrixResolvent B w=matrixResolvent B w*matrixResolvent B z := by
  have hc := matrixResolvent_commutes B B hB rfl z hz
  symm
  apply inverse_commutes_of_commutes (1-w • B) (matrixResolvent B z)
  · simp only [Matrix.sub_mul,Matrix.mul_sub,Matrix.one_mul,Matrix.mul_one,
      Matrix.smul_mul,Matrix.mul_smul,hc]
  · exact (matrixResolvent_inverse B hB w hw).1
  · exact (matrixResolvent_inverse B hB w hw).2

theorem resolvent_pair_identity (B : Matrix n n ℂ) (hB : ‖B‖<1)
    (z : ℂ) (hz : ‖z‖=1) :
    star z • matrixResolvent B (star z)+z • matrixResolvent B z=
      (2*(z.re : ℂ)) • (matrixResolvent B (star z)*matrixResolvent B z)-
        (2 : ℂ) • (matrixResolvent B (star z)*matrixResolvent B z*B) := by
  let R := matrixResolvent B (star z)
  let T := matrixResolvent B z
  have hzs : ‖star z‖=1 := by simpa only [norm_star] using hz
  have hBT := matrixResolvent_commutes B B hB rfl z hz
  have hRT : R=R*T-z • (R*B*T) := by
    have h := congrArg (fun X : Matrix n n ℂ => R*X) (matrixResolvent_inverse B hB z hz).1
    simpa only [R,T,Matrix.sub_mul,Matrix.mul_sub,Matrix.mul_one,Matrix.one_mul,Matrix.mul_smul,
      Matrix.smul_mul,Matrix.mul_assoc] using h.symm
  have hTR : T=R*T-star z • (R*B*T) := by
    have h := congrArg (fun X : Matrix n n ℂ => X*T) (matrixResolvent_inverse B hB (star z) hzs).2
    simpa only [R,T,Matrix.sub_mul,Matrix.mul_sub,Matrix.mul_one,Matrix.one_mul,Matrix.mul_smul,
      Matrix.smul_mul,Matrix.mul_assoc] using h.symm
  have hzz : star z*z=1 := by
    rw [mul_comm,Complex.star_def,Complex.mul_conj,Complex.normSq_eq_norm_sq,hz]
    norm_num
  have hzz' : z*star z=1 := by rw [mul_comm,hzz]
  have hadd : star z+z=2*(z.re : ℂ) := by
    simpa only [Complex.star_def,add_comm,Complex.ofReal_mul,Complex.ofReal_ofNat] using Complex.add_conj z
  have he : R*B*T=R*T*B := by
    simp only [Matrix.mul_assoc]
    rw [← hBT]
  change star z • R+z • T=_
  calc
    _ = star z • (R*T-z • (R*B*T))+z • (R*T-star z • (R*B*T)) :=
      congrArg₂ (·+·) (congrArg (star z • ·) hRT) (congrArg (z • ·) hTR)
    _ = (star z+z) • (R*T)-(2 : ℂ) • (R*T*B) := by
      simp only [smul_sub,smul_smul,hzz,hzz',one_smul,he]
      module
    _ = _ := by rw [hadd]

theorem gram_null_trace (A Ai : Matrix m n ℂ) (P : Matrix n n ℂ)
    (hAP : A*P=A) (hPA : P*Aᵀ=Aᵀ) :
    ((1-P)*(Aiᵀ*A+Aᵀ*Ai)).trace=0 := by
  have h0 : A*(1-P)=0 := by rw [Matrix.mul_sub,Matrix.mul_one,hAP,sub_self]
  have h1 : (1-P)*Aᵀ=0 := by rw [Matrix.sub_mul,Matrix.one_mul,hPA,sub_self]
  rw [Matrix.mul_add,Matrix.trace_add]
  have he : ((1-P)*(Aiᵀ*A)).trace=0 := by
    rw [Matrix.trace_mul_comm,Matrix.mul_assoc,h0,Matrix.mul_zero,Matrix.trace_zero]
  rw [he,← Matrix.mul_assoc,h1,Matrix.zero_mul,Matrix.trace_zero,add_zero]

theorem isotropic_response_trace (η : ℝ) (hη : η ≠ 0)
    (A Ai : Matrix m n ℂ) (hA : Aᴴ=Aᵀ) (hAi : Aiᴴ=Aiᵀ)
    (P : Matrix n n ℂ) (hPt : Pᵀ=P) (hPH : Pᴴ=P) (hPP : P*P=P)
    (hAP : A*P=A) (hPA : P*Aᵀ=Aᵀ)
    (hB : ‖P-η • (Aᵀ*A)‖<1) (z : ℂ) (hz : ‖z‖=1) :
    (NoiseResponse.Curvature.response η
      (η • ((star z • matrixResolvent (P-η • (Aᵀ*A)) (star z))*Aᵀ))
      Ai (Aiᴴ*A+Aᴴ*Ai)).trace=
      -(1/2 : ℂ)*(((1-(z.re : ℂ)) •
        (matrixResolvent (P-η • (Aᵀ*A)) (star z)*matrixResolvent (P-η • (Aᵀ*A)) z))*
          (Aiᵀ*A+Aᵀ*Ai)).trace := by
  let K := Aᵀ*A
  let B := P-η • K
  let R := matrixResolvent B (star z)
  let T := matrixResolvent B z
  let S := star z • R
  have hzs : ‖star z‖=1 := by simpa only [norm_star] using hz
  have hAT : (Aᵀ)ᴴ=A := by rw [← hA,Matrix.conjTranspose_conjTranspose]
  have hBt : Bᵀ=B := by simp only [B,K,Matrix.transpose_sub,Matrix.transpose_smul,
    Matrix.transpose_mul,Matrix.transpose_transpose,hPt]
  have hBH : Bᴴ=B := by simp only [B,K,Matrix.conjTranspose_sub,Matrix.conjTranspose_smul,
    star_trivial,Matrix.conjTranspose_mul,hA,hAT,hPH]
  have hSH : Sᴴ=z • T := by
    simp only [S,Matrix.conjTranspose_smul,matrixResolvent_adjoint B hBH,star_star,R,T]
  have hS : Sᵀ=S := by simp only [S,Matrix.transpose_smul,R,matrixResolvent_transpose B hBt]
  have hSHt : (Sᴴ)ᵀ=Sᴴ := by
    rw [hSH]
    simp only [Matrix.transpose_smul,T,matrixResolvent_transpose B hBt]
  have hPK : P*K=K := by simp only [K,← Matrix.mul_assoc,hPA]
  have hKP : K*P=K := by simp only [K,Matrix.mul_assoc,hAP]
  have hBK : B*K=K*B := by
    simp only [B,Matrix.sub_mul,Matrix.mul_sub,Matrix.smul_mul,Matrix.mul_smul,hPK,hKP]
  have hSK : S*K=K*S := by
    simpa only [S,Matrix.smul_mul,Matrix.mul_smul] using
      congrArg (star z • ·) (matrixResolvent_commutes B K hB hBK (star z) hzs)
  have hzz : star z*z=1 := by
    rw [mul_comm,Complex.star_def,Complex.mul_conj,Complex.normSq_eq_norm_sq,hz]
    norm_num
  have hprod : S*Sᴴ=R*T := by
    rw [hSH]
    simp only [S,Matrix.smul_mul,Matrix.mul_smul,smul_smul,mul_comm z (star z),hzz,one_smul]
  have hBN : B*(1-P)=0 := by
    simp only [B,Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_one,Matrix.smul_mul,hPP,hKP,
      sub_self,smul_zero]
  have hN : R*T*(1-P)=1-P := by
    rw [Matrix.mul_assoc,matrixResolvent_kernel B (1-P) hB hBN z hz,
      matrixResolvent_kernel B (1-P) hB hBN (star z) hzs]
  have hRP : R*T*P=R*T-(1-P) := by
    have he : R*T-(R*T*P)=1-P := by
      simpa only [Matrix.mul_sub,Matrix.mul_one] using hN
    exact eq_sub_iff_add_eq.mpr ((add_comm _ _).trans (sub_eq_iff_eq_add.mp he).symm)
  have hfield : S+Sᴴ-(2*η : ℝ) • (S*Sᴴ*K)=
      (-(2 : ℂ)*(1-(z.re : ℂ))) • (R*T)+(2 : ℂ) • (1-P) := by
    calc
      _ = (2*(z.re : ℂ)) • (R*T)-(2 : ℂ) • (R*T*B)-
          (2*η : ℝ) • (R*T*K) := by
        rw [hprod,hSH]
        change star z • R+z • T-_= _
        rw [resolvent_pair_identity B hB z hz]
      _ = _ := by
        rw [show R*T*B=R*T*P-η • (R*T*K) by
          simp only [B,Matrix.mul_sub,Matrix.mul_smul],hRP]
        simp only [Complex.real_smul,smul_sub,smul_smul]
        push_cast
        module
  change (NoiseResponse.Curvature.response η (η • (S*Aᵀ)) Ai _).trace=_
  rw [gram_response_trace η hη A Ai hA hAi S hS hSHt hSK,hfield]
  simp only [Matrix.add_mul,Matrix.smul_mul,Matrix.trace_add,Matrix.trace_smul,
    gram_null_trace A Ai P hAP hPA,smul_eq_mul,mul_zero,add_zero]
  ring

end NoiseResponse.IsotropicSpectrum
