/- Added by cx on 2026-10-29: trace primitives on a moving idempotent
   support. Derivatives of the support cancel by proved cyclic identities,
   so zero eigenvalues are handled without differentiating eigenvalues. -/
module

public import NoiseResponse.CyclicTraceSeries
public import NoiseResponse.MatrixCalculus
public import Mathlib.Tactic

@[expose] public section
set_option maxRecDepth 1600
set_option maxHeartbeats 6000000
noncomputable section
open Filter Set ContinuousLinearMap
open scoped Topology
namespace NoiseResponse.TraceSeries
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [NormOneClass A]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem idempotent_trace_variation (L : A →L[ℝ] ℝ)
    (hcyc : ∀ X Y : A, L (X*Y)=L (Y*X)) (P D : A)
    (hP : P*P=P) (hD : P*D+D*P=D) : P*D*P=0 ∧ L D=0 := by
  have hcorner : P*D*P=0 := by
    have he := congrArg (fun X : A => P*X) hD
    simp only [mul_add, ← mul_assoc, hP] at he
    exact add_eq_left.mp he
  have hPD : L (P*D)=0 := by
    calc
      _ = L ((P*P)*D) := by rw [hP]
      _ = L (P*D*P) := by rw [mul_assoc, hcyc P (P*D)]
      _ = 0 := by rw [hcorner,map_zero]
  have he := congrArg L hD
  rw [map_add,hcyc D P,hPD,zero_add] at he
  exact ⟨hcorner,he.symm⟩

theorem supported_trace_variation (L : A →L[ℝ] ℝ)
    (hcyc : ∀ X Y : A, L (X*Y)=L (Y*X)) (P D X : A)
    (hcorner : P*D*P=0) (hPX : P*X=X) (hXP : X*P=X) : L (X*D)=0 := by
  calc
    _ = L ((P*X)*D) := by rw [hPX]
    _ = L (X*D*P) := by rw [mul_assoc,hcyc P (X*D)]
    _ = L ((X*P)*D*P) := by rw [hXP]
    _ = L (X*(P*D*P)) := by simp only [mul_assoc]
    _ = 0 := by rw [hcorner,mul_zero,map_zero]

theorem supported_power_trace_variation (L : A →L[ℝ] ℝ)
    (hcyc : ∀ X Y : A, L (X*Y)=L (Y*X)) (P D B : A)
    (hP : P*P=P) (hD : P*D+D*P=D) (hPB : P*B=B) (hBP : B*P=B) (n : ℕ) :
    L (B^n*D)=0 := by
  obtain ⟨hcorner,htrace⟩ := idempotent_trace_variation L hcyc P D hP hD
  cases n with
  | zero => simpa only [pow_zero,one_mul] using htrace
  | succ n =>
      apply supported_trace_variation L hcyc P D (B^(n+1)) hcorner
      · rw [pow_succ', ← mul_assoc, hPB]
      · rw [pow_succ, mul_assoc, hBP]

theorem coefficientSeries_trace_variation (L : A →L[ℝ] ℝ)
    (hcyc : ∀ X Y : A, L (X*Y)=L (Y*X)) (c : ℕ → ℝ) (P D B : A)
    (hP : P*P=P) (hD : P*D+D*P=D) (hPB : P*B=B) (hBP : B*P=B)
    (hs : Summable (fun n => c n • B^n)) : L (coefficientSeries c B*D)=0 := by
  let T : A →L[ℝ] ℝ := (ContinuousLinearMap.apply ℝ ℝ D).comp (traceLeftCLM L)
  change T (coefficientSeries c B)=0
  rw [coefficientSeries,T.map_tsum hs]
  calc
    _ = ∑' n : ℕ, (0 : ℝ) := by
      apply tsum_congr
      intro n
      rw [map_smul]
      change c n*L (B^n*D)=0
      rw [supported_power_trace_variation L hcyc P D B hP hD hPB hBP n,mul_zero]
    _ = 0 := tsum_zero

theorem idempotent_field_derivative (P : E → A) (x v : E)
    (hP : DifferentiableAt ℝ P x) (hPP : ∀ᶠ y in 𝓝 x, P y*P y=P y) :
    P x*fderiv ℝ P x v+fderiv ℝ P x v*P x=fderiv ℝ P x v := by
  have hl := NoiseResponse.MatrixCalculus.hasDerivAt_line hP v
  have ht : Tendsto (fun t : ℝ => x+t • v) (𝓝 0) (𝓝 x) := by
    have hc : Continuous (fun t : ℝ => x+t • v) := by fun_prop
    simpa only [zero_smul,add_zero] using hc.tendsto 0
  have he := (hl.mul hl).unique (hl.congr_of_eventuallyEq (ht hPP))
  simpa only [zero_smul,add_zero,add_comm] using he

def supportedPotential (L : A →L[ℝ] ℝ) (c : ℕ → ℝ) (η : ℝ)
    (P H : E → A) (x : E) : ℝ := -(2*η)⁻¹*tracePrimitive L c (P x-η • H x)

theorem supportedPotential_derivative (L : A →L[ℝ] ℝ)
    (hcyc : ∀ X Y : A, L (X*Y)=L (Y*X)) (c : ℕ → ℝ) (η : ℝ) (hη : η ≠ 0)
    (P H : E → A) (x : E) (hP : DifferentiableAt ℝ P x) (hH : DifferentiableAt ℝ H x)
    (hPP : ∀ᶠ y in 𝓝 x, P y*P y=P y) (hPH : P x*H x=H x) (hHP : H x*P x=H x)
    (q : ℝ) (hX : ‖P x-η • H x‖<q) (hs : Summable (fun n => ‖c n‖*q^n)) :
    HasFDerivAt (supportedPotential L c η P H)
      ((1/2 : ℝ) • ((traceLeftCLM L (coefficientSeries c (P x-η • H x))).comp (fderiv ℝ H x))) x := by
  let B := P x-η • H x
  have hq0 : 0 ≤ q := le_of_lt (lt_of_le_of_lt (norm_nonneg _) hX)
  have hsum := coefficientSeries_summable c B q hq0 hX.le hs
  have hPB : P x*B=B := by dsimp only [B]; rw [mul_sub,mul_smul_comm,hPP.self_of_nhds,hPH]
  have hBP : B*P x=B := by dsimp only [B]; rw [sub_mul,smul_mul_assoc,hPP.self_of_nhds,hHP]
  have hp := tracePrimitive_hasFDerivAt L hcyc c B q hX hs
  have hc := hp.comp x (hP.hasFDerivAt.sub (hH.hasFDerivAt.const_smul η))
  have hh := hc.const_smul (-(2*η)⁻¹)
  convert! hh using 1
  ext v
  have hkill := coefficientSeries_trace_variation L hcyc c (P x) (fderiv ℝ P x v) B
    hPP.self_of_nhds (idempotent_field_derivative P x v hP hPP) hPB hBP hsum
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    traceLeftCLM_apply, ContinuousLinearMap.sub_apply, mul_sub, mul_smul_comm,
    map_sub,map_smul,smul_eq_mul,hkill,zero_sub]
  change (1/2 : ℝ)*L (coefficientSeries c B*fderiv ℝ H x v)=
    -(2*η)⁻¹*(-(η*L (coefficientSeries c B*fderiv ℝ H x v)))
  field_simp
  <;> ring

end NoiseResponse.TraceSeries

#print axioms NoiseResponse.TraceSeries.supportedPotential_derivative
