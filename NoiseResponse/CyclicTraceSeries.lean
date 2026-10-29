/- Added by cx on 2026-10-29: a genuine noncommutative trace-series
   primitive. Cyclicity proves its derivative; no eigenvalue derivatives
   or pre-existing potential identity are supplied as assumptions. -/
module

public import Mathlib.Analysis.Calculus.FDeriv.Pow
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.Analysis.Analytic.ChangeOrigin
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Tactic

@[expose] public section
set_option maxRecDepth 1600
set_option maxHeartbeats 6000000
noncomputable section
open Filter Set ContinuousLinearMap
open scoped Topology RightActions NNReal ENNReal
namespace NoiseResponse.TraceSeries
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [NormOneClass A]

def traceLeftCLM (L : A →L[ℝ] ℝ) : A →L[ℝ] A →L[ℝ] ℝ :=
  ((ContinuousLinearMap.compL ℝ A A ℝ) L).comp (ContinuousLinearMap.mul ℝ A)

@[simp] theorem traceLeftCLM_apply (L : A →L[ℝ] ℝ) (X V : A) :
    traceLeftCLM L X V=L (X*V) := rfl

theorem traceLeftCLM_norm (L : A →L[ℝ] ℝ) (X : A) :
    ‖traceLeftCLM L X‖ ≤ ‖L‖*‖X‖ := by
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_mul_apply_le ℝ A X) (norm_nonneg L))

theorem trace_power_derivative (L : A →L[ℝ] ℝ)
    (hcyc : ∀ X Y : A, L (X*Y)=L (Y*X)) (n : ℕ) (X : A) :
    HasFDerivAt (fun Y : A => L (Y^(n+1)))
      ((n+1 : ℝ) • traceLeftCLM L (X^n)) X := by
  have hp := L.hasFDerivAt.comp X (hasFDerivAt_pow' (𝕜 := ℝ) (n+1) (x := X))
  convert! hp using 1
  ext V
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    traceLeftCLM_apply, ContinuousLinearMap.sum_apply, smul_eq_mul]
  have hterm (i : ℕ) (hi : i ∈ Finset.range (n+1)) :
      L (X^(n-i)*V*X^i)=L (X^n*V) := by
    have hn : n-i+i=n := Nat.sub_add_cancel (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hi)
    rw [hcyc _ (X^i)]
    simp only [← mul_assoc, ← pow_add, Nat.add_comm i (n-i), hn]
  rw [map_sum]
  change (n+1 : ℝ)*L (X^n*V)=∑ i ∈ Finset.range (n+1), L (X^(n-i)*V*X^i)
  rw [Finset.sum_congr rfl (fun i hi => hterm i hi)]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]

def primitiveTerm (L : A →L[ℝ] ℝ) (c : ℕ → ℝ) (n : ℕ) (X : A) : ℝ :=
  c n/(n+1 : ℝ)*L (X^(n+1))

def tracePrimitive (L : A →L[ℝ] ℝ) (c : ℕ → ℝ) (X : A) : ℝ :=
  ∑' n, primitiveTerm L c n X

def coefficientSeries (c : ℕ → ℝ) (X : A) : A := ∑' n, c n • X^n

theorem primitiveTerm_derivative (L : A →L[ℝ] ℝ)
    (hcyc : ∀ X Y : A, L (X*Y)=L (Y*X)) (c : ℕ → ℝ) (n : ℕ) (X : A) :
    HasFDerivAt (primitiveTerm L c n) (c n • traceLeftCLM L (X^n)) X := by
  have hp := (trace_power_derivative L hcyc n X).const_smul (c n/(n+1 : ℝ))
  have hn : (n+1 : ℝ) ≠ 0 := by positivity
  simpa only [primitiveTerm, Pi.smul_apply, smul_eq_mul, smul_smul, div_mul_cancel₀ _ hn] using! hp

theorem coefficientSeries_summable (c : ℕ → ℝ) (X : A) (q : ℝ)
    (hq : 0 ≤ q) (hX : ‖X‖ ≤ q) (hs : Summable (fun n => ‖c n‖*q^n)) :
    Summable (fun n => c n • X^n) := by
  apply Summable.of_norm_bounded hs
  intro n
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left ((norm_pow_le X n).trans
    (pow_le_pow_left₀ (norm_nonneg X) hX n)) (norm_nonneg _)

theorem primitiveTerm_summable (L : A →L[ℝ] ℝ) (c : ℕ → ℝ) (X : A) (q : ℝ)
    (hq : 0 ≤ q) (hX : ‖X‖ ≤ q) (hs : Summable (fun n => ‖c n‖*q^n)) :
    Summable (fun n => primitiveTerm L c n X) := by
  apply Summable.of_norm_bounded (hs.mul_left (‖L‖*q))
  intro n
  have hc : ‖c n/(n+1 : ℝ)‖ ≤ ‖c n‖ := by
    rw [norm_div, show ‖(n+1 : ℝ)‖=n+1 by
      rw [Real.norm_eq_abs,abs_of_pos (by positivity)]]
    have hn : (1 : ℝ)≤n+1 := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    exact div_le_self (norm_nonneg _) hn
  calc
    _ = ‖c n/(n+1 : ℝ)‖*‖L (X^(n+1))‖ := norm_mul _ _
    _ ≤ ‖c n‖*(‖L‖*q^(n+1)) := mul_le_mul hc
      ((L.le_opNorm _).trans (mul_le_mul_of_nonneg_left
        ((norm_pow_le X (n+1)).trans (pow_le_pow_left₀ (norm_nonneg X) hX _)) (norm_nonneg L)))
      (norm_nonneg _) (norm_nonneg _)
    _ = _ := by rw [pow_succ]; ring

theorem coefficientSeries_analyticAt (c : ℕ → ℝ) (X : A) (q : ℝ)
    (hX : ‖X‖<q) (hs : Summable (fun n => ‖c n‖*q^n)) :
    AnalyticAt ℝ (coefficientSeries c) X := by
  let p := FormalMultilinearSeries.ofScalars A c
  have hq : 0 ≤ q := le_of_lt (lt_of_le_of_lt (norm_nonneg X) hX)
  let r : ℝ≥0 := NNReal.mk q hq
  have hr : ENNReal.ofNNReal r ≤ p.radius := by
    apply p.le_radius_of_summable_norm
    simpa only [p,r,NNReal.coe_mk,FormalMultilinearSeries.ofScalars_norm] using hs
  have hm : X ∈ Metric.eball (0 : A) p.radius := by
    apply Metric.eball_subset_eball hr
    rw [Metric.eball_coe]
    simpa only [Metric.mem_ball,dist_zero_right,r,NNReal.coe_mk] using hX
  have hp := p.analyticOnNhd X hm
  have he : p.sum=coefficientSeries (A := A) c := by
    funext Y
    exact FormalMultilinearSeries.ofScalars_sum_eq c Y
  simpa only [he] using hp

theorem tracePrimitive_hasFDerivAt (L : A →L[ℝ] ℝ)
    (hcyc : ∀ X Y : A, L (X*Y)=L (Y*X)) (c : ℕ → ℝ) (X : A) (q : ℝ)
    (hX : ‖X‖<q) (hs : Summable (fun n => ‖c n‖*q^n)) :
    HasFDerivAt (tracePrimitive L c) (traceLeftCLM L (coefficientSeries c X)) X := by
  have hq : 0<q := lt_of_le_of_lt (norm_nonneg X) hX
  let u : ℕ → ℝ := fun n => ‖L‖*(‖c n‖*q^n)
  have hu : Summable u := hs.mul_left ‖L‖
  have hd (n : ℕ) (Y : A) (_ : Y ∈ Metric.ball 0 q) :
      HasFDerivAt (primitiveTerm L c n) (c n • traceLeftCLM L (Y^n)) Y :=
    primitiveTerm_derivative L hcyc c n Y
  have hb (n : ℕ) (Y : A) (hY : Y ∈ Metric.ball 0 q) :
      ‖c n • traceLeftCLM L (Y^n)‖ ≤ u n := by
    have hn : ‖Y‖ ≤ q := (by simpa only [Metric.mem_ball, dist_zero_right] using hY : ‖Y‖<q).le
    calc
      _ = ‖c n‖*‖traceLeftCLM L (Y^n)‖ := norm_smul _ _
      _ ≤ ‖c n‖*(‖L‖*q^n) := mul_le_mul_of_nonneg_left
        ((traceLeftCLM_norm L (Y^n)).trans (mul_le_mul_of_nonneg_left
          ((norm_pow_le Y n).trans (pow_le_pow_left₀ (norm_nonneg Y) hn n)) (norm_nonneg L)))
          (norm_nonneg _)
      _ = _ := by dsimp [u]; ring
  have hzero : Summable (fun n => primitiveTerm L c n (0 : A)) := by
    simp only [primitiveTerm, zero_pow (Nat.succ_ne_zero _), map_zero, mul_zero]
    exact summable_zero
  have hh := hasFDerivAt_tsum_of_isPreconnected hu Metric.isOpen_ball
    (convex_ball (0 : A) q).isPreconnected hd hb (Metric.mem_ball_self hq) hzero
    (show X ∈ Metric.ball 0 q by simpa only [Metric.mem_ball, dist_zero_right] using hX)
  have hsum := coefficientSeries_summable c X q hq.le hX.le hs
  have he : (∑' n, c n • traceLeftCLM L (X^n))=traceLeftCLM L (coefficientSeries c X) := by
    rw [coefficientSeries, (traceLeftCLM L).map_tsum hsum]
    simp only [map_smul]
  simpa only [tracePrimitive, he] using! hh

theorem tracePrimitive_contDiffAt (L : A →L[ℝ] ℝ)
    (hcyc : ∀ X Y : A, L (X*Y)=L (Y*X)) (c : ℕ → ℝ) (X : A) (q : ℝ)
    (hX : ‖X‖<q) (hs : Summable (fun n => ‖c n‖*q^n)) :
    ContDiffAt ℝ 2 (tracePrimitive L c) X := by
  have hq : 0<q := lt_of_le_of_lt (norm_nonneg X) hX
  apply contDiffAt_succ_iff_hasFDerivAt.mpr
  refine ⟨fun Y => traceLeftCLM L (coefficientSeries c Y),?_,?_⟩
  · refine ⟨Metric.ball 0 q,?_,?_⟩
    · exact Metric.isOpen_ball.mem_nhds (by simpa only [Metric.mem_ball,dist_zero_right] using hX)
    · intro Y hY
      exact tracePrimitive_hasFDerivAt L hcyc c Y q
        (by simpa only [Metric.mem_ball,dist_zero_right] using hY) hs
  · exact ((traceLeftCLM L).analyticAt _ |>.comp (coefficientSeries_analyticAt c X q hX hs)).contDiffAt

end NoiseResponse.TraceSeries

#print axioms NoiseResponse.TraceSeries.tracePrimitive_hasFDerivAt
