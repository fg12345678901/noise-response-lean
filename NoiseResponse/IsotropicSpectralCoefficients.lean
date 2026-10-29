/- Added by cx on 2026-10-29: scalar coefficients and an explicit
   convergent primitive for every finite positive isotropic spectrum. -/
module

public import NoiseResponse.CyclicTraceSeries
public import NoiseResponse.RankOneSpectralKernel
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Tactic

@[expose] public section
set_option maxRecDepth 1800
set_option maxHeartbeats 6000000
noncomputable section
open Filter Set MeasureTheory Complex
open scoped Topology ComplexConjugate
namespace NoiseResponse.IsotropicSpectrum
open NoiseResponse.Classification
variable {Ω : Type*} [MeasurableSpace Ω]

def doubleCoeff (z : ℂ) (n : ℕ) : ℂ :=
  ∑ k ∈ Finset.range (n+1), z^k*(star z)^(n-k)

def poissonCoeff (z : ℂ) (n : ℕ) : ℝ := (1-z.re)*(doubleCoeff z n).re

def scalarKernel (a : ℝ) (z : ℂ) : ℝ := (1-z.re)*(normalPowerKernel a z).re

theorem doubleCoeff_norm (z : ℂ) (hz : ‖z‖=1) (n : ℕ) : ‖doubleCoeff z n‖ ≤ n+1 := by
  unfold doubleCoeff
  calc
    _ ≤ ∑ k ∈ Finset.range (n+1), ‖z^k*(star z)^(n-k)‖ := norm_sum_le _ _
    _ = _ := by simp only [norm_mul, norm_pow, norm_star, hz, one_pow, one_mul,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one, mul_one]

theorem poissonCoeff_bound (z : ℂ) (hz : ‖z‖=1) (n : ℕ) :
    ‖poissonCoeff z n‖ ≤ 2*(n+1) := by
  have hr : |z.re| ≤ 1 := (Complex.abs_re_le_norm z).trans_eq hz
  have h1 : |1-z.re| ≤ 2 := by
    calc
      _ ≤ |(1 : ℝ)|+|z.re| := abs_sub _ _
      _ ≤ 2 := by rw [abs_one]; linarith
  unfold poissonCoeff
  rw [norm_mul]
  exact (mul_le_mul h1 ((Complex.abs_re_le_norm _).trans (doubleCoeff_norm z hz n))
    (abs_nonneg _) (by norm_num)).trans_eq (by rfl)

theorem linear_geometric_summable (q : ℝ) (hq0 : 0 ≤ q) (hq : q<1) :
    Summable (fun n : ℕ => (n+1 : ℝ)*q^n) := by
  have hn := (hasSum_coe_mul_geometric_of_norm_lt_one
    (show ‖q‖<1 by simpa only [Real.norm_eq_abs, abs_of_nonneg hq0] using hq)).summable
  have hg := summable_geometric_of_lt_one hq0 hq
  simpa only [add_mul, one_mul] using hn.add hg

theorem normalPowerKernel_hasSum (a : ℝ) (ha : ‖a‖<1) (z : ℂ) (hz : ‖z‖=1) :
    HasSum (fun n : ℕ => (a : ℂ)^n*doubleCoeff z n) (normalPowerKernel a z) := by
  have hp : ‖(a : ℂ)*z‖<1 := by simpa only [norm_mul, Complex.norm_real, hz, mul_one] using ha
  have hm : ‖(a : ℂ)*star z‖<1 := by
    simpa only [norm_mul, Complex.norm_real, norm_star, hz, mul_one] using ha
  have hps : Summable (fun n : ℕ => ‖((a : ℂ)*z)^n‖) := by
    simpa only [norm_pow] using summable_geometric_of_lt_one (norm_nonneg _) hp
  have hms : Summable (fun n : ℕ => ‖((a : ℂ)*star z)^n‖) := by
    simpa only [norm_pow] using summable_geometric_of_lt_one (norm_nonneg _) hm
  have hc := hasSum_sum_range_mul_of_summable_norm hps hms
  have hterm (n : ℕ) :
      (∑ k ∈ Finset.range (n+1), ((a : ℂ)*z)^k*((a : ℂ)*star z)^(n-k))=
        (a : ℂ)^n*doubleCoeff z n := by
    unfold doubleCoeff
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hn : k+(n-k)=n := Nat.add_sub_of_le (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hk)
    rw [mul_pow, mul_pow]
    calc
      _ = ((a : ℂ)^k*(a : ℂ)^(n-k))*(z^k*(star z)^(n-k)) := by ring
      _ = _ := by rw [← pow_add, hn]
  have hval : ((∑' n : ℕ, ((a : ℂ)*z)^n)*(∑' n : ℕ, ((a : ℂ)*star z)^n))=
      normalPowerKernel a z := by
    rw [(hasSum_geometric_of_norm_lt_one hp).tsum_eq,
      (hasSum_geometric_of_norm_lt_one hm).tsum_eq]
    simp only [normalPowerKernel, one_div, mul_inv_rev, mul_comm]
  simpa only [hterm,hval] using hc

theorem scalarKernel_hasSum (a : ℝ) (ha : ‖a‖<1) (z : ℂ) (hz : ‖z‖=1) :
    HasSum (fun n => poissonCoeff z n*a^n) (scalarKernel a z) := by
  have hp := (normalPowerKernel_hasSum a ha z hz).mapL Complex.reCLM
  have hc := hp.const_smul (1-z.re)
  simpa only [poissonCoeff, scalarKernel, Complex.reCLM_apply, ← Complex.ofReal_pow,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    smul_eq_mul, mul_assoc, mul_comm (a^_) _] using! hc

def spectralCoeff (ν : Measure Ω) (z : Ω → ℂ) (n : ℕ) : ℝ := ∫ x, poissonCoeff (z x) n ∂ν

theorem spectralCoeff_bound (ν : Measure Ω) [IsFiniteMeasure ν]
    (z : Ω → ℂ) (hzunit : ∀ x, ‖z x‖=1) (n : ℕ) :
    ‖spectralCoeff ν z n‖ ≤ (2*ν.real univ)*(n+1) := by
  unfold spectralCoeff
  exact (norm_integral_le_of_norm_le_const (Eventually.of_forall
    (fun x => poissonCoeff_bound (z x) (hzunit x) n))).trans_eq (by ring)

theorem spectralCoeff_summable (ν : Measure Ω) [IsFiniteMeasure ν]
    (z : Ω → ℂ) (hzunit : ∀ x, ‖z x‖=1) (q : ℝ) (hq0 : 0 ≤ q) (hq : q<1) :
    Summable (fun n => ‖spectralCoeff ν z n‖*q^n) := by
  apply Summable.of_nonneg_of_le (fun n => by positivity)
    (fun n => mul_le_mul_of_nonneg_right (spectralCoeff_bound ν z hzunit n) (pow_nonneg hq0 n))
  simpa only [mul_assoc] using (linear_geometric_summable q hq0 hq).mul_left (2*ν.real univ)

theorem integrated_kernel_hasSum (ν : Measure Ω) [IsFiniteMeasure ν]
    (z : Ω → ℂ) (hz : Measurable z) (hu : ∀ x, ‖z x‖=1) (a : ℝ) (ha : ‖a‖<1) :
    HasSum (fun n => spectralCoeff ν z n*a^n) (∫ x, scalarKernel a (z x) ∂ν) := by
  let bound : ℕ → Ω → ℝ := fun n _ => 2*(n+1 : ℝ)*‖a‖^n
  have hmeas (n : ℕ) : AEStronglyMeasurable (fun x => poissonCoeff (z x) n*a^n) ν := by
    apply Measurable.aestronglyMeasurable
    unfold poissonCoeff doubleCoeff
    fun_prop
  have hb (n : ℕ) : ∀ᵐ x ∂ν, ‖poissonCoeff (z x) n*a^n‖ ≤ bound n x := by
    apply Eventually.of_forall
    intro x
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_right (poissonCoeff_bound (z x) (hu x) n) (by positivity)
  have hs : Summable (fun n : ℕ => 2*(n+1 : ℝ)*‖a‖^n) := by
    simpa only [mul_assoc] using (linear_geometric_summable ‖a‖ (norm_nonneg _) ha).mul_left 2
  have hInt : Integrable (fun x => ∑' n, bound n x) ν := by
    exact integrable_const (∑' n : ℕ, 2*(n+1 : ℝ)*‖a‖^n)
  have hp := hasSum_integral_of_dominated_convergence bound hmeas hb
    (Eventually.of_forall (fun _ => hs)) hInt
    (Eventually.of_forall (fun x => scalarKernel_hasSum a ha (z x) (hu x)))
  simpa only [integral_mul_const, spectralCoeff] using hp

def scalarPrimitive (ν : Measure Ω) (z : Ω → ℂ) (a : ℝ) : ℝ :=
  NoiseResponse.TraceSeries.tracePrimitive (ContinuousLinearMap.id ℝ ℝ) (spectralCoeff ν z) a

theorem scalarPrimitive_derivative (ν : Measure Ω) [IsFiniteMeasure ν]
    (z : Ω → ℂ) (hz : Measurable z) (hu : ∀ x, ‖z x‖=1) (a : ℝ) (ha : ‖a‖<1) :
    HasDerivAt (scalarPrimitive ν z) (∫ x, scalarKernel a (z x) ∂ν) a := by
  let q := (‖a‖+1)/2
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hq1 : q<1 := by dsimp only [q]; linarith
  have haq : ‖a‖<q := by dsimp only [q]; linarith
  have hd := NoiseResponse.TraceSeries.tracePrimitive_hasFDerivAt (ContinuousLinearMap.id ℝ ℝ)
    (fun X Y => mul_comm X Y) (spectralCoeff ν z) a q haq (spectralCoeff_summable ν z hu q hq0 hq1)
  have he : NoiseResponse.TraceSeries.coefficientSeries (spectralCoeff ν z) a=
      ∫ x, scalarKernel a (z x) ∂ν := by
    simpa only [NoiseResponse.TraceSeries.coefficientSeries, smul_eq_mul] using
      (integrated_kernel_hasSum ν z hz hu a ha).tsum_eq
  simpa only [scalarPrimitive, NoiseResponse.TraceSeries.traceLeftCLM_apply,
    ContinuousLinearMap.id_apply, mul_one, he] using! hd.hasDerivAt

end NoiseResponse.IsotropicSpectrum

#print axioms NoiseResponse.IsotropicSpectrum.scalarPrimitive_derivative
