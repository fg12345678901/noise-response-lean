/- Added by cx on 2026-10-29: analytic integration of the skew and
   trace-free generating-function ODEs on the entire stable interval. -/
module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Tactic

@[expose] public section

set_option maxRecDepth 1000
set_option maxHeartbeats 1000000
noncomputable section
open Filter Set
open scoped Topology
namespace NoiseResponse.Classification

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Closedness controls a period only up to a constant. The endpoint
    limit, supplied separately by Abel dominated convergence, kills it. -/
theorem skew_ode_endpoint_zero (T T' : ℝ → E)
    (hT : ∀ a ∈ Ioo (-1 : ℝ) 1, HasDerivAt T (T' a) a)
    (hode : ∀ a ∈ Ioo (-1 : ℝ) 1, (1-a) • T' a - T a = 0)
    (a : ℕ → ℝ) (ha : ∀ k, a k ∈ Ioo (-1 : ℝ) 1)
    (hlim : Tendsto (fun k => (1-a k) • T (a k)) atTop (𝓝 0)) :
    ∀ x ∈ Ioo (-1 : ℝ) 1, T x = 0 := by
  let F : ℝ → E := fun x => (1-x) • T x
  have hd : ∀ x ∈ Ioo (-1 : ℝ) 1, HasDerivAt F 0 x := by
    intro x hx
    have h := ((hasDerivAt_const x (1 : ℝ)).fun_sub (hasDerivAt_id x)).fun_smul (hT x hx)
    have he : (1-x) • T' x + (-1 : ℝ) • T x = 0 := by
      simpa only [neg_one_smul, sub_eq_add_neg] using hode x hx
    have h' : HasDerivAt F ((1-x) • T' x + (-1 : ℝ) • T x) x := by
      simpa only [F, Pi.sub_apply, Pi.smul_apply, id_eq, zero_sub] using h
    exact h'.congr_deriv he
  have hc : ∀ x ∈ Ioo (-1 : ℝ) 1, F x = F 0 := by
    intro x hx
    exact isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo (-1 : ℝ) 1).isPreconnected
      (fun y hy => (hd y hy).differentiableAt.differentiableWithinAt)
      (fun y hy => (hd y hy).deriv) hx (by norm_num)
  have hconst : Tendsto (fun _ : ℕ => F 0) atTop (𝓝 0) := by
    exact hlim.congr' (Filter.Eventually.of_forall (fun k => hc (a k) (ha k)))
  have hzero : F 0 = 0 := tendsto_nhds_unique tendsto_const_nhds hconst
  intro x hx
  have hfx : (1-x) • T x = 0 := (hc x hx).trans hzero
  exact (smul_eq_zero.mp hfx).resolve_left (sub_ne_zero.mpr (ne_of_gt hx.2))

/-- The trace-free differential equation integrates to (B5). -/
theorem symmetric_ode_integrates (K K' : ℝ → E) (g : E)
    (hK : ∀ a ∈ Ioo (-1 : ℝ) 1, HasDerivAt K (K' a) a)
    (hode : ∀ a ∈ Ioo (-1 : ℝ) 1,
      (1-a^2) • K' a - (2*a) • K a = g) :
    ∃ d : E, ∀ a ∈ Ioo (-1 : ℝ) 1,
      (1-a^2) • K a = a • g + d := by
  let F : ℝ → E := fun x => (1-x^2) • K x - x • g
  have hd : ∀ x ∈ Ioo (-1 : ℝ) 1, HasDerivAt F 0 x := by
    intro x hx
    have h := (((hasDerivAt_const x (1 : ℝ)).fun_sub
      ((hasDerivAt_id x).fun_pow 2)).fun_smul (hK x hx)).fun_sub
      ((hasDerivAt_id x).smul_const g)
    have h' : HasDerivAt F
        ((1-x^2) • K' x - (2*x) • K x - g) x := by
      simpa only [F, Pi.sub_apply, Pi.smul_apply, Pi.pow_apply, id_eq,
        zero_sub, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one,
        one_smul, zero_add, neg_smul, sub_eq_add_neg] using h
    exact h'.congr_deriv (by rw [hode x hx]; simp)
  refine ⟨F 0, ?_⟩
  intro x hx
  have hc : F x = F 0 :=
    isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo (-1 : ℝ) 1).isPreconnected
      (fun y hy => (hd y hy).differentiableAt.differentiableWithinAt)
      (fun y hy => (hd y hy).deriv) hx (by norm_num)
  change (1-x^2) • K x - x • g = F 0 at hc
  simpa only [add_comm] using (sub_eq_iff_eq_add.mp hc)

/-- Two actual endpoint limits determine both integration constants.
    This result is vector-valued, so it applies entrywise or directly to
    a finite matrix space, including its trace-free subspace. -/
theorem endpoint_limits_identify
    (K : ℝ → E) (g d m0 mpi : E)
    (hK : ∀ a ∈ Ioo (-1 : ℝ) 1, (1-a^2) • K a = a • g + d)
    (ap am : ℕ → ℝ)
    (hap : ∀ k, ap k ∈ Ioo (-1 : ℝ) 1)
    (ham : ∀ k, am k ∈ Ioo (-1 : ℝ) 1)
    (hapt : Tendsto ap atTop (𝓝 1))
    (hamt : Tendsto am atTop (𝓝 (-1)))
    (hp : Tendsto (fun k => (1-ap k) • K (ap k)) atTop (𝓝 m0))
    (hm : Tendsto (fun k => (1+am k) • K (am k)) atTop (𝓝 (-mpi))) :
    g = m0 + mpi ∧ d = m0 - mpi := by
  have hn (a : ℝ) (ha : a ∈ Ioo (-1 : ℝ) 1) : 1-a^2 ≠ 0 := by
    have : 1-a^2 = (1-a)*(1+a) := by ring
    rw [this]
    exact mul_ne_zero (by linarith [ha.2]) (by linarith [ha.1])
  have hk (a : ℝ) (ha : a ∈ Ioo (-1 : ℝ) 1) :
      K a = (1-a^2)⁻¹ • (a • g + d) := by
    rw [← hK a ha, smul_smul, inv_mul_cancel₀ (hn a ha), one_smul]
  have hpf (a : ℝ) (ha : a ∈ Ioo (-1 : ℝ) 1) :
      (1-a) • K a = (1+a)⁻¹ • (a • g + d) := by
    rw [hk a ha, smul_smul]
    congr 1
    have hp' : 1+a ≠ 0 := by linarith [ha.1]
    field_simp [hn a ha, hp']
    <;> ring
  have hmf (a : ℝ) (ha : a ∈ Ioo (-1 : ℝ) 1) :
      (1+a) • K a = (1-a)⁻¹ • (a • g + d) := by
    rw [hk a ha, smul_smul]
    congr 1
    have hm' : 1-a ≠ 0 := by linarith [ha.2]
    field_simp [hn a ha, hm']
    <;> ring
  have hp' : (2 : ℝ)⁻¹ • (g+d) = m0 := by
    have hl := (((tendsto_const_nhds (x := (1 : ℝ))).add hapt).inv₀
      (by norm_num)).smul ((hapt.smul_const g).add (tendsto_const_nhds (x := d)))
    have hl' : Tendsto (fun k => (1-ap k) • K (ap k)) atTop
        (𝓝 ((2 : ℝ)⁻¹ • (g+d))) := by
      simpa only [one_add_one_eq_two, one_smul] using
        hl.congr' (Filter.Eventually.of_forall (fun k => (hpf (ap k) (hap k)).symm))
    exact tendsto_nhds_unique hl' hp
  have hm' : (2 : ℝ)⁻¹ • (-g+d) = -mpi := by
    have hl := (((tendsto_const_nhds (x := (1 : ℝ))).sub hamt).inv₀
      (by norm_num)).smul ((hamt.smul_const g).add (tendsto_const_nhds (x := d)))
    have hl' : Tendsto (fun k => (1+am k) • K (am k)) atTop
        (𝓝 ((2 : ℝ)⁻¹ • (-g+d))) := by
      simpa only [sub_neg_eq_add, one_add_one_eq_two, neg_one_smul] using
        hl.congr' (Filter.Eventually.of_forall (fun k => (hmf (am k) (ham k)).symm))
    exact tendsto_nhds_unique hl' hm
  have hp2 : g+d = (2 : ℝ) • m0 := by
    rw [← hp', smul_smul]; norm_num
  have hm2 : -g+d = (2 : ℝ) • (-mpi) := by
    rw [← hm', smul_smul]; norm_num
  constructor
  · calc
      g = (2 : ℝ)⁻¹ • ((g+d)-(-g+d)) := by module
      _ = (2 : ℝ)⁻¹ • ((2 : ℝ) • m0 - (2 : ℝ) • (-mpi)) := by rw [hp2, hm2]
      _ = m0+mpi := by module
  · calc
      d = (2 : ℝ)⁻¹ • ((g+d)+(-g+d)) := by module
      _ = (2 : ℝ)⁻¹ • ((2 : ℝ) • m0 + (2 : ℝ) • (-mpi)) := by rw [hp2, hm2]
      _ = m0-mpi := by module

end NoiseResponse.Classification

#print axioms NoiseResponse.Classification.skew_ode_endpoint_zero
#print axioms NoiseResponse.Classification.symmetric_ode_integrates
#print axioms NoiseResponse.Classification.endpoint_limits_identify
