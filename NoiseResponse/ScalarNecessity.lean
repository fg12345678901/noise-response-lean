/- Added by cx on 2026-10-29: end-to-end necessity for one orthonormal
   pair of noise coordinates. This is a component of Theorem 3, not its
   full matrix-measure statement. Endpoint limits have separate proofs. -/
module

public import NoiseResponse.RankOnePair
public import NoiseResponse.PowerSeriesIdentification
public import NoiseResponse.GeneratingODE
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic

@[expose] public section

set_option maxRecDepth 1000
set_option maxHeartbeats 2000000
noncomputable section
open Filter Set
open scoped Topology
namespace NoiseResponse.Classification

structure PairCovariances where
  lag00 : ℕ → ℝ
  lag11 : ℕ → ℝ
  lagSym : ℕ → ℝ
  lagSkew : ℕ → ℝ
  zero00 : ℝ
  zero11 : ℝ
  zeroSym : ℝ
  bound : ℝ
  bounded00 : ∀ n, ‖lag00 n‖ ≤ bound
  bounded11 : ∀ n, ‖lag11 n‖ ≤ bound
  boundedSym : ∀ n, ‖lagSym n‖ ≤ bound
  boundedSkew : ∀ n, ‖lagSkew n‖ ≤ bound

namespace PairCovariances
variable (P : PairCovariances)
def sym := generating P.lagSym
def skew := generating P.lagSkew
def k00 := generating P.lag00
def k11 := generating P.lag11
def c00 (a : ℝ) := P.zero00+2*a*P.k00 a
def c11 (a : ℝ) := P.zero11+2*a*P.k11 a

def AllAxisPotentials (η : ℝ) : Prop :=
  ∀ r : ℝ, r ≠ 0 → (1-η*r^2) ∈ Ioo (-1 : ℝ) 1 →
    ∀ p ∈ ({![r,0], ![0,r]} : Set Plane),
      HasLocalPlanePotential
        (pairAlpha0 P.k00 (fun a => P.sym a+P.skew a) P.c00
          (fun a => P.zeroSym+2*a*P.sym a) P.c11 η)
        (pairAlpha1 (fun a => P.sym a-P.skew a) P.k11 P.c00
          (fun a => P.zeroSym+2*a*P.sym a) P.c11 η) p

theorem axis_potentials_odes (η : ℝ) (hη : 0 < η) (hp : P.AllAxisPotentials η)
    (a : ℝ) (ha : a ∈ Ioo (-1 : ℝ) 1) :
    (1-a)*deriv P.skew a-P.skew a = 0 ∧
      (1-a^2)*deriv P.sym a-2*a*P.sym a = P.zeroSym := by
  let r := Real.sqrt ((1-a)/η)
  have hrpos : 0 < r := Real.sqrt_pos.mpr (div_pos (by linarith [ha.2]) hη)
  have hr : r ≠ 0 := ne_of_gt hrpos
  have hrsq : η*r^2 = 1-a := by
    dsimp [r]
    rw [Real.sq_sqrt (le_of_lt (div_pos (by linarith [ha.2]) hη))]
    field_simp
  have har : 1-η*r^2 = a := by linarith
  have hn : ‖a‖ < 1 := by simpa [Real.norm_eq_abs] using abs_lt.mpr ha
  have hs : DifferentiableAt ℝ P.sym a :=
    bounded_generating_differentiable _ _ P.boundedSym _ hn
  have ht : DifferentiableAt ℝ P.skew a :=
    bounded_generating_differentiable _ _ P.boundedSkew _ hn
  have h00 : DifferentiableAt ℝ P.k00 a :=
    bounded_generating_differentiable _ _ P.bounded00 _ hn
  have h11 : DifferentiableAt ℝ P.k11 a :=
    bounded_generating_differentiable _ _ P.bounded11 _ hn
  have hc00 : DifferentiableAt ℝ P.c00 a := by unfold c00; fun_prop
  have hc11 : DifferentiableAt ℝ P.c11 a := by unfold c11; fun_prop
  have he := pair_potentials_force_odes P.sym P.skew P.k00 P.k11 P.c00 P.c11
    P.zeroSym η r hr (by rw [har]; linarith [ha.1])
    (by simpa only [har] using hs) (by simpa only [har] using ht)
    (by simpa only [har] using h00) (by simpa only [har] using h11)
    (by simpa only [har] using hc00) (by simpa only [har] using hc11)
    (hp r hr (by simpa only [har] using ha))
  simpa only [har] using he

/-- Exact positive-lag necessity for a fixed coordinate pair. The two
    endpoint limits retain their different signs. No ODE or coefficient
    identification is assumed as a premise of this theorem. -/
theorem necessary_lags (η : ℝ) (hη : 0 < η) (hp : P.AllAxisPotentials η)
    (ap am : ℕ → ℝ)
    (hap : ∀ k, ap k ∈ Ioo (-1 : ℝ) 1) (ham : ∀ k, am k ∈ Ioo (-1 : ℝ) 1)
    (hapt : Tendsto ap atTop (𝓝 1)) (hamt : Tendsto am atTop (𝓝 (-1)))
    (hskew : Tendsto (fun k => (1-ap k)*P.skew (ap k)) atTop (𝓝 0))
    (m0 mpi : ℝ)
    (hplus : Tendsto (fun k => (1-ap k)*P.sym (ap k)) atTop (𝓝 m0))
    (hminus : Tendsto (fun k => (1+am k)*P.sym (am k)) atTop (𝓝 (-mpi))) :
    (∀ n, P.lagSkew n = 0) ∧ P.zeroSym = m0+mpi ∧
      (∀ n, P.lagSym n = m0-(-1 : ℝ)^n*mpi) := by
  have hd (f : ℕ → ℝ) (hb : ∀ n, ‖f n‖ ≤ P.bound)
      (a : ℝ) (ha : a ∈ Ioo (-1 : ℝ) 1) :
      DifferentiableAt ℝ (generating f) a :=
    bounded_generating_differentiable f P.bound hb a
      (by simpa [Real.norm_eq_abs] using abs_lt.mpr ha)
  have hz : ∀ a ∈ Ioo (-1 : ℝ) 1, P.skew a = 0 := by
    apply skew_ode_endpoint_zero P.skew (deriv P.skew)
      (fun a ha => (hd P.lagSkew P.boundedSkew a ha).hasDerivAt)
      (fun a ha => by simpa only [smul_eq_mul] using (P.axis_potentials_odes η hη hp a ha).1)
      ap hap
    simpa only [smul_eq_mul] using hskew
  have hsz : generating P.lagSkew =ᶠ[𝓝 (0 : ℝ)] generating (fun _ => (0 : ℝ)) := by
    filter_upwards [isOpen_Ioo.mem_nhds (by norm_num : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1)] with a ha
    rw [show generating (fun _ => (0 : ℝ)) a = 0 by simp [generating]]
    exact hz a ha
  have hcoeff := bounded_generating_eq_coefficients P.lagSkew (fun _ => (0 : ℝ))
    P.bound 0 P.boundedSkew (by intro n; simp) hsz
  obtain ⟨d, hkd⟩ := symmetric_ode_integrates P.sym (deriv P.sym) P.zeroSym
    (fun a ha => (hd P.lagSym P.boundedSym a ha).hasDerivAt)
    (fun a ha => by simpa only [smul_eq_mul] using (P.axis_potentials_odes η hη hp a ha).2)
  have hconst := endpoint_limits_identify P.sym P.zeroSym d m0 mpi hkd
    ap am hap ham hapt hamt (by simpa only [smul_eq_mul] using hplus)
    (by simpa only [smul_eq_mul] using hminus)
  have hpoles : ∀ a ∈ Ioo (-1 : ℝ) 1,
      generating P.lagSym a = (1-a)⁻¹ • m0-(1+a)⁻¹ • mpi := by
    intro a ha
    have hne : 1-a^2 ≠ 0 := by nlinarith [ha.1, ha.2]
    have hw : (1-a^2)*P.sym a = a*P.zeroSym+d := by
      simpa only [smul_eq_mul] using hkd a ha
    have hfrac : P.sym a = (a*P.zeroSym+d)/(1-a^2) := by
      exact (eq_div_iff hne).mpr (by nlinarith [hw])
    rw [hconst.1, hconst.2] at hfrac
    rw [endpoint_partial_fractions a m0 mpi (by linarith [ha.2]) (by linarith [ha.1])] at hfrac
    simpa only [sym, smul_eq_mul, div_eq_mul_inv, mul_comm] using hfrac
  exact ⟨fun n => congrFun hcoeff n, hconst.1,
    endpoint_poles_identify_coefficients P.lagSym P.bound P.boundedSym m0 mpi hpoles⟩

end PairCovariances
end NoiseResponse.Classification

#print axioms NoiseResponse.Classification.PairCovariances.axis_potentials_odes
#print axioms NoiseResponse.Classification.PairCovariances.necessary_lags
