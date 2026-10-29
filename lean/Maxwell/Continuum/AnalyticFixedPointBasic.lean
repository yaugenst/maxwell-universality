import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Parameter-dependent scalar contractions on a genuine closed complex disk.
The fixed point is constructed by the Banach contraction theorem. -/

noncomputable section
namespace Maxwell.Continuum.AnalyticFixedPoint

open Set Metric Filter Function
open scoped Topology NNReal Classical

variable {E : Type*} {F : E → ℂ → ℂ} {U : Set E} {c : ℂ} {r : ℝ} {k : ℝ≥0}

structure Data (F : E → ℂ → ℂ) (U : Set E) (c : ℂ) (r : ℝ) (k : ℝ≥0) : Prop where
  radius_pos : 0 < r
  constant_lt_one : k < 1
  maps : ∀ p ∈ U, MapsTo (F p) (closedBall c r) (closedBall c r)
  lipschitz : ∀ p ∈ U, LipschitzOnWith k (F p) (closedBall c r)

namespace Data

variable (D : Data F U c r k)

def diskMap (p : E) (hp : p ∈ U) : closedBall c r → closedBall c r :=
  fun z => ⟨F p z, D.maps p hp z.property⟩

theorem diskMap_contracting (p : E) (hp : p ∈ U) : ContractingWith k (D.diskMap p hp) :=
  ⟨D.constant_lt_one, fun z w => D.lipschitz p hp z.property w.property⟩

def pointInDisk (p : E) (hp : p ∈ U) : closedBall c r :=
  let _ : Nonempty (closedBall c r) := ⟨⟨c, mem_closedBall_self D.radius_pos.le⟩⟩
  let _ : CompleteSpace (closedBall c r) := isClosed_closedBall.isComplete.completeSpace_coe
  (D.diskMap_contracting p hp).fixedPoint (D.diskMap p hp)

def point (p : E) : ℂ := if hp : p ∈ U then (D.pointInDisk p hp).val else c

theorem point_eq (p : E) (hp : p ∈ U) : D.point p = (D.pointInDisk p hp).val := by
  simp only [point, dite_eq_left hp]

theorem point_mem (p : E) (hp : p ∈ U) : D.point p ∈ closedBall c r := by
  rw [D.point_eq p hp]
  exact (D.pointInDisk p hp).property

theorem point_fixed (p : E) (hp : p ∈ U) : F p (D.point p) = D.point p := by
  rw [D.point_eq p hp]
  let _ : Nonempty (closedBall c r) := ⟨⟨c, mem_closedBall_self D.radius_pos.le⟩⟩
  let _ : CompleteSpace (closedBall c r) := isClosed_closedBall.isComplete.completeSpace_coe
  exact congrArg Subtype.val (D.diskMap_contracting p hp).fixedPoint_isFixedPt

theorem point_unique (p : E) (hp : p ∈ U) {z : ℂ}
    (hz : z ∈ closedBall c r) (hfz : F p z = z) : z = D.point p := by
  have hd : dist z (D.point p) ≤ (k : ℝ) * dist z (D.point p) := by
    simpa only [hfz, D.point_fixed p hp] using
      (D.lipschitz p hp).dist_le_mul z hz (D.point p) (D.point_mem p hp)
  have hk : (k : ℝ) < 1 := D.constant_lt_one
  exact dist_le_zero.mp (by nlinarith [dist_nonneg (x := z) (y := D.point p)])

/-- A posteriori residual bound; no fixed point premise is imposed on `z`. -/
theorem residual_bound (p : E) (hp : p ∈ U) {z : ℂ} (hz : z ∈ closedBall c r) :
    dist z (D.point p) ≤ dist z (F p z) / (1 - (k : ℝ)) := by
  have hk : (k : ℝ) < 1 := D.constant_lt_one
  apply (le_div_iff₀ (sub_pos.mpr hk)).mpr
  have htri := dist_triangle z (F p z) (D.point p)
  have hlip := (D.lipschitz p hp).dist_le_mul z hz (D.point p) (D.point_mem p hp)
  rw [D.point_fixed p hp] at hlip
  nlinarith

def iterate (_D : Data F U c r k) (n : ℕ) (p : E) : ℂ := (F p)^[n] c

theorem iterate_mem (n : ℕ) (p : E) (hp : p ∈ U) : D.iterate n p ∈ closedBall c r := by
  exact (D.maps p hp).iterate n (mem_closedBall_self D.radius_pos.le)

/-- The error is uniformly geometric over the entire parameter set. -/
theorem iterate_error (n : ℕ) (p : E) (hp : p ∈ U) :
    dist (D.iterate n p) (D.point p) ≤ (k : ℝ) ^ n * r := by
  induction n with
  | zero =>
    simpa only [iterate, Function.iterate_zero, id_eq, pow_zero, one_mul, mem_closedBall, dist_comm]
      using D.point_mem p hp
  | succ n ih =>
    have h := (D.lipschitz p hp).dist_le_mul (D.iterate n p) (D.iterate_mem n p hp)
      (D.point p) (D.point_mem p hp)
    rw [D.point_fixed p hp] at h
    calc
      dist (D.iterate (n + 1) p) (D.point p) =
          dist (F p (D.iterate n p)) (D.point p) := by
            simp only [iterate, Function.iterate_succ_apply']
      _ ≤ (k : ℝ) * dist (D.iterate n p) (D.point p) := h
      _ ≤ (k : ℝ) * ((k : ℝ) ^ n * r) := mul_le_mul_of_nonneg_left ih k.coe_nonneg
      _ = (k : ℝ) ^ (n + 1) * r := by rw [pow_succ]; ring

/-- Comparing with any fixed point of a second map only requires the first
map's contraction, and the residual is evaluated at that second root. -/
theorem perturbation_bound {G : E → ℂ → ℂ} (p : E) (hp : p ∈ U)
    {z : ℂ} (hz : z ∈ closedBall c r) (hGz : G p z = z) {δ : ℝ}
    (hFG : dist (F p z) (G p z) ≤ δ) :
    dist (D.point p) z ≤ δ / (1 - (k : ℝ)) := by
  rw [dist_comm]
  refine (D.residual_bound p hp hz).trans ?_
  have hk : (k : ℝ) < 1 := D.constant_lt_one
  apply div_le_div_of_nonneg_right _ (sub_pos.mpr hk).le
  simpa only [hGz, dist_comm] using hFG

#print axioms point_fixed
#print axioms point_unique
#print axioms iterate_error
#print axioms perturbation_bound

end Data
end Maxwell.Continuum.AnalyticFixedPoint
