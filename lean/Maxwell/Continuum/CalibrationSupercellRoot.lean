import Maxwell.Continuum.CalibrationSupercellFourier
import Maxwell.Continuum.CalibrationBumpTail

/-! The periodic compact root is exactly the physical well root throughout
the selected supercell, including the two-unit offset of its boundary. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1000000

namespace Maxwell.Continuum.Calibration.Supercell

open FreeFiber CellGauge CellBandFourier UnitAddTorus MeasureTheory Set PeriodicSampling

variable (M : ℕ) [NeZero M]

theorem cell_coordinate_bounds (a : Grid M) {x : Space}
    (hx : x∈spatialBox (representative M a)) (i : Fin 3) :
    -(M : ℝ)<x i ∧ x i≤(M : ℝ)+2 := by
  have hc := (spatialBox_mem (representative M a) x).mp hx i
  have ha : -(M : ℝ)<2*(centeredOffset M (a i) : ℝ) ∧
      2*(centeredOffset M (a i) : ℝ)≤(M : ℝ) := by
    exact_mod_cast centeredOffset_bounds M (a i)
  change 2*(centeredOffset M (a i) : ℝ)<x i ∧ x i≤2*(centeredOffset M (a i) : ℝ)+2 at hc
  constructor <;> linarith only [ha.1,ha.2,hc.1,hc.2]

omit [NeZero M] in
theorem root_ratio_ge_four {L : ℝ} (hL : 1≤L) (hM : 16*(L+1)≤(M : ℝ)) :
    4≤2*(M : ℝ)/L := by
  apply (le_div_iff₀ (by linarith : 0<L)).mpr
  linarith only [hL,hM]

theorem rootTorus_on_cell {L : ℝ} (hL : 1≤L) (hM : 16*(L+1)≤(M : ℝ))
    (hs : 4≤2*(M : ℝ)/L) (a : Grid M) {x : Space}
    (hx : x∈spatialBox (representative M a)) :
    rootTorus (2*(M : ℝ)/L) hs (torusPoint M x)=(Well.qw (L⁻¹ • x) : ℂ) := by
  have hL0 : 0<L := by linarith only [hL]
  have hM0 : 0<(M : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
  have hb := cell_coordinate_bounds M a hx
  by_cases hc : ∀i : Fin 3, x i≤(M : ℝ)
  · have hr (i : Fin 3) : x i/(2*(M : ℝ))∈Ioc (-(1/2) : ℝ) (1/2) := by
      constructor
      · apply (lt_div_iff₀ (by positivity : 0<2*(M : ℝ))).mpr
        linarith only [(hb i).1]
      · apply (div_le_iff₀ (by positivity : 0<2*(M : ℝ))).mpr
        linarith only [hc i]
    change centeredLift (scaledRoot (2*(M : ℝ)/L))
      (fun i => ((x i/(2*(M : ℝ)) : ℝ) : UnitAddCircle))=_
    rw [centeredLift_real _ _ hr]
    unfold scaledRoot
    congr 2
    apply PiLp.ext
    intro i
    change (2*(M : ℝ)/L)*(x i/(2*(M : ℝ)))=L⁻¹*x i
    field_simp
  · push Not at hc
    obtain ⟨i,hi⟩ := hc
    have hm4 : (4 : ℝ)≤(M : ℝ) := by linarith only [hL,hM]
    have hrlo : -(1/2 : ℝ)<x i/(2*(M : ℝ))-1 := by
      have hd : (1/2 : ℝ)<x i/(2*(M : ℝ)) :=
        (lt_div_iff₀ (by positivity : 0<2*(M : ℝ))).mpr (by linarith only [hi])
      linarith only [hd]
    have hrhi : x i/(2*(M : ℝ))-1≤-(1/4 : ℝ) := by
      have hh : x i≤(3/4 : ℝ)*(2*(M : ℝ)) := by linarith only [(hb i).2,hm4]
      have hd := (div_le_iff₀ (by positivity : 0<2*(M : ℝ))).mpr hh
      linarith only [hd]
    have htor : ((x i/(2*(M : ℝ))-1 : ℝ) : UnitAddCircle)=(torusPoint M x) i := by
      rw [AddCircle.coe_sub,AddCircle.coe_period,sub_zero]
      rfl
    have hnorm : (1/4 : ℝ)≤‖(torusPoint M x) i‖ := by
      rw [← htor,(AddCircle.norm_coe_eq_abs_iff 1 (by norm_num)).mpr (by
        norm_num only [abs_one]
        apply abs_le.mpr
        constructor <;> linarith only [hrlo,hrhi])]
      rw [abs_of_neg (by linarith only [hrhi])]
      linarith only [hrhi]
    have hz : rootTorus (2*(M : ℝ)/L) hs (torusPoint M x)=0 :=
      centeredLift_zero _ (scaledRoot_zero hs) _ ⟨i,hnorm⟩
    rw [hz]
    have hxnorm : 1≤‖L⁻¹ • x‖ := by
      have hcoord : ‖x i‖≤‖x‖ := PiLp.norm_apply_le x i
      rw [Real.norm_eq_abs,abs_of_pos (lt_trans hM0 hi)] at hcoord
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hL0)]
      apply (le_inv_mul_iff₀ hL0).mpr
      linarith only [hcoord,hi,hM,hL]
    rw [(Well.qw_zero_iff _).mpr hxnorm,Complex.ofReal_zero]

#print axioms rootTorus_on_cell

end Maxwell.Continuum.Calibration.Supercell
