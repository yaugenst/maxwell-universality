import Maxwell.Continuum.CutoffAntiderivativeMap
import Maxwell.Continuum.RationalDataflowFixedWidths

/-! Polynomial widths of the actual table-scaling recurrence, including every
intermediate arithmetic value and the last unused power/odd update. -/
namespace Maxwell.Continuum.Calibration.RawCutoff
open RationalDataflow RationalDataflow.PartArray
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384

theorem literal_quarter_width : (Parts.literal (1/4)).Width 3 := by
  apply Parts.literal_width
  have h := RationalWords.width_fraction (z := 1) (d := 4) (B := 3)
    (by decide) (by decide) (by decide)
  simpa only [Int.cast_one,Nat.cast_ofNat] using h

theorem literal_two_width : (Parts.literal 2).Width 2 := by
  unfold Parts.Width Parts.literal
  decide

theorem descendingPower_width (n k : ℕ) : (descendingPower n k).Width (4*n+4*k+1) := by
  induction k with
  | zero =>
    apply (power_width (x := Parts.literal 4) (B := 3) (by
      unfold Parts.Width Parts.literal
      decide) (n-1)).mono
    omega
  | succ k ih =>
    apply (ih.mul literal_quarter_width).mono
    omega

theorem descendingOdd_width (n k : ℕ) : (descendingOdd n k).Width (2*n+3*k+2) := by
  induction k with
  | zero =>
    apply (Parts.literal_width (q := 2*((n-1:ℕ):ℚ)+1) (by
      simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] using
        RationalWords.width_nat (2*(n-1)+1))).mono
    omega
  | succ k ih =>
    apply (ih.sub literal_two_width).mono
    omega

def scaleStateWidth (n W : ℕ) : ℕ := W+16*(n+1)
def scaleWorkingWidth (n W : ℕ) : ℕ := 64*(scaleStateWidth n W+1)

theorem scaleInitial_good (n : ℕ) : Good scaleSlots (scaleInitial n) := by
  intro i hi
  simp only [scaleSlots,Finset.mem_range] at hi
  interval_cases i <;> simp only [scaleInitial,Function.update_self] <;>
    first | exact descendingPower_valid _ _ | exact descendingOdd_valid _ _ | exact Parts.literal_valid _

theorem scaleInitial_width (n W : ℕ) : WidthBank scaleSlots (scaleStateWidth n W) (scaleInitial n) := by
  intro i hi
  simp only [scaleSlots,Finset.mem_range] at hi
  interval_cases i <;> simp only [scaleInitial,Function.update_self]
  · exact (Parts.literal_width RationalWords.width_zero').mono (by unfold scaleStateWidth; omega)
  · exact (Parts.literal_width RationalWords.width_zero').mono (by unfold scaleStateWidth; omega)
  · exact (descendingPower_width n 0).mono (by unfold scaleStateWidth; omega)
  · exact (descendingOdd_width n 0).mono (by unfold scaleStateWidth; omega)
  · exact (Parts.literal_width RationalWords.width_zero').mono (by unfold scaleStateWidth; omega)
  · exact literal_quarter_width.mono (by unfold scaleStateWidth; omega)
  · exact literal_two_width.mono (by unfold scaleStateWidth; omega)

theorem scale_iterate_width {n : ℕ} (a : Table n) (W : ℕ)
    (ha : ∀ i, (a.get i).Width W) (k : ℕ) (hk : k≤n) :
    WidthBank scaleSlots (scaleStateWidth n W) (iterate a 1 antiderivativeScaleControl (scaleInitial n) k) := by
  cases k with
  | zero => exact scaleInitial_width n W
  | succ k =>
    have hkn : k<n := by omega
    have state := scale_iterate_state a k
    have hget : (a.getD (n-1-k)).Width W := by
      simp only [Table.getD,dite_eq_left (show n-1-k<n by omega)]
      exact ha _
    intro i hi
    simp only [scaleSlots,Finset.mem_range] at hi
    change (antiderivativeScaleControl.evaluate
      (Function.update (iterate a 1 antiderivativeScaleControl (scaleInitial n) k) 1
        (a.getD (n-1-k))) i).Width (scaleStateWidth n W)
    rw [antiderivativeScaleControl_state]
    interval_cases i
    all_goals
      simp (disch := decide) only [Function.update_self,Function.update_of_ne]
    all_goals
      try rw [state.1]
      try rw [state.2.1]
      try rw [state.2.2.1]
      try rw [state.2.2.2]
    · exact ((hget.mul (descendingPower_width n k)).mul (descendingOdd_width n k).inverse).mono
        (C := scaleStateWidth n W)
        (by unfold scaleStateWidth; omega)
    · exact hget.mono (by unfold scaleStateWidth; omega)
    · exact ((descendingPower_width n k).mul literal_quarter_width).mono (C := scaleStateWidth n W)
        (by unfold scaleStateWidth; omega)
    · exact ((descendingOdd_width n k).sub literal_two_width).mono (C := scaleStateWidth n W)
        (by unfold scaleStateWidth; omega)
    · exact (descendingOdd_width n k).inverse.mono (C := scaleStateWidth n W) (by unfold scaleStateWidth; omega)
    · exact literal_quarter_width.mono (C := scaleStateWidth n W) (by unfold scaleStateWidth; omega)
    · exact literal_two_width.mono (C := scaleStateWidth n W) (by unfold scaleStateWidth; omega)

theorem scale_loaded_width {n : ℕ} (a : Table n) (W : ℕ)
    (ha : ∀ i, (a.get i).Width W) (k : ℕ) (hk : k<n) :
    WidthBank scaleSlots (scaleStateWidth n W)
      (loaded a 1 antiderivativeScaleControl (scaleInitial n) k) := by
  apply (scale_iterate_width a W ha k hk.le).update
  simp only [Table.getD,dite_eq_left (show n-1-k<n by omega)]
  exact (ha _).mono (by unfold scaleStateWidth; omega)

theorem scale_loaded_admissible {n : ℕ} (a : Table n) (k : ℕ) (hk : k<n) :
    antiderivativeScaleControl.AdmissibleTrace
      (loaded a 1 antiderivativeScaleControl (scaleInitial n) k) := by
  have state := scale_iterate_state a k
  have hne : (descendingOdd n k).value≠0 := by
    rw [descendingOdd_value_index n k hk]
    positivity
  have general (v : ℕ→Parts) : antiderivativeScaleControl.AdmissibleTrace v ↔ (v 3).value≠0 := by
    simp only [antiderivativeScaleControl,Control.AdmissibleTrace,Instruction.Admissible,and_true]
  rw [general]
  simpa only [loaded,Function.update_of_ne (by decide : (3:ℕ)≠1),state.2.1] using hne

theorem scale_iterate_good {n : ℕ} (a : Table n) (ha : ∀ i, (a.get i).Valid)
    (k : ℕ) (hk : k≤n) : Good scaleSlots (iterate a 1 antiderivativeScaleControl (scaleInitial n) k) := by
  induction k with
  | zero => exact scaleInitial_good n
  | succ k ih =>
    apply Control.evaluate_good scaleSlots _ antiderivativeScaleControl_valid
      (loaded a 1 antiderivativeScaleControl (scaleInitial n) k) _ (scale_loaded_admissible a k (by omega))
    intro i hi
    by_cases he : i=1
    · subst i
      simp only [loaded,Function.update_self,Table.getD,dite_eq_left (show n-1-k<n by omega)]
      exact ha _
    · simpa only [loaded,Function.update_of_ne he] using ih (by omega) i hi

theorem scale_loaded_good {n : ℕ} (a : Table n) (ha : ∀ i, (a.get i).Valid)
    (k : ℕ) (hk : k<n) : Good scaleSlots (loaded a 1 antiderivativeScaleControl (scaleInitial n) k) := by
  intro i hi
  by_cases he : i=1
  · subst i
    simp only [loaded,Function.update_self,Table.getD,dite_eq_left (show n-1-k<n by omega)]
    exact ha _
  · simpa only [loaded,Function.update_of_ne he] using scale_iterate_good a ha k hk.le i hi

theorem scale_loaded_widthTrace {n : ℕ} (a : Table n) (W : ℕ)
    (ha : ∀ i, (a.get i).Width W) (k : ℕ) (hk : k<n) :
    antiderivativeScaleControl.WidthTrace scaleSlots (scaleWorkingWidth n W)
      (loaded a 1 antiderivativeScaleControl (scaleInitial n) k) := by
  have h := antiderivativeScaleControl.automatic_widthTrace scaleSlots antiderivativeScaleControl_valid
    _ (scaleStateWidth n W) (scale_loaded_width a W ha k hk)
    (by simp [antiderivativeScaleControl,Control.LiteralsFit,Instruction.LiteralFits])
  apply h.mono
  rw [antiderivativeScaleControl_steps]
  unfold scaleWorkingWidth
  norm_num

#print axioms scale_loaded_widthTrace
#print axioms scale_iterate_good
end Maxwell.Continuum.Calibration.RawCutoff
