import Maxwell.Continuum.CalibrationSupercellIndex
import Maxwell.Continuum.CellSpatialTiling

/-! The literal finite family of spatial cells used for supercell
reconstruction contains every well cell at the selected torus size. -/

namespace Maxwell.Continuum.Calibration.Supercell

open FreeFiber CellGauge

variable (M : ℕ) [NeZero M]

theorem centeredOffset_bounds (j : ZMod M) :
    -(M : ℤ)<2*centeredOffset M j ∧ 2*centeredOffset M j≤M := by
  have hM := NeZero.pos M
  have hj := ZMod.val_lt j
  unfold centeredOffset
  split_ifs with h <;> omega

theorem centeredOffset_unique (a : ℤ) (ha : -(M : ℤ)<2*a ∧ 2*a≤M) :
    centeredOffset M (a : ZMod M)=a := by
  have hb := centeredOffset_bounds M (a : ZMod M)
  have hd : (M : ℤ) ∣ centeredOffset M (a : ZMod M)-a := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).mp
    rw [Int.cast_sub,centeredOffset_cast,sub_self]
  obtain ⟨k,hk⟩ := hd
  have hM : (0 : ℤ)<M := by exact_mod_cast NeZero.pos M
  have hk0 : k=0 := by
    rcases lt_trichotomy k 0 with hlt|heq|hgt
    · have hp := mul_le_mul_of_nonneg_left (show k≤-1 by omega) hM.le
      nlinarith
    · exact heq
    · have hp := mul_le_mul_of_nonneg_left (show 1≤k by omega) hM.le
      nlinarith
  rw [hk0,mul_zero] at hk
  omega

def representative (j : Grid M) : Alias := fun i => centeredOffset M (j i)

theorem representative_injective : Function.Injective (representative M) := by
  intro j k h
  funext i
  have hi := congrArg (fun a : Alias => (a i : ZMod M)) h
  simpa only [representative,centeredOffset_cast] using hi

theorem representative_frequency (a : Alias)
    (ha : ∀ i, -(M : ℤ)<2*a i ∧ 2*a i≤M) :
    representative M (PeriodicSampling.Product.frequency M a)=a := by
  funext i
  exact centeredOffset_unique M (a i) (ha i)

theorem frequency_representative (j : Grid M) :
    PeriodicSampling.Product.frequency M (representative M j)=j := by
  funext i
  exact centeredOffset_cast M (j i)

theorem ballCells_representative {L : ℝ} (hL : 1≤L) (hM : 16*(L+1)≤(M : ℝ))
    {a : Alias} (ha : a∈ballCells L) :
    representative M (PeriodicSampling.Product.frequency M a)=a := by
  apply representative_frequency
  intro i
  have hai := Fintype.mem_piFinset.mp ha i
  rw [Finset.mem_Icc] at hai
  have hc := Nat.ceil_lt_add_one (show 0≤L by linarith)
  have hrad : (ballCellRadius L : ℝ)<L+3 := by
    simp only [ballCellRadius,Nat.cast_add,Nat.cast_ofNat]
    linarith
  have hlo : -(ballCellRadius L : ℝ)≤(a i : ℝ) := by exact_mod_cast hai.1
  have hhi : (a i : ℝ)≤(ballCellRadius L : ℝ) := by exact_mod_cast hai.2
  have hlow : -(M : ℝ)<2*(a i : ℝ) := by linarith
  have hhigh : 2*(a i : ℝ)≤(M : ℝ) := by linarith
  exact ⟨by exact_mod_cast hlow,by exact_mod_cast hhigh⟩

#print axioms ballCells_representative

end Maxwell.Continuum.Calibration.Supercell
