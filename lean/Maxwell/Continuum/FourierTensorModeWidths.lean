import Maxwell.Continuum.FourierTensorModeRows
import Maxwell.Continuum.RoundedIntegerMagnitude

/-! Small stored tensor-input words follow from the normalized mode's
actual norm bound. Large raw calibration denominators do not propagate
into the canonical amplitude words. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime.RowArithmetic
open Maxwell.Cost RationalDataflow RationalDataflow.PartArray Calibration
open FreeFiber
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency true

theorem field_coordinate_abs (v : FourierData) (hv : ‖v.value‖≤2) (ν : Alias) (j : Fin 3) :
    |(v.field ν j).1|≤2 ∧ |(v.field ν j).2|≤2 := by
  have hn : ‖v.value ν j‖≤2 :=
    ((PiLp.norm_apply_le (v.value ν) j).trans (lp.norm_apply_le_norm (by norm_num) v.value ν)).trans hv
  rw [←v.represents ν j,rationalComplexValue_eq] at hn
  have hr := (Complex.abs_re_le_norm (((v.field ν j).1:ℂ)+((v.field ν j).2:ℂ)*Complex.I)).trans hn
  have hi := (Complex.abs_im_le_norm (((v.field ν j).1:ℂ)+((v.field ν j).2:ℂ)*Complex.I)).trans hn
  norm_num only [Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,
    Complex.ratCast_re,Complex.ratCast_im,Complex.I_re,Complex.I_im,
    mul_zero,mul_one,sub_zero,zero_add,add_zero] at hr hi
  exact ⟨by exact_mod_cast hr,by exact_mod_cast hi⟩

theorem loaded_amplitude_abs (M P R : ℕ) [NeZero M] (a : Table (2*aliasArraySize R))
    (j : Fin 3) (r : Fin (rowCount R)) (v : ℕ→Parts)
    (hnorm : (v 0).value=Supercell.physicalFactorApprox M P)
    (hmode : ‖(GlobalPower.tableData R a).value‖≤2) :
    |((loaded R a j r v 0).mul (loaded R a j r v 2)).value|≤4 ∧
    |((loaded R a j r v 0).mul (loaded R a j r v 3)).value|≤4 := by
  have hc := field_coordinate_abs (GlobalPower.tableData R a) hmode (rowAlias R r) j
  rw [table_coordinate] at hc
  have hp : |Supercell.physicalFactorApprox M P|≤(2:ℚ) := by
    exact_mod_cast Supercell.physicalFactorApprox_abs_le_two M P
  have h0 : loaded R a j r v 0=v 0 := by simp [loaded]
  have h2 : loaded R a j r v 2=a.get (GlobalPower.realIndex R (0,rowIndex R j r)) := by simp [loaded]
  have h3 : loaded R a j r v 3=a.get (GlobalPower.realIndex R (1,rowIndex R j r)) := by simp [loaded]
  rw [Parts.mul_value,Parts.mul_value,h0,h2,h3,hnorm,abs_mul,abs_mul]
  exact ⟨by nlinarith only [mul_le_mul hp hc.1 (abs_nonneg _) (by norm_num : (0:ℚ)≤2)],
    by nlinarith only [mul_le_mul hp hc.2 (abs_nonneg _) (by norm_num : (0:ℚ)≤2)]⟩

theorem output_amplitude_width (M P B R : ℕ) [NeZero M] (a : Table (2*aliasArraySize R))
    (j : Fin 3) (r : Fin (rowCount R)) (v : ℕ→Parts)
    (hnorm : (v 0).value=Supercell.physicalFactorApprox M P)
    (hmode : ‖(GlobalPower.tableData R a).value‖≤2) :
    (output B (loaded R a j r v) 9).Width (B+6) ∧
    (output B (loaded R a j r v) 10).Width (B+6) := by
  have hc := loaded_amplitude_abs M P R a j r v hnorm hmode
  have h9 : output B (loaded R a j r v) 9=
      RoundedInteger.result B ((loaded R a j r v 0).mul (loaded R a j r v 2)) := by simp [output]
  have h10 : output B (loaded R a j r v) 10=
      RoundedInteger.result B ((loaded R a j r v 0).mul (loaded R a j r v 3)) := by simp [output]
  rw [h9,h10]
  constructor
  · simpa only [Nat.add_assoc,Nat.reduceAdd] using
      (RoundedInteger.result_magnitude_width B 2 _ (by norm_num;exact hc.1))
  · simpa only [Nat.add_assoc,Nat.reduceAdd] using
      (RoundedInteger.result_magnitude_width B 2 _ (by norm_num;exact hc.2))

theorem output_frequency_width (P R W : ℕ) (a : Table (2*aliasArraySize R)) (j : Fin 3)
    (r : Fin (rowCount R)) (v : ℕ→Parts) (hscale : (v 1).Width W) (k : Fin 3) :
    (output P (loaded R a j r v) (4+k.val)).Width (W+R.bits.length+3) := by
  rw [output_frequency,loaded_coordinate]
  have hs : loaded R a j r v 1=v 1 := by simp [loaded]
  rw [hs]
  have h := hscale.mul (RawFree.coordinatePart_width R (rowIndex R j r) k)
  simpa only [Nat.add_assoc] using h

#print axioms output_amplitude_width
#print axioms output_frequency_width
end Maxwell.Continuum.Profile.WaveMachine.Runtime.RowArithmetic
