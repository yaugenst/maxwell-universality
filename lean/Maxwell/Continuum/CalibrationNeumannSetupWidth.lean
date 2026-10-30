import Maxwell.Continuum.CalibrationNeumannSetup

/-! Automatic word bounds for the concrete inverse layout. The width
includes the actual array-word length, since indexed reads and arithmetic
really traverse those bits. -/

namespace Maxwell.Continuum.Calibration.NeumannMachine

open Maxwell.Cost Maxwell.Cost.CalibrationMatrix Maxwell.Continuum.RationalDataflow
set_option maxHeartbeats 1800000

def setupWidth (n width heap D N : ℕ) : ℕ :=
  width+heap.bits.length+4*n.bits.length+width.bits.length+D.bits.length+N.bits.length+64

theorem layout_offset_bound (n : ℕ) (i : Fin 12) :
    vectorOffset n (n*n) i≤12*(n+1)^2 := by
  fin_cases i <;> norm_num [vectorOffset] <;> nlinarith

theorem layout_address_bits (n width heap offset : ℕ) (ho : offset≤12*(n+1)^2) :
    (heap+offset*width).bits.length≤heap.bits.length+2*n.bits.length+width.bits.length+10 := by
  have hn := RationalAccumulator.bits_add_le n 1
  norm_num at hn
  have hn' : (n+1).bits.length≤n.bits.length+2 := by omega
  have hs := RationalAccumulator.bits_mul_le (n+1) (n+1)
  have hc := RationalAccumulator.bits_mul_le 12 ((n+1)^2)
  rw [show (12:ℕ).bits.length=4 from by decide] at hc
  have hp := RationalAccumulator.bits_mul_le (12*(n+1)^2) width
  have ha := RationalAccumulator.bits_add_le heap (12*(n+1)^2*width)
  have hmono := Nat.size_le_size (Nat.add_le_add_left (Nat.mul_le_mul_right width ho) heap)
  simp only [←Nat.size_eq_bits_len] at hmono
  rw [←pow_two] at hs
  omega

theorem initialData_sized {n : ℕ} (a : PartArray.Table (tableSize n)) (heap D N : ℕ)
    (hw : 0<addressValue a.width) (hc : a.width=(addressValue a.width).bits) :
    (initialData a heap D hw).Sized (setupWidth n (addressValue a.width) heap D N) := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · change a.width.length≤_
    rw [hc]
    simp only [addressValue_bits]
    unfold setupWidth
    omega
  · change addressValue a.width≤_
    unfold setupWidth
    omega
  · have h := layout_address_bits n (addressValue a.width) heap n (by nlinarith)
    change (heap+n*addressValue a.width).bits.length≤_
    unfold setupWidth
    omega
  · have h := layout_address_bits n (addressValue a.width) heap (tableSize n+n)
      (by unfold tableSize; nlinarith)
    change (heap+(tableSize n+n)*addressValue a.width).bits.length≤_
    unfold setupWidth
    omega
  · intro i
    have h := layout_address_bits n (addressValue a.width) heap (vectorOffset n (n*n) i)
      (layout_offset_bound n i)
    change (heap+vectorOffset n (n*n) i*addressValue a.width).bits.length≤_
    unfold setupWidth
    omega
  · change D.bits.length≤_
    unfold setupWidth
    omega
  · change (1:ℕ).bits.length≤_
    norm_num [setupWidth]

theorem setupWidth_dimension (n width heap D N : ℕ) :
    n*n<2^(setupWidth n width heap D N) ∧ n<2^(setupWidth n width heap D N) := by
  have hmul := RationalAccumulator.bits_mul_le n n
  have hm : (n*n).bits.length≤setupWidth n width heap D N := by unfold setupWidth; omega
  have hn : n.bits.length≤setupWidth n width heap D N := by unfold setupWidth; omega
  exact ⟨Nat.size_le.mp (by simpa only [←Nat.size_eq_bits_len] using hm),
    Nat.size_le.mp (by simpa only [←Nat.size_eq_bits_len] using hn)⟩

theorem setupWidth_count (n width heap D N : ℕ) :
    n.bits.length≤setupWidth n width heap D N ∧ N.bits.length≤setupWidth n width heap D N := by
  unfold setupWidth
  omega

theorem setupWidth_input_bound (n width heap D N B : ℕ)
    (hn : n.bits.length≤B) (hw : width.bits.length≤B) (hh : heap.bits.length≤B)
    (hD : D.bits.length≤B) (hN : N.bits.length≤B) :
    setupWidth n width heap D N≤width+8*B+64 := by
  unfold setupWidth
  omega

#print axioms initialData_sized
#print axioms setupWidth_input_bound

end Maxwell.Continuum.Calibration.NeumannMachine
