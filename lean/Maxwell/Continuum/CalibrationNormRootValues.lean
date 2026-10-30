import Maxwell.Continuum.RationalSquareRootRaw
import Maxwell.Continuum.RationalMagnitudeMachine
import Maxwell.Continuum.CalibrationBufferNormData

/-! Scalar normalization of the actual integer power output. The stored
common denominator is squared before the literal rational root is taken. -/

namespace Maxwell.Continuum.Calibration.PowerMachine.BufferNorm.Root

open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.CalibrationMatrix
open scoped BigOperators
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384

def ids : Finset ℕ := RationalRoot.Raw.ids∪{549}
def changed : Finset ℕ := RationalRoot.Raw.changed∪{549}
def inputValues (p m D base N : ℕ) (i : ℕ) : ℕ :=
  if i=30 then p else if i=31 then m else if i=530 then base else
    if i=531 then 1 else if i=532 then D else if i=533 then 1 else if i=544 then N else 0
def magnitudeValues (p m D base N : ℕ) : ℕ → ℕ :=
  Function.update (inputValues p m D base N) 34 (IntegerNormSquare.magnitude p m)
def preparePlan : List NatAssign.Instruction :=
  [.copy 34 228,.copy 532 229,.multiply 532 229,.copy 532 549,
   .literal 30 0,.literal 31 0,.literal 32 0,.literal 33 0,.literal 34 0,
   .literal 35 0,.literal 36 0,
   .literal 530 0,.literal 531 0,.literal 532 0,.literal 533 0]
def preparedValues (p m D N : ℕ) (i : ℕ) : ℕ :=
  if i=549 then D else RationalRoot.Raw.inputValues (IntegerNormSquare.magnitude p m) (D^2) N i
def normRadicand (p m D N : ℕ) : ℕ :=
  RationalRoot.radicand (IntegerNormSquare.magnitude p m/Nat.gcd (IntegerNormSquare.magnitude p m) (D^2))
    (D^2/Nat.gcd (IntegerNormSquare.magnitude p m) (D^2)) N

theorem ids_ge : ∀ i∈ids, 4 ≤ i := by
  intro i hi
  rcases Finset.mem_union.mp hi with h|h
  · exact RationalRoot.Raw.ids_ge i h
  · have : i=549 := by simpa using h
    omega

theorem preparePlan_valid : ∀ a∈preparePlan, a.Valid ids := by
  simp [preparePlan,NatAssign.Instruction.Valid,ids,RationalRoot.Raw.ids,
    RationalRoot.ids,NaturalRoot.fullIds,NaturalRoot.ids,RationalCanonicalBank.ids]

theorem preparePlan_values (p m D base N : ℕ) :
    NatAssign.values preparePlan (magnitudeValues p m D base N)=preparedValues p m D N := by
  ext i
  by_cases hcore : 30 ≤ i ∧ i ≤ 36
  · obtain ⟨hlo,hhi⟩ := hcore
    interval_cases i <;>
      simp [preparePlan,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.value,
        NatAssign.Instruction.target,magnitudeValues,inputValues,preparedValues,
        RationalRoot.Raw.inputValues,RationalCanonicalBank.inputValues]
  by_cases hpower : 530 ≤ i ∧ i ≤ 533
  · obtain ⟨hlo,hhi⟩ := hpower
    interval_cases i <;>
      simp [preparePlan,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.value,
        NatAssign.Instruction.target,magnitudeValues,inputValues,preparedValues,
        RationalRoot.Raw.inputValues,RationalCanonicalBank.inputValues]
  by_cases h228 : i=228
  · subst i
    simp [preparePlan,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.value,
      NatAssign.Instruction.target,magnitudeValues,inputValues,preparedValues,
      RationalRoot.Raw.inputValues,RationalCanonicalBank.inputValues]
  by_cases h229 : i=229
  · subst i
    simp [preparePlan,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.value,
      NatAssign.Instruction.target,magnitudeValues,inputValues,preparedValues,
      RationalRoot.Raw.inputValues,RationalCanonicalBank.inputValues,pow_two]
  by_cases h549 : i=549
  · subst i
    simp [preparePlan,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.value,
      NatAssign.Instruction.target,magnitudeValues,inputValues,preparedValues]
  have h30 : i≠30 := by omega
  have h31 : i≠31 := by omega
  have h32 : i≠32 := by omega
  have h33 : i≠33 := by omega
  have h34 : i≠34 := by omega
  have h35 : i≠35 := by omega
  have h36 : i≠36 := by omega
  have h530 : i≠530 := by omega
  have h531 : i≠531 := by omega
  have h532 : i≠532 := by omega
  have h533 : i≠533 := by omega
  simp [preparePlan,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.value,
    NatAssign.Instruction.target,magnitudeValues,inputValues,preparedValues,
    RationalRoot.Raw.inputValues,RationalCanonicalBank.inputValues,h30,h31,h32,h33,h34,
    h35,h36,h530,h531,h532,h533,h228,h229,h549]

theorem magnitude_width (p m D base N W : ℕ) (hp : p.bits.length≤W) (hm : m.bits.length≤W)
    (hD : D.bits.length≤W) (hbase : base.bits.length≤W) (hN : N.bits.length≤W) (i : ℕ) :
    (magnitudeValues p m D base N i).bits.length≤W+1 := by
  have hmag := (IntegerNormSquare.magnitude_bits_length_le p m).trans
    (Nat.add_le_add_right (max_le hp hm) 1)
  have hone : (1:ℕ).bits.length=1 := rfl
  have hzero : (0:ℕ).bits.length=0 := rfl
  simp only [magnitudeValues,Function.update_apply,inputValues]
  split_ifs <;> omega

theorem normRadicand_bits (p m D N W : ℕ) (hp : p.bits.length≤W)
    (hm : m.bits.length≤W) (hD : D.bits.length≤W) :
    (normRadicand p m D N).bits.length≤4*W+3*N+5 := by
  have hmag : (IntegerNormSquare.magnitude p m).bits.length≤2*W+2 := by
    have h := (IntegerNormSquare.magnitude_bits_length_le p m).trans
      (Nat.add_le_add_right (max_le hp hm) 1)
    omega
  have hden : (D^2).bits.length≤2*W+2 := by
    have h := RationalAccumulator.bits_mul_le D D
    rw [pow_two]
    omega
  have smaller (a d : ℕ) : (a/d).bits.length≤a.bits.length := by
    rw [Nat.size_eq_bits_len,Nat.size_eq_bits_len]
    exact Nat.size_le_size (Nat.div_le_self a d)
  have h := RationalRoot.radicand_bits
    (IntegerNormSquare.magnitude p m/Nat.gcd (IntegerNormSquare.magnitude p m) (D^2))
    (D^2/Nat.gcd (IntegerNormSquare.magnitude p m) (D^2)) N (2*W+2)
    ((smaller _ _).trans hmag) ((smaller _ _).trans hden)
  change (normRadicand p m D N).bits.length≤2*(2*W+2)+3*N+1 at h
  omega

theorem magnitude_norm {n : ℕ} (b : Buffers n) :
    (IntegerNormSquare.magnitude
      (Pairing.positive (bufferChannels b) (bufferChannels b))
      (Pairing.negative (bufferChannels b) (bufferChannels b)):ℤ)=
        ∑ i, ((bufferChannels b).value i)^2 := by
  rw [IntegerNormSquare.magnitude,Int.natCast_natAbs,norm_value]
  exact abs_of_nonneg (Finset.sum_nonneg (fun i _ => sq_nonneg _))

theorem rational_magnitude_norm {n : ℕ} (b : Buffers n) (D : ℕ) :
    (IntegerNormSquare.magnitude
      (Pairing.positive (bufferChannels b) (bufferChannels b))
      (Pairing.negative (bufferChannels b) (bufferChannels b)):ℚ)/(D^2:ℕ)=
        ∑ i, (((bufferChannels b).value i:ℚ)/D)^2 := by
  have h := congrArg (fun x : ℤ => (x:ℚ)) (magnitude_norm b)
  simp only [Int.cast_natCast,Int.cast_sum,Int.cast_pow] at h
  rw [h]
  simp only [Nat.cast_pow,Finset.sum_div,div_pow]

#print axioms rational_magnitude_norm

end Maxwell.Continuum.Calibration.PowerMachine.BufferNorm.Root
