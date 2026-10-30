import Maxwell.Continuum.RationalSquareRootMachine
import Maxwell.Continuum.CalibrationNormFactor
import Maxwell.Continuum.CalibrationSupercellFactor

/-! Runtime preparation of the physical Fourier normalization. Its input
fraction has numerator one, so canonicality is proved before calling the
existing fixed rational square-root program. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime.PhysicalFactorMachine
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow Calibration
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

def ids : Finset ℕ := RationalRoot.ids∪{350,351}
def changed : Finset ℕ := {0,1,2,3}∪ids
def initial (M P i : ℕ) : ℕ := if i=350 then M else if i=351 then P else 0
def setup : List NatAssign.Instruction :=
  [.literal 542 1,.literal 543 8,.multiply 350 543,.multiply 350 543,.multiply 350 543,.copy 351 544]
def setupCode : Code := NatAssign.code setup
def denominator (M : ℕ) : ℕ := 8*M^3
def rootArgument (M P : ℕ) : ℕ := RationalRoot.radicand 1 (denominator M) P
def outputValues (M P i : ℕ) : ℕ :=
  if i=350 then M else if i=351 then P else
    if i∈NaturalRoot.fullIds then NaturalRoot.doneValues (rootArgument M P) i else
      RationalRoot.preparedValues 1 (denominator M) P i

theorem ids_ge (i : ℕ) (hi : i∈ids) : 4 ≤ i := by
  rcases Finset.mem_union.mp hi with hi|hi
  · exact RationalRoot.ids_ge i hi
  · simp only [Finset.mem_insert,Finset.mem_singleton] at hi;omega

theorem setup_valid : ∀a∈setup,a.Valid ids := by
  simp [setup,NatAssign.Instruction.Valid,ids,RationalRoot.ids]

theorem setup_values (M P : ℕ) (i : ℕ) :
    NatAssign.values setup (initial M P) i=
      if i=350 then M else if i=351 then P else RationalRoot.inputValues 1 (denominator M) P i := by
  by_cases h350 : i=350
  · subst i
    simp [setup,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,
      NatAssign.Instruction.value,initial]
  by_cases h351 : i=351
  · subst i
    simp [setup,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,
      NatAssign.Instruction.value,initial]
  by_cases h542 : i=542
  · subst i
    simp [setup,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,
      NatAssign.Instruction.value,initial,RationalRoot.inputValues]
  by_cases h543 : i=543
  · subst i
    simp [setup,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,
      NatAssign.Instruction.value,initial,RationalRoot.inputValues,denominator]
    ring
  by_cases h544 : i=544
  · subst i
    simp [setup,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,
      NatAssign.Instruction.value,initial,RationalRoot.inputValues]
  simp [setup,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,
    NatAssign.Instruction.value,initial,RationalRoot.inputValues,h350,h351,h542,h543,h544]

theorem setup_root_values (M P : ℕ) (i : ℕ) (hi : i∈RationalRoot.ids) :
    NatAssign.values setup (initial M P) i=RationalRoot.inputValues 1 (denominator M) P i := by
  have h350 : i≠350 := fun h => (by decide : 350∉RationalRoot.ids) (h ▸ hi)
  have h351 : i≠351 := fun h => (by decide : 351∉RationalRoot.ids) (h ▸ hi)
  simp only [setup_values,h350,h351,ite_false]

theorem denominator_width (M W : ℕ) (hM : M.bits.length≤W) : (denominator M).bits.length≤3*W+4 := by
  have h1 := RationalAccumulator.bits_mul_le 8 M
  have h2 := RationalAccumulator.bits_mul_le (8*M) M
  have h3 := RationalAccumulator.bits_mul_le (8*M*M) M
  have he : denominator M=8*M*M*M := by unfold denominator;ring
  rw [he]
  rw [show (8:ℕ).bits.length=4 by decide] at h1
  omega

theorem denominator_pos (M : ℕ) (hM : 0<M) : 0<denominator M := by unfold denominator;positivity

theorem factor_value (M P : ℕ) (hM : 0<M) :
    (Nat.sqrt (rootArgument M P):ℚ)/(denominator M*2^P)=Supercell.physicalFactorApprox M P := by
  let b := denominator M
  have hb : 0<b := denominator_pos M hM
  have num := RationalCanonical.value_num_natAbs false 1 b hb
  have den := RationalCanonical.value_den false 1 b hb
  simp only [RationalCanonical.value,Bool.false_eq_true,ite_false,Nat.cast_one,
    Nat.gcd_one_left,Nat.div_one] at num den
  have literal := RationalRoot.literal_value ((1:ℚ)/b) P
  rw [num,den] at literal
  change (Nat.sqrt (RationalRoot.radicand 1 b P):ℚ)/(b*2^P)=_ at literal
  change (Nat.sqrt (RationalRoot.radicand 1 b P):ℚ)/(b*2^P)=_
  rw [literal]
  simp only [Supercell.physicalFactorApprox,Supercell.physicalFactorSquare,b,denominator,
    Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,one_div]

theorem output_width (M P W i : ℕ) (hM : M.bits.length≤W) (hP : P.bits.length≤W) :
    (outputValues M P i).bits.length≤32*W+16*P+64 := by
  have hd := denominator_width M W hM
  have hrad := RationalRoot.radicand_bits 1 (denominator M) P (3*W+4)
    (by change 1≤3*W+4;omega) hd
  have hdone := PowerMachine.BufferNorm.Factor.done_width (rootArgument M P) i
  have hp := SelectedParameters.Geometric.power_bits 2 P
  change (2^P).bits.length≤P*2+1 at hp
  have hprod := RationalAccumulator.bits_mul_le (denominator M) (2^P)
  have hone : (1:ℕ).bits.length=1 := rfl
  have hzero : (0:ℕ).bits.length=0 := rfl
  change (rootArgument M P).bits.length≤2*(3*W+4)+3*P+1 at hrad
  dsimp only [rootArgument] at hrad hdone
  unfold outputValues rootArgument RationalRoot.preparedValues RationalRoot.inputValues
  split_ifs <;> omega

#print axioms factor_value
#print axioms output_width
end Maxwell.Continuum.Profile.WaveMachine.Runtime.PhysicalFactorMachine
