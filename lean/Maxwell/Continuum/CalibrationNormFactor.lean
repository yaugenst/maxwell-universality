import Maxwell.Continuum.CalibrationNormRootMachine
import Maxwell.Continuum.RationalDataflowParts

/-! Charged handoff of the computed norm to one shared coefficient scale.
The integer square-root workspace is cleared before indexed output writes. -/

namespace Maxwell.Continuum.Calibration.PowerMachine.BufferNorm.Factor

open Maxwell.Cost Maxwell.Cost.Structured
open RationalAccumulator (Word Blank)
open RationalDataflow
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

def ids : Finset ℕ := NaturalRoot.fullIds∪{548,549,550,551,552}
def changed : Finset ℕ := {0,1,2,3,550,551,552}∪Finset.Icc 30 36
def inputValues (T d D : ℕ) (i : ℕ) : ℕ :=
  if i=548 then d else if i=549 then D else NaturalRoot.doneValues T i
def outputValues (T d D : ℕ) (i : ℕ) : ℕ :=
  if i=550 then Nat.sqrt T else if i=551 then d else if i=552 then D*Nat.sqrt T else
    if 30 ≤ i ∧ i ≤ 36 then 0 else inputValues T d D i
def plan : List NatAssign.Instruction :=
  [.copy 32 550,.copy 548 551,.copy 549 552,.multiply 550 552,
   .literal 30 0,.literal 31 0,.literal 32 0,.literal 33 0,
   .literal 34 0,.literal 35 0,.literal 36 0]
def code : Code := NatAssign.code plan
def factor (T d D : ℕ) : Parts := ⟨d,0,D*Nat.sqrt T⟩
def costBound (T d D : ℕ) : ℕ := 2^52*(4*T.bits.length+d.bits.length+D.bits.length+6)^2

theorem ids_ge : ∀ i∈ids, 4 ≤ i := by
  intro i hi
  simp only [ids,NaturalRoot.fullIds,NaturalRoot.ids,Finset.mem_union,Finset.mem_insert,
    Finset.mem_singleton,Finset.mem_Icc] at hi
  omega

theorem plan_valid : ∀ a∈plan, a.Valid ids := by
  simp [plan,NatAssign.Instruction.Valid,ids,NaturalRoot.fullIds,NaturalRoot.ids]

theorem done_width (T i : ℕ) : (NaturalRoot.doneValues T i).bits.length≤4*T.bits.length+4 := by
  have h4 := SelectedParameters.Geometric.power_bits 4 T.bits.length
  change (4^T.bits.length).bits.length≤T.bits.length*3+1 at h4
  have h2 := SelectedParameters.Geometric.power_bits 2 T.bits.length
  change (2^T.bits.length).bits.length≤T.bits.length*2+1 at h2
  have hm := RationalAccumulator.bits_mul_le T (4^T.bits.length)
  have hs : (Nat.sqrt T).bits.length≤T.bits.length := by
    rw [Nat.size_eq_bits_len,Nat.size_eq_bits_len]
    exact Nat.size_le_size (Nat.sqrt_le_self T)
  have hk := NaturalRoot.length_width T
  have hfour : (4:ℕ).bits.length=3 := rfl
  have hone : (1:ℕ).bits.length=1 := rfl
  have hzero : (0:ℕ).bits.length=0 := rfl
  simp only [NaturalRoot.doneValues,DyadicSqrt.bank,NaturalRoot.powerValues]
  split_ifs <;> omega

theorem plan_values (T d D : ℕ) :
    NatAssign.values plan (inputValues T d D)=outputValues T d D := by
  ext i
  by_cases hc : 30 ≤ i ∧ i ≤ 36
  · obtain ⟨hlo,hhi⟩ := hc
    interval_cases i <;> simp [plan,NatAssign.values,NatAssign.Instruction.update,
      NatAssign.Instruction.value,NatAssign.Instruction.target,outputValues]
  by_cases h550 : i=550
  · subst i
    simp [plan,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.value,
      NatAssign.Instruction.target,inputValues,outputValues,NaturalRoot.doneValues,DyadicSqrt.bank]
  by_cases h551 : i=551
  · subst i
    simp [plan,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.value,
      NatAssign.Instruction.target,inputValues,outputValues]
  by_cases h552 : i=552
  · subst i
    simp [plan,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.value,
      NatAssign.Instruction.target,inputValues,outputValues,NaturalRoot.doneValues,DyadicSqrt.bank,Nat.mul_comm]
  have h30 : i≠30 := by omega
  have h31 : i≠31 := by omega
  have h32 : i≠32 := by omega
  have h33 : i≠33 := by omega
  have h34 : i≠34 := by omega
  have h35 : i≠35 := by omega
  have h36 : i≠36 := by omega
  simp [plan,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.value,
    NatAssign.Instruction.target,outputValues,hc,h550,h551,h552,h30,h31,h32,h33,h34,h35,h36]

theorem executes (T d D : ℕ) (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (hs : NatAssign.Bank ids (inputValues T d D) s.val) (hz : NatAssign.Scratch s.val) :
    ∃ cost t, Executes input tape code cost s t ∧ cost≤costBound T d D ∧
      NatAssign.Bank ids (outputValues T d D) t.val ∧ NatAssign.Scratch t.val ∧
      BinaryPrecision.Frame changed s.val t.val := by
  obtain ⟨cost,t,run,hcost,bank,scratch,frame⟩ := NatAssign.executes ids ids_ge plan plan_valid
    (inputValues T d D) input tape s hs hz
  have widths : ∀ i∈ids, (inputValues T d D i).bits.length≤
      4*T.bits.length+d.bits.length+D.bits.length+4 := by
    intro i _
    have h := done_width T i
    simp only [inputValues]
    split_ifs <;> omega
  have hp := NatAssign.price_bound ids plan plan_valid (inputValues T d D)
    (4*T.bits.length+d.bits.length+D.bits.length+4) widths
    (by simp [plan,NatAssign.Instruction.literalWidth])
  refine ⟨cost,t,run,?_,by simpa only [plan_values] using bank,scratch,frame.mono (by decide)⟩
  have hsmall : cost≤3000*8^11*(4*T.bits.length+d.bits.length+D.bits.length+6)^2 := by
    simpa only [plan,List.length_cons,List.length_nil,Nat.add_assoc] using hcost.trans hp
  exact hsmall.trans (Nat.mul_le_mul_right _ (by norm_num : 3000*8^11≤2^52))

theorem factor_value (T d D : ℕ) :
    (factor T d D).value=((Nat.sqrt T:ℚ)/d)⁻¹/(D:ℚ) := by
  simp only [factor,Parts.value,Nat.cast_zero,sub_zero,Nat.cast_mul,inv_div,div_div]
  congr 1
  ring

theorem factor_valid (T d D : ℕ) (hD : 0<D) (hT : 0<Nat.sqrt T) : (factor T d D).Valid :=
  Nat.mul_pos hD hT

#print axioms executes
#print axioms factor_value

end Maxwell.Continuum.Calibration.PowerMachine.BufferNorm.Factor
