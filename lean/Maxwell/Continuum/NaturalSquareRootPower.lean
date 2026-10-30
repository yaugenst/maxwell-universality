import Maxwell.Continuum.NaturalSquareRootInteger
import Maxwell.Continuum.ParameterPowerMachine
import Maxwell.Continuum.StoredWordLength
import Maxwell.Continuum.NatAssignOutputWidth

/-! The integer square-root scaling and loop length are computed from
the actual input word. They are not supplied as a precision certificate. -/

namespace Maxwell.Continuum.Calibration.NaturalRoot

open Maxwell.Cost Maxwell.Cost.Structured
open RationalAccumulator (Word Blank)
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384

def ids : Finset ℕ := {530,531,532,533,534,540,541}
def powerChanged : Finset ℕ := {0,1,2,3,530,531,532,533,534,541}
def inputValues (T : ℕ) (i : ℕ) : ℕ := if i=540 then T else 0
def lengthValues (T : ℕ) : ℕ → ℕ := Function.update (inputValues T) 541 T.bits.length
def powerPlan : List NatAssign.Instruction := [.literal 530 4,.literal 531 1,.copy 541 534]
def powerCode : Code := .seq (WordLength.code 540 541)
  (.seq (NatAssign.code powerPlan) Parameters.PowerMachine.code)
def powerValues (T : ℕ) (i : ℕ) : ℕ :=
  if i=530 then 4 else if i=531 then 1 else if i=532 then 4^T.bits.length else
    if i=533 then 1 else if i=540 then T else if i=541 then T.bits.length else 0
def powerCost (k : ℕ) : ℕ := 48*(k+1)^2+1+3000*8^3*(k+6)^2+
  Parameters.PowerMachine.costBound k (k+4)

theorem powerPlan_valid : ∀ a∈powerPlan, a.Valid ids := by
  simp [powerPlan,NatAssign.Instruction.Valid,ids]

theorem length_width (T : ℕ) : T.bits.length.bits.length≤T.bits.length := by
  rw [Nat.size_eq_bits_len]
  exact Nat.size_le.mpr Nat.lt_two_pow_self

theorem power_executes (T : ℕ) (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (hs : NatAssign.Bank ids (inputValues T) s.val) (hz : NatAssign.Scratch s.val) :
    ∃ cost t, Executes input tape powerCode cost s t ∧ cost≤powerCost T.bits.length ∧
      NatAssign.Bank ids (powerValues T) t.val ∧ NatAssign.Scratch t.val ∧
      BinaryPrecision.Frame powerChanged s.val t.val := by
  obtain ⟨c0,u,e0,hc0,b0,z0,f0⟩ := NatAssign.stored_length ids 540 541 (by decide)
    (by decide) (by decide) (by decide) (inputValues T) (by simp [inputValues]) input tape s hs hz
  change NatAssign.Bank ids (lengthValues T) u.val at b0
  have hids : ∀ i∈ids, 4 ≤ i := by
    intro i hi
    simp only [ids,Finset.mem_insert,Finset.mem_singleton] at hi
    omega
  obtain ⟨c1,v,e1,hc1,b1,z1,f1⟩ := NatAssign.executes ids hids powerPlan powerPlan_valid
    (lengthValues T) input tape u b0 z0
  have fourBits : (4:ℕ).bits.length=3 := rfl
  have oneBits : (1:ℕ).bits.length=1 := rfl
  have zeroBits : (0:ℕ).bits.length=0 := rfl
  have w0 : ∀ i∈ids, (lengthValues T i).bits.length≤T.bits.length+4 := by
    intro i _
    have hh := length_width T
    simp only [lengthValues,Function.update_apply,inputValues]
    split_ifs <;> omega
  have price := NatAssign.price_bound ids powerPlan powerPlan_valid (lengthValues T)
    (T.bits.length+4) w0 (by simp [powerPlan,NatAssign.Instruction.literalWidth,fourBits])
  have cost1 : c1≤3000*8^3*(T.bits.length+6)^2 := by
    simpa only [powerPlan,List.length_cons,List.length_nil,Nat.add_assoc] using hc1.trans price
  have values (i : ℕ) : NatAssign.values powerPlan (lengthValues T) i=
      (if i=530 then 4 else if i=531 then 1 else if i=534 then T.bits.length else
        lengthValues T i) := by
    simp [powerPlan,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.value,
      NatAssign.Instruction.target,lengthValues]
    split_ifs <;> simp_all
  have widths : ∀ i∈SelectedParameters.DynamicPower.ids,
      (NatAssign.values powerPlan (lengthValues T) i).bits.length≤T.bits.length+4 := by
    intro i _
    rw [values]
    simp only [lengthValues,Function.update_apply,inputValues]
    have hh := length_width T
    split_ifs <;> omega
  have count : Word v.val 534 T.bits.length := by
    simpa [values] using b1 534 (by decide)
  obtain ⟨c2,t,e2,hc2,b2,blank,f2⟩ := Parameters.PowerMachine.executes
    (NatAssign.values powerPlan (lengthValues T)) T.bits.length (T.bits.length+4)
      (by omega) widths ((length_width T).trans (by omega)) input tape v
      (fun i hi => b1 i ((by decide : SelectedParameters.DynamicPower.ids⊆ids) hi)) z1 count
  have output : NatAssign.Bank ids (powerValues T) t.val := by
    intro i hi
    simp only [ids,Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · simpa [SelectedParameters.DynamicPower.values,powerValues,values] using b2.bank 530 (by decide)
    · simpa [SelectedParameters.DynamicPower.values,powerValues,values] using b2.bank 531 (by decide)
    · simpa [SelectedParameters.DynamicPower.values,powerValues,values] using b2.bank 532 (by decide)
    · simpa [SelectedParameters.DynamicPower.values,powerValues,values] using b2.bank 533 (by decide)
    · simpa [powerValues] using (RationalAccumulator.zero_word_iff_blank _ _).mpr blank
    · have hb := RationalAccumulator.word_of_eq (f2.tapes 540 (by decide)) (b1 540 (by decide))
      rw [values] at hb
      simpa [powerValues,lengthValues,inputValues] using hb
    · have hb := RationalAccumulator.word_of_eq (f2.tapes 541 (by decide)) (b1 541 (by decide))
      rw [values] at hb
      simpa [powerValues,lengthValues,inputValues] using hb
  refine ⟨c0+(c1+c2),t,e0.seq (e1.seq e2),?_,output,b2.scratch,
    (f0.mono (by decide)).trans ((f1.mono (by decide)).trans (f2.mono (by decide)))⟩
  have hc0' : c0≤48*(T.bits.length+1)^2+1 := by simpa [inputValues] using hc0
  unfold powerCost
  omega

theorem powerCost_polynomial (k : ℕ) : powerCost k≤2^32*(k+6)^5 := by
  unfold powerCost Parameters.PowerMachine.costBound Parameters.PowerMachine.bodyCost
    SelectedParameters.DynamicPower.width
  ring_nf
  omega

#print axioms power_executes
#print axioms powerCost_polynomial

end Maxwell.Continuum.Calibration.NaturalRoot
