import Maxwell.Continuum.NaturalSquareRootPower
import Maxwell.Cost.DyadicSqrt

/-! Uniform execution of the literal integer square root. The input is
the stored integer on tape 540; tape 32 holds its exact `Nat.sqrt`.
All scaling, precision discovery, comparisons, and cleanup are charged. -/

namespace Maxwell.Continuum.Calibration.NaturalRoot

open Maxwell.Cost Maxwell.Cost.Structured
open RationalAccumulator (Word Blank)
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

def fullIds : Finset ℕ := ids∪Finset.Icc 30 36∪{40}
def changed : Finset ℕ := powerChanged∪Finset.Icc 30 36∪{40}
def loadPlan : List NatAssign.Instruction :=
  [.copy 540 30,.copy 532 31,.literal 33 1,.literal 34 1,.copy 541 40]
def preparedValues (T : ℕ) (i : ℕ) : ℕ :=
  if 30 ≤ i ∧ i ≤ 36 then DyadicSqrt.bank T (4^T.bits.length) 0 1 i else
    if i=40 then T.bits.length else powerValues T i
def doneValues (T : ℕ) (i : ℕ) : ℕ :=
  if 30 ≤ i ∧ i ≤ 36 then
    DyadicSqrt.bank (T*4^T.bits.length) (4^T.bits.length) (Nat.sqrt T) (2^T.bits.length) i
  else powerValues T i
def code : Code := .seq powerCode (.seq (NatAssign.code loadPlan)
  (.seq DyadicSqrt.loopCode (.call (TapeOps.clear 40))))
def costBound (T : ℕ) : ℕ := powerCost T.bits.length+
  (3000*8^5*(3*T.bits.length+6)^2+
    (DyadicSqrt.loopBudget T (4^T.bits.length) T.bits.length+6*T.bits.length.bits.length+4))

theorem power_width (T : ℕ) (i : ℕ) :
    (powerValues T i).bits.length≤3*T.bits.length+4 := by
  have hp := SelectedParameters.Geometric.power_bits 4 T.bits.length
  change (4^T.bits.length).bits.length≤T.bits.length*3+1 at hp
  have hk := length_width T
  have fourBits : (4:ℕ).bits.length=3 := rfl
  have oneBits : (1:ℕ).bits.length=1 := rfl
  have zeroBits : (0:ℕ).bits.length=0 := rfl
  simp only [powerValues]
  split_ifs <;> omega

theorem loadPlan_valid : ∀ a∈loadPlan, a.Valid fullIds := by
  simp [loadPlan,NatAssign.Instruction.Valid,fullIds,ids]

theorem loadPlan_values (T : ℕ) : NatAssign.values loadPlan (powerValues T)=preparedValues T := by
  ext i
  by_cases core : 30 ≤ i ∧ i ≤ 36
  · obtain ⟨hlo,hhi⟩ := core
    interval_cases i <;>
      simp [loadPlan,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.value,
        NatAssign.Instruction.target,preparedValues,DyadicSqrt.bank,powerValues]
  · by_cases h40 : i=40
    · subst i
      simp [loadPlan,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.value,
        NatAssign.Instruction.target,preparedValues,powerValues]
    · have h30 : i≠30 := by omega
      have h31 : i≠31 := by omega
      have h33 : i≠33 := by omega
      have h34 : i≠34 := by omega
      simp only [loadPlan,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.value,
        NatAssign.Instruction.target,Function.update_of_ne h30,Function.update_of_ne h31,
        Function.update_of_ne h33,Function.update_of_ne h34,Function.update_of_ne h40,
        preparedValues,ite_eq_right core,ite_eq_right h40]

theorem executes (T : ℕ) (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (hs : NatAssign.Bank fullIds (inputValues T) s.val) (hz : NatAssign.Scratch s.val) :
    ∃ cost t, Executes input tape code cost s t ∧ cost≤costBound T ∧
      Word t.val 32 (Nat.sqrt T) ∧ NatAssign.Bank fullIds (doneValues T) t.val ∧
      NatAssign.Scratch t.val ∧ BinaryPrecision.Frame changed s.val t.val := by
  obtain ⟨c0,u,e0,hc0,b0,z0,f0⟩ := power_executes T input tape s
    (fun i hi => hs i ((by decide : ids⊆fullIds) hi)) hz
  have allBank : NatAssign.Bank fullIds (powerValues T) u.val := by
    intro i hi
    by_cases hold : i∈ids
    · exact b0 i hold
    · have lo : i∈Finset.Icc 30 36 ∨ i=40 := by
        simpa only [fullIds,Finset.mem_union,Finset.mem_singleton,hold,false_or] using hi
      have outside : i∉powerChanged := by
        simp only [Finset.mem_Icc] at lo
        simp only [powerChanged,Finset.mem_insert,Finset.mem_singleton]
        omega
      have hv : powerValues T i=inputValues T i := by
        simp only [Finset.mem_Icc] at lo
        simp [powerValues,inputValues,show i≠530 by omega,show i≠531 by omega,
          show i≠532 by omega,show i≠533 by omega,show i≠540 by omega,show i≠541 by omega]
      exact hv ▸ RationalAccumulator.word_of_eq (f0.tapes i outside) (hs i hi)
  have hids : ∀ i∈fullIds, 4 ≤ i := by
    intro i hi
    simp only [fullIds,ids,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.mem_Icc] at hi
    omega
  obtain ⟨c1,v,e1,hc1,b1,z1,f1⟩ := NatAssign.executes fullIds hids loadPlan loadPlan_valid
    (powerValues T) input tape u allBank z0
  have price := NatAssign.price_bound fullIds loadPlan loadPlan_valid (powerValues T)
    (3*T.bits.length+4) (fun i _ => power_width T i)
      (by simp [loadPlan,NatAssign.Instruction.literalWidth])
  have cost1 : c1≤3000*8^5*(3*T.bits.length+6)^2 := by
    simpa only [loadPlan,List.length_cons,List.length_nil,Nat.add_assoc] using hc1.trans price
  rw [loadPlan_values] at b1
  have smallBank : RationalAccumulator.Bank v.val (DyadicSqrt.bank T (4^T.bits.length) 0 1) := by
    intro i hlo hhi
    have hi : i∈fullIds := Finset.mem_union_left {40}
      (Finset.mem_union_right ids (Finset.mem_Icc.mpr ⟨hlo,hhi⟩))
    have hb : Word v.val i (preparedValues T i) := b1 i hi
    simpa only [preparedValues,ite_eq_left (show 30 ≤ i ∧ i ≤ 36 from ⟨hlo,hhi⟩)] using hb
  have scratch : RationalAccumulator.Scratch v.val 0 :=
    ⟨z1 0 (by decide),(RationalAccumulator.zero_word_iff_blank _ _).mpr (z1 1 (by decide)),
      z1 2 (by decide),z1 3 (by decide)⟩
  have count : Word v.val 40 T.bits.length := by
    simpa [preparedValues] using b1 40 (by decide)
  obtain ⟨origin,count⟩ := count
  obtain ⟨c2,w,last,hc2,e2,b2,z2,count2,length2,f2⟩ := DyadicSqrt.loop_executes
    input tape T (4^T.bits.length) T.bits.length origin v smallBank scratch count
  obtain ⟨t,e3,tt,f3⟩ := WordCall.clear 40 input tape last origin w count2
  have keep (i : ℕ) (hi : i≠40) : t.val.tapes i=w.val.tapes i := by simp [tt,hi]
  have cleared : Blank t.val 40 := ⟨origin+last.length,by simp [tt]⟩
  have bank : NatAssign.Bank fullIds (doneValues T) t.val := by
    intro i hi
    by_cases core : 30 ≤ i ∧ i ≤ 36
    · have hb := RationalAccumulator.word_of_eq (keep i (by omega)) (b2 i core.1 core.2)
      simpa only [doneValues,ite_eq_left core,computed_root] using hb
    · by_cases h40 : i=40
      · subst i
        simpa [doneValues,powerValues] using (RationalAccumulator.zero_word_iff_blank _ _).mpr cleared
      · have big : i∈ids := by
          simpa only [fullIds,Finset.mem_union,Finset.mem_Icc,Finset.mem_singleton,core,h40,
            or_false] using hi
        have hlo : 37 ≤ i := by
          simp only [ids,Finset.mem_insert,Finset.mem_singleton] at big
          omega
        have hf := f2.2.2.2.2.2.1 i (Or.inr ⟨hlo,h40⟩)
        simpa only [doneValues,preparedValues,ite_eq_right core,ite_eq_right h40] using
          RationalAccumulator.word_of_eq ((keep i h40).trans hf) (b1 i hi)
  have zero : NatAssign.Scratch t.val := by
    intro i hi
    interval_cases i
    · exact RationalAccumulator.blank_of_eq (keep 0 (by decide)) z2.1
    · exact RationalAccumulator.blank_of_eq (keep 1 (by decide))
        ((RationalAccumulator.zero_word_iff_blank _ _).mp z2.2.1)
    · exact RationalAccumulator.blank_of_eq (keep 2 (by decide)) z2.2.2.1
    · exact RationalAccumulator.blank_of_eq (keep 3 (by decide)) z2.2.2.2
  have frame2 : BinaryPrecision.Frame changed v.val t.val := by
    refine ⟨f3.1.trans f2.1,f3.2.1.trans f2.2.1,f3.2.2.1.trans f2.2.2.1,
      f3.2.2.2.1.trans f2.2.2.2.1,f3.2.2.2.2.1.trans f2.2.2.2.2.1,?_⟩
    intro i hi
    have hi' := hi
    simp only [changed,powerChanged,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,
      Finset.mem_Icc,not_or] at hi'
    exact (keep i hi'.2).trans (f2.2.2.2.2.2.1 i (by omega))
  refine ⟨c0+(c1+(c2+(6*last.length+4))),t,e0.seq (e1.seq (e2.seq e3)),?_,
    by simpa [doneValues,DyadicSqrt.bank] using bank 32 (by decide),bank,zero,
    (f0.mono (by decide)).trans ((f1.mono (by decide)).trans frame2)⟩
  unfold costBound
  omega

#print axioms executes

end Maxwell.Continuum.Calibration.NaturalRoot
