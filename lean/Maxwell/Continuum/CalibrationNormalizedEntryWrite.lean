import Maxwell.Continuum.CalibrationNormalizedEntryRead
import Maxwell.Continuum.RationalDataflowArrayOutputCost

/-! The normalized integer channels are written directly to the rational
output table. No rational-workspace layout change is assumed. -/

namespace Maxwell.Continuum.Calibration.PowerMachine.NormalizedEntry

open Maxwell.Cost Maxwell.Cost.Structured
open RationalDataflow RationalDataflow.PartArray
open RationalAccumulator (Word Blank)
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

def writeCode : Code :=
  .seq (BankArray.writeCanonicalCode 210 140 212 215 560)
    (.seq (BankArray.writeCanonicalCode 210 140 213 215 561)
      (BankArray.writeCanonicalCode 210 140 214 215 552))

def storedEntry (v : ℕ → ℕ) : Parts := ⟨v 560,v 561,v 552⟩

theorem bank_write_frame {v : ℕ → ℕ} {s t : BitRAMState}
    (h : NatAssign.Bank ids v s) (f : BankArray.FrameExcept 37 s t) : NatAssign.Bank ids v t := by
  intro i hi
  have high : 10 ≤ i ∧ i≠37 := by
    simp only [ids,Finset.mem_insert,Finset.mem_singleton] at hi
    omega
  exact RationalAccumulator.word_of_eq (f.2.2.2.1 i (Or.inr high.1) high.2) (h i hi)

theorem write_executes {n : ℕ} (a : Table n) (v : ℕ → ℕ) (i : Fin n)
    (hpositive : 0<addressValue a.width) (hfit : (storedEntry v).Width (addressValue a.width))
    (hsep : a.Separated) (input : List Bool) (tape : ℕ → Bool)
    (index : List Bool) (hindex : addressValue index=i.val) (s : Store)
    (hb : NatAssign.Bank ids v s.val) (ha : a.OutputReady s)
    (hi : BankArray.Word s.val 140 index) :
    ∃ cost t, Executes input tape writeCode cost s t ∧
      cost≤BankArray.costCap a.width index a.basePositive
          (FixedWidth.bits (addressValue a.width) (v 560).bits)+
        BankArray.costCap a.width index a.baseNegative
          (FixedWidth.bits (addressValue a.width) (v 561).bits)+
        BankArray.costCap a.width index a.baseDenominator
          (FixedWidth.bits (addressValue a.width) (v 552).bits)+
        300*addressValue a.width+300 ∧
      NatAssign.Bank ids v t.val ∧ (a.set i (storedEntry v)).OutputReady t ∧
      t.val.memory=a.writeMemory i (storedEntry v) s.val.memory ∧
      BankArray.FrameExcept 37 s.val t.val := by
  obtain ⟨c0,u0,hc0,e0,m0,p0,z0,s0,b0,f0⟩ := BankArray.write_canonical
    210 140 212 215 560 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    input tape a.width index a.basePositive a.clock a.positive i (v 560) a.width_pos
    hindex a.clock_length hpositive hfit.1 s ha.scratch ha.seven ha.packing ha.width hi
    ha.basePositive ha.clock (hb 560 (by decide)) ha.positive
  have bank0 := bank_write_frame hb f0
  have meta0 (j : ℕ) (hj : 100 ≤ j) {xs : List Bool} (hx : BankArray.Word s.val j xs) :=
    BankArray.word_of_eq (f0.2.2.2.1 j (Or.inr (by omega)) (by omega)) hx
  have n0 : BitArray.Represents u0.val.memory (addressValue a.baseNegative)
      (addressValue a.width) a.negative := by
    rw [m0]
    exact IncidenceEncoding.represents_write_disjoint ha.negative _ _ i _
      (FixedWidth.bits_length _ _) hsep.1.symm
  have d0 : BitArray.Represents u0.val.memory (addressValue a.baseDenominator)
      (addressValue a.width) a.denominator := by
    rw [m0]
    exact IncidenceEncoding.represents_write_disjoint ha.denominator _ _ i _
      (FixedWidth.bits_length _ _) hsep.2.1.symm
  obtain ⟨c1,u1,hc1,e1,m1,n1,z1,s1,b1,f1⟩ := BankArray.write_canonical
    210 140 213 215 561 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    input tape a.width index a.baseNegative a.clock a.negative i (v 561) a.width_pos
    hindex a.clock_length hpositive hfit.2.1 u0 z0 s0 b0
    (meta0 _ (by decide) ha.width) (meta0 _ (by decide) hi)
    (meta0 _ (by decide) ha.baseNegative) (meta0 _ (by decide) ha.clock) (bank0 561 (by decide)) n0
  have bank1 := bank_write_frame bank0 f1
  have meta1 (j : ℕ) (hj : 100 ≤ j) {xs : List Bool} (hx : BankArray.Word s.val j xs) :=
    BankArray.word_of_eq (f1.2.2.2.1 j (Or.inr (by omega)) (by omega)) (meta0 j hj hx)
  have p1 : BitArray.Represents u1.val.memory (addressValue a.basePositive)
      (addressValue a.width) (a.positive.set i (FixedWidth.bits (addressValue a.width) (v 560).bits)) := by
    rw [m1]
    exact IncidenceEncoding.represents_write_disjoint p0 _ _ i _ (FixedWidth.bits_length _ _) hsep.1
  have d1 : BitArray.Represents u1.val.memory (addressValue a.baseDenominator)
      (addressValue a.width) a.denominator := by
    rw [m1]
    exact IncidenceEncoding.represents_write_disjoint d0 _ _ i _
      (FixedWidth.bits_length _ _) hsep.2.2.symm
  obtain ⟨c2,t,hc2,e2,m2,d2,z2,s2,b2,f2⟩ := BankArray.write_canonical
    210 140 214 215 552 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    input tape a.width index a.baseDenominator a.clock a.denominator i (v 552) a.width_pos
    hindex a.clock_length hpositive hfit.2.2 u1 z1 s1 b1
    (meta1 _ (by decide) ha.width) (meta1 _ (by decide) hi)
    (meta1 _ (by decide) ha.baseDenominator) (meta1 _ (by decide) ha.clock) (bank1 552 (by decide)) d1
  have meta2 (j : ℕ) (hj : 100 ≤ j) {xs : List Bool} (hx : BankArray.Word s.val j xs) :=
    BankArray.word_of_eq (f2.2.2.2.1 j (Or.inr (by omega)) (by omega)) (meta1 j hj hx)
  have p2 : BitArray.Represents t.val.memory (addressValue a.basePositive)
      (addressValue a.width) (a.positive.set i (FixedWidth.bits (addressValue a.width) (v 560).bits)) := by
    rw [m2]
    exact IncidenceEncoding.represents_write_disjoint p1 _ _ i _ (FixedWidth.bits_length _ _) hsep.2.1
  have n2 : BitArray.Represents t.val.memory (addressValue a.baseNegative)
      (addressValue a.width) (a.negative.set i (FixedWidth.bits (addressValue a.width) (v 561).bits)) := by
    rw [m2]
    exact IncidenceEncoding.represents_write_disjoint n1 _ _ i _ (FixedWidth.bits_length _ _) hsep.2.2
  refine ⟨c0+(c1+c2),t,e0.seq (e1.seq e2),by omega,bank_write_frame bank1 f2,
    ⟨z2,s2,b2,meta2 _ (by decide) ha.width,meta2 _ (by decide) ha.basePositive,
      meta2 _ (by decide) ha.baseNegative,meta2 _ (by decide) ha.baseDenominator,
      meta2 _ (by decide) ha.clock,p2,n2,d2⟩,?_,?_⟩
  · rw [m2,m1,m0]
    rfl
  · exact ⟨f2.1.trans (f1.1.trans f0.1),f2.2.1.trans (f1.2.1.trans f0.2.1),
      f2.2.2.1.trans (f1.2.2.1.trans f0.2.2.1),fun j hj h37 =>
        (f2.2.2.2.1 j hj h37).trans ((f1.2.2.2.1 j hj h37).trans (f0.2.2.2.1 j hj h37)),
      fun j hj h24 h25 h26 h27 h28 h29 => (f2.2.2.2.2 j hj h24 h25 h26 h27 h28 h29).trans
        ((f1.2.2.2.2 j hj h24 h25 h26 h27 h28 h29).trans (f0.2.2.2.2 j hj h24 h25 h26 h27 h28 h29))⟩

#print axioms write_executes

end Maxwell.Continuum.Calibration.PowerMachine.NormalizedEntry
