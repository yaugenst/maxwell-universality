import Maxwell.Continuum.RationalDataflowArrayOutput

/-! Stored rational writes with a separate index word. This permits cached
row updates while the runtime outer countdown remains unchanged. -/
namespace Maxwell.Continuum.RationalDataflow.PartArray
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

def writeAtCode (indexBank entry : ℕ) : Code :=
  .seq (BankArray.writeCanonicalCode 210 indexBank 212 215 (positivePort entry))
    (.seq (BankArray.writeCanonicalCode 210 indexBank 213 215 (negativePort entry))
      (BankArray.writeCanonicalCode 210 indexBank 214 215 (denominatorPort entry)))

theorem rationalReady_write_frame {S : Finset ℕ} {v : ℕ→Parts} {s t : Store}
    (h : RationalDataflow.Ready S v s) (hf : BankArray.FrameExcept 37 s.val t.val)
    (hz : BankArray.Scratch t.val) : RationalDataflow.Ready S v t := by
  constructor
  · intro i hi
    have hne : i≠37 := by
      intro he
      subst i
      exact bankIds_ne_packing S (Finset.mem_union_left _ hi)
    exact RationalAccumulator.word_of_eq
      (hf.2.2.2.1 i (Or.inr (ids_ge_ten S i hi)) hne) (h.1 i hi)
  · intro i hi
    interval_cases i
    · exact hz.1
    · exact hz.2.1
    · exact hz.2.2.1
    · exact hz.2.2.2.1

theorem writeAt_executes {n : ℕ} (a : Table n) (S : Finset ℕ) (indexBank : ℕ) (hiB : 100 ≤ indexBank) (entry : ℕ) (he : entry∈S)
    (v : ℕ→Parts) (i : Fin n) (hpositive : 0<addressValue a.width)
    (hfit : (v entry).Width (addressValue a.width)) (hsep : a.Separated)
    (input : List Bool) (tape : ℕ→Bool) (index : List Bool) (hindex : addressValue index=i.val)
    (s : Store) (hs : RationalDataflow.Ready S v s) (ha : a.OutputReady s)
    (hi : BankArray.Word s.val indexBank index) :
    ∃ cost t, Executes input tape (writeAtCode indexBank entry) cost s t ∧
      cost≤BankArray.costCap a.width index a.basePositive
          (FixedWidth.bits (addressValue a.width) (v entry).positive.bits)+
        BankArray.costCap a.width index a.baseNegative
          (FixedWidth.bits (addressValue a.width) (v entry).negative.bits)+
        BankArray.costCap a.width index a.baseDenominator
          (FixedWidth.bits (addressValue a.width) (v entry).denominator.bits)+
        300*addressValue a.width+300 ∧
      RationalDataflow.Ready S v t ∧ (a.set i (v entry)).OutputReady t ∧
      t.val.memory=a.writeMemory i (v entry) s.val.memory ∧ BankArray.FrameExcept 37 s.val t.val := by
  have bank (j : ℕ) (hj : j∈ids S) := hs.1 j hj
  have hp : RationalAccumulator.Word s.val (positivePort entry) (v entry).positive :=
    by simpa only [dataValues_positive] using bank (positivePort entry) (cell_mem he (by simp [cellPorts]))
  obtain ⟨c1,t1,h1,e1,m1,p1,z1,s1,b1,f1⟩ := BankArray.write_canonical
    210 indexBank 212 215 (positivePort entry) (by decide) (by omega) (by decide) (by decide)
    (by have := positivePort_ge entry; omega) (by decide) (by omega) (by decide)
    input tape a.width index a.basePositive a.clock a.positive i (v entry).positive a.width_pos
    hindex a.clock_length hpositive hfit.1 s ha.scratch ha.seven ha.packing ha.width hi
    ha.basePositive ha.clock hp ha.positive
  have ready1 := rationalReady_write_frame hs f1 z1
  have meta1 (j : ℕ) (hj : 100 ≤ j) {xs : List Bool} (hx : BankArray.Word s.val j xs) :=
    BankArray.word_of_eq (f1.2.2.2.1 j (Or.inr (by omega)) (by omega)) hx
  have n1 : BitArray.Represents t1.val.memory (addressValue a.baseNegative) (addressValue a.width) a.negative := by
    rw [m1]
    exact IncidenceEncoding.represents_write_disjoint ha.negative _ _ i _ (FixedWidth.bits_length _ _) hsep.1.symm
  have d1 : BitArray.Represents t1.val.memory (addressValue a.baseDenominator) (addressValue a.width) a.denominator := by
    rw [m1]
    exact IncidenceEncoding.represents_write_disjoint ha.denominator _ _ i _ (FixedWidth.bits_length _ _) hsep.2.1.symm
  have hn : RationalAccumulator.Word t1.val (negativePort entry) (v entry).negative :=
    by simpa only [dataValues_negative] using ready1.1 (negativePort entry) (cell_mem he (by simp [cellPorts]))
  obtain ⟨c2,t2,h2,e2,m2,n2,z2,s2,b2,f2⟩ := BankArray.write_canonical
    210 indexBank 213 215 (negativePort entry) (by decide) (by omega) (by decide) (by decide)
    (by have := negativePort_ge entry; omega) (by decide) (by omega) (by decide)
    input tape a.width index a.baseNegative a.clock a.negative i (v entry).negative a.width_pos
    hindex a.clock_length hpositive hfit.2.1 t1 z1 s1 b1 (meta1 _ (by decide) ha.width)
    (meta1 _ hiB hi) (meta1 _ (by decide) ha.baseNegative) (meta1 _ (by decide) ha.clock) hn n1
  have ready2 := rationalReady_write_frame ready1 f2 z2
  have meta2 (j : ℕ) (hj : 100 ≤ j) {xs : List Bool} (hx : BankArray.Word s.val j xs) :=
    BankArray.word_of_eq (f2.2.2.2.1 j (Or.inr (by omega)) (by omega)) (meta1 j hj hx)
  have p2 : BitArray.Represents t2.val.memory (addressValue a.basePositive) (addressValue a.width)
      (a.positive.set i (FixedWidth.bits (addressValue a.width) (v entry).positive.bits)) := by
    rw [m2]
    exact IncidenceEncoding.represents_write_disjoint p1 _ _ i _ (FixedWidth.bits_length _ _) hsep.1
  have d2 : BitArray.Represents t2.val.memory (addressValue a.baseDenominator) (addressValue a.width) a.denominator := by
    rw [m2]
    exact IncidenceEncoding.represents_write_disjoint d1 _ _ i _ (FixedWidth.bits_length _ _) hsep.2.2.symm
  have hd : RationalAccumulator.Word t2.val (denominatorPort entry) (v entry).denominator :=
    by simpa only [dataValues_denominator] using ready2.1 (denominatorPort entry) (cell_mem he (by simp [cellPorts]))
  obtain ⟨c3,t3,h3,e3,m3,d3,z3,s3,b3,f3⟩ := BankArray.write_canonical
    210 indexBank 214 215 (denominatorPort entry) (by decide) (by omega) (by decide) (by decide)
    (by have := denominatorPort_ge entry; omega) (by decide) (by omega) (by decide)
    input tape a.width index a.baseDenominator a.clock a.denominator i (v entry).denominator a.width_pos
    hindex a.clock_length hpositive hfit.2.2 t2 z2 s2 b2 (meta2 _ (by decide) ha.width)
    (meta2 _ hiB hi) (meta2 _ (by decide) ha.baseDenominator) (meta2 _ (by decide) ha.clock) hd d2
  have meta3 (j : ℕ) (hj : 100 ≤ j) {xs : List Bool} (hx : BankArray.Word s.val j xs) :=
    BankArray.word_of_eq (f3.2.2.2.1 j (Or.inr (by omega)) (by omega)) (meta2 j hj hx)
  have p3 : BitArray.Represents t3.val.memory (addressValue a.basePositive) (addressValue a.width)
      (a.positive.set i (FixedWidth.bits (addressValue a.width) (v entry).positive.bits)) := by
    rw [m3]
    exact IncidenceEncoding.represents_write_disjoint p2 _ _ i _ (FixedWidth.bits_length _ _) hsep.2.1
  have n3 : BitArray.Represents t3.val.memory (addressValue a.baseNegative) (addressValue a.width)
      (a.negative.set i (FixedWidth.bits (addressValue a.width) (v entry).negative.bits)) := by
    rw [m3]
    exact IncidenceEncoding.represents_write_disjoint n2 _ _ i _ (FixedWidth.bits_length _ _) hsep.2.2
  refine ⟨c1+(c2+c3),t3,e1.seq (e2.seq e3),by omega,rationalReady_write_frame ready2 f3 z3,
    ⟨z3,s3,b3,meta3 _ (by decide) ha.width,meta3 _ (by decide) ha.basePositive,
      meta3 _ (by decide) ha.baseNegative,meta3 _ (by decide) ha.baseDenominator,
      meta3 _ (by decide) ha.clock,p3,n3,d3⟩,?_,?_⟩
  · rw [m3,m2,m1]
    rfl
  · exact ⟨f3.1.trans (f2.1.trans f1.1),f3.2.1.trans (f2.2.1.trans f1.2.1),
      f3.2.2.1.trans (f2.2.2.1.trans f1.2.2.1),fun j hj h37 =>
        (f3.2.2.2.1 j hj h37).trans ((f2.2.2.2.1 j hj h37).trans (f1.2.2.2.1 j hj h37)),
      fun j hj h24 h25 h26 h27 h28 h29 => (f3.2.2.2.2 j hj h24 h25 h26 h27 h28 h29).trans
        ((f2.2.2.2.2 j hj h24 h25 h26 h27 h28 h29).trans (f1.2.2.2.2 j hj h24 h25 h26 h27 h28 h29))⟩


#print axioms writeAt_executes
end Maxwell.Continuum.RationalDataflow.PartArray
