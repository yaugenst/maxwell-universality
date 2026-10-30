import Maxwell.Continuum.RationalDataflowArrayOutputFrame

/-! Read generated cache entries directly through the output headers.
The original source headers remain available for the tensor-row loop. -/
namespace Maxwell.Continuum.RationalDataflow.PartArray
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 3500000
set_option maxRecDepth 8192

theorem Table.OutputReady.scalar_read_frame {n target : ℕ} {a : Table n} {s t : Store}
    (h : a.OutputReady s) (ht : 1000≤target) (f : ArrayRead.Frame target s.val t.val)
    (hz : BankArray.Scratch t.val) (h7 : RationalAccumulator.Blank t.val 7) : a.OutputReady t := by
  apply h.transfer f.memory _ hz h7
  intro i hi
  have hbounds : 10 ≤ i ∧ i<1000 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    omega
  exact f.tapes i hbounds.1 (by omega)

def cachedReadCode (indexBank target : ℕ) : Code :=
  .seq (ArrayRead.code 210 indexBank 212 215 (positivePort target))
    (.seq (ArrayRead.code 210 indexBank 213 215 (negativePort target))
      (ArrayRead.code 210 indexBank 214 215 (denominatorPort target)))

theorem cachedRead_executes {n : ℕ} (a : Table n) (S : Finset ℕ) (indexBank target : ℕ)
    (hib : 10 ≤ indexBank) (hib' : indexBank<1000) (ht : target∈S)
    (v : ℕ→Parts) (input : List Bool) (tape : ℕ→Bool) (index : List Bool) (i : Fin n)
    (hindex : addressValue index=i.val) (s : Store) (hs : RationalDataflow.Ready S v s)
    (ha : a.OutputReady s) (hi : BankArray.Word s.val indexBank index) :
    ∃cost t,Executes input tape (cachedReadCode indexBank target) cost s t ∧
      cost≤a.readCost index (v target) ∧
      RationalDataflow.Ready S (Function.update v target (a.get i)) t ∧ a.OutputReady t ∧
      BankArray.Word t.val indexBank index ∧ Frame target s.val t.val := by
  have hp := positivePort_ge target
  have hn := negativePort_ge target
  have hd := denominatorPort_ge target
  have pm : positivePort target∈ids S := cell_mem ht (by simp [cellPorts])
  have nm : negativePort target∈ids S := cell_mem ht (by simp [cellPorts])
  have dm : denominatorPort target∈ids S := cell_mem ht (by simp [cellPorts])
  obtain ⟨c1,t1,e1,h1,b1,z1,s1,_,f1⟩ := ArrayRead.executes (ids S) (ids_ge_ten S)
    210 indexBank 212 215 (positivePort target) (by decide) hib (by decide) (by decide) pm
    (by omega) (by omega) (by omega) (by omega) input tape a.width index a.basePositive a.clock
    a.positive i a.width_pos hindex a.clock_length (dataValues v) s hs.1 ha.scratch ha.seven
    ha.width hi ha.basePositive ha.clock ha.positive
  have a1 := ha.scalar_read_frame hp f1 z1 s1
  have i1 := BankArray.word_of_eq (f1.tapes indexBank hib (by omega)) hi
  obtain ⟨c2,t2,e2,h2,b2,z2,s2,_,f2⟩ := ArrayRead.executes (ids S) (ids_ge_ten S)
    210 indexBank 213 215 (negativePort target) (by decide) hib (by decide) (by decide) nm
    (by omega) (by omega) (by omega) (by omega) input tape a.width index a.baseNegative a.clock
    a.negative i a.width_pos hindex a.clock_length _ t1 b1 a1.scratch a1.seven
    a1.width i1 a1.baseNegative a1.clock a1.negative
  have a2 := a1.scalar_read_frame hn f2 z2 s2
  have i2 := BankArray.word_of_eq (f2.tapes indexBank hib (by omega)) i1
  obtain ⟨c3,t3,e3,h3,b3,z3,s3,_,f3⟩ := ArrayRead.executes (ids S) (ids_ge_ten S)
    210 indexBank 214 215 (denominatorPort target) (by decide) hib (by decide) (by decide) dm
    (by omega) (by omega) (by omega) (by omega) input tape a.width index a.baseDenominator a.clock
    a.denominator i a.width_pos hindex a.clock_length _ t2 b2 a2.scratch a2.seven
    a2.width i2 a2.baseDenominator a2.clock a2.denominator
  refine ⟨c1+(c2+c3),t3,e1.seq (e2.seq e3),?_,?_,a2.scalar_read_frame hd f3 z3 s3,
    BankArray.word_of_eq (f3.tapes indexBank hib (by omega)) i2,?_⟩
  · simp at h1 h2 h3
    unfold Table.readCost
    omega
  · constructor
    · change NatAssign.Bank (ids S) (writeParts (dataValues v) target (a.get i)) t3.val at b3
      rwa [writeParts_dataValues] at b3
    · intro k hk
      interval_cases k
      · exact z3.1
      · exact z3.2.1
      · exact z3.2.2.1
      · exact z3.2.2.2.1
  · refine ⟨f3.memory.trans (f2.memory.trans f1.memory),
      f3.inputHead.trans (f2.inputHead.trans f1.inputHead),
      f3.randomCursor.trans (f2.randomCursor.trans f1.randomCursor),
      f3.output.trans (f2.output.trans f1.output),?_⟩
    intro k hk hkt
    have kp : k≠positivePort target := by intro he;exact hkt (by simp [cellPorts,he])
    have kn : k≠negativePort target := by intro he;exact hkt (by simp [cellPorts,he])
    have kd : k≠denominatorPort target := by intro he;exact hkt (by simp [cellPorts,he])
    exact (f3.tapes k hk kd).trans ((f2.tapes k hk kn).trans (f1.tapes k hk kp))

theorem Table.Ready.cachedRead_frame {n target : ℕ} {a : Table n} {s t : Store}
    (h : a.Ready s) (f : Frame target s.val t.val) (hz : BankArray.Scratch t.val)
    (h7 : RationalAccumulator.Blank t.val 7) : a.Ready t := by
  have keep (i : ℕ) (hlo : 10 ≤ i) (hhi : i<1000) := f.tapes i hlo (by
    have hp := positivePort_ge target
    have hn := negativePort_ge target
    have hd := denominatorPort_ge target
    simp only [cellPorts,Finset.mem_insert,Finset.mem_singleton]
    omega)
  refine ⟨hz,h7,BankArray.word_of_eq (keep 200 (by decide) (by decide)) h.width,
    BankArray.word_of_eq (keep 202 (by decide) (by decide)) h.basePositive,
    BankArray.word_of_eq (keep 203 (by decide) (by decide)) h.baseNegative,
    BankArray.word_of_eq (keep 204 (by decide) (by decide)) h.baseDenominator,
    BankArray.word_of_eq (keep 205 (by decide) (by decide)) h.clock,?_,?_,?_⟩
  · simpa only [f.memory] using h.positive
  · simpa only [f.memory] using h.negative
  · simpa only [f.memory] using h.denominator

#print axioms cachedRead_executes
end Maxwell.Continuum.RationalDataflow.PartArray
