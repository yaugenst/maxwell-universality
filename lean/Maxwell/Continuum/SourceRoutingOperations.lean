import Maxwell.Continuum.SourceRoutingPairWrite
import Maxwell.Continuum.SourceRoutingAccessCost

/-! Fixed cursor tests and increments for the actual two-pointer completion
pass, together with uniform charges for the existing array reads and writes. -/

namespace Maxwell.Cost.RoutingPorts.Complete
open Structured
open RationalAccumulator (Blank)
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000

theorem pairCost_bound {n : ℕ} (l : Layout n) (i j : Fin n) :
    pairCost l i j≤operationCap l := by
  have h1 := layout_access_bound l i l.forward (by omega)
    (FixedWidth.bits n.bits.length j.val.bits) (FixedWidth.bits_length _ _)
  have h2 := layout_access_bound l j l.backward (by omega)
    (FixedWidth.bits n.bits.length i.val.bits) (FixedWidth.bits_length _ _)
  unfold pairCost
  omega

theorem probeCost_bound {n : ℕ} (l : Layout n) (i : Fin n) (base : ℕ)
    (hb : base.bits.length≤l.forward.bits.length+l.backward.bits.length) :
    BankArray.costCap n.bits.length.bits i.val.bits base.bits l.clock+
      102*n.bits.length+95≤operationCap l/2 := by
  have h := layout_access_bound l i base hb l.clock l.clock_length
  omega

def cursorTestCode (index : ℕ) : Code :=
  .seq (BankArray.packCanonicalCode index 718)
    (.seq (BankArray.compareCode 37 709) (.call (TapeOps.clear 37)))

theorem cursor_test {n : ℕ} (l : Layout n) (index i : ℕ) (hindex : 730 ≤ index)
    (hi : i≤n) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : Ready s.val) (hm : Metadata l s.val)
    (hw : RationalAccumulator.Word s.val index i) :
    ∃cost t, Executes input tape (cursorTestCode index) cost s t ∧
      cost≤200*n.bits.length+200 ∧ (t.val.registers 2=true ↔ i<n) ∧
      Ready t.val ∧ t.val.memory=s.val.memory ∧ Frame {37} s.val t.val := by
  have hfit : i.bits.length≤n.bits.length := by
    simp only [Nat.size_eq_bits_len]
    exact Nat.size_le_size hi
  have hp : 0<n.bits.length := RationalAccumulator.bits_nonempty l.positive
  obtain ⟨ca,a,hca,ea,wa,sa,a7,ac,af⟩ := BankArray.pack_canonical index 718
    (by omega) (by decide) input tape i.bits l.clock
    (by rw [l.clock_length]; exact hp) (by rw [l.clock_length]; exact hfit)
    s hs.scratch hs.seven hs.pack hw hm.clock
  rw [l.clock_length] at wa hca
  have an := RationalAccumulator.word_of_eq (af.2.2.2.1 709 (by decide) (by decide)) hm.count
  obtain ⟨b,eb,hb,sb,bm,bk,bf⟩ := BankArray.compare_bank 37 709 (by decide) (by decide)
    input tape (FixedWidth.bits n.bits.length i.bits) n.bits (FixedWidth.bits_length _ _)
    a wa an sa
  obtain ⟨origin,ho⟩ := wa
  obtain ⟨t,et,tt,tf⟩ := WordCall.clear 37 input tape (FixedWidth.bits n.bits.length i.bits)
    origin b ((bk 37 (by decide)).trans ho)
  have cf : Frame {37} b.val t.val := by
    refine ⟨tf.2.1,tf.2.2.2.1,tf.2.2.2.2.1,?_,?_⟩
    · intro j _ hj
      simp only [Finset.mem_singleton] at hj
      simp [tt,hj]
    · intro j _ _ _ h26 h27 _ _
      exact tf.2.2.2.2.2.2 j h26 h27
  have frame := (Frame.of_bankExcept af).trans ((Frame.of_bank bf).trans cf)
  have keep (j : ℕ) (hj : j≠37) : t.val.tapes j=b.val.tapes j := by simp [tt,hj]
  refine ⟨_,t,ea.seq (eb.seq et),?_,?_,?_,tf.2.2.1.trans (bm.trans ac.2.2.2.1),frame⟩
  · simp only [FixedWidth.bits_length]
    omega
  · rw [tf.2.2.2.2.2.2 2 (by decide) (by decide),hb,
      FixedWidth.bits_value _ _ hfit,addressValue_bits,addressValue_bits]
  · refine ⟨?_,?_,⟨origin+(FixedWidth.bits n.bits.length i.bits).length,by simp [tt]⟩,?_⟩
    · rcases sb with ⟨h0,h1,h2,h3,h5,h6,h8,h9⟩
      exact ⟨RationalAccumulator.blank_of_eq (keep 0 (by decide)) h0,
        RationalAccumulator.blank_of_eq (keep 1 (by decide)) h1,
        RationalAccumulator.blank_of_eq (keep 2 (by decide)) h2,
        RationalAccumulator.blank_of_eq (keep 3 (by decide)) h3,
        RationalAccumulator.blank_of_eq (keep 5 (by decide)) h5,
        RationalAccumulator.blank_of_eq (keep 6 (by decide)) h6,
        RationalAccumulator.blank_of_eq (keep 8 (by decide)) h8,
        RationalAccumulator.blank_of_eq (keep 9 (by decide)) h9⟩
    · exact RationalAccumulator.blank_of_eq ((keep 7 (by decide)).trans (bk 7 (by decide))) a7
    · exact RationalAccumulator.blank_of_eq (frame.tapes 752 (by decide) (by decide)) hs.probe

theorem increment_cursor (index i : ℕ) (hindex : index=730 ∨ index=731)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : Ready s.val) (hw : RationalAccumulator.Word s.val index i) :
    ∃cost t, Executes input tape (PhysicalEmit.incrementCode index) cost s t ∧
      cost≤12*i.bits.length+18 ∧ Ready t.val ∧
      RationalAccumulator.Word t.val index (i+1) ∧
      t.val.memory=s.val.memory ∧ Frame {index} s.val t.val := by
  obtain ⟨cost,t,hc,he,ht,hf⟩ := PhysicalEmit.increment index i input tape s hw
  have keep (j : ℕ) (hj : j≠index) := hf.tapes j (by simpa using hj)
  refine ⟨cost,t,he,hc,?_,ht,hf.memory,?_⟩
  · rcases hs.scratch with ⟨h0,h1,h2,h3,h5,h6,h8,h9⟩
    refine ⟨⟨RationalAccumulator.blank_of_eq (keep 0 (by omega)) h0,
      RationalAccumulator.blank_of_eq (keep 1 (by omega)) h1,
      RationalAccumulator.blank_of_eq (keep 2 (by omega)) h2,
      RationalAccumulator.blank_of_eq (keep 3 (by omega)) h3,
      RationalAccumulator.blank_of_eq (keep 5 (by omega)) h5,
      RationalAccumulator.blank_of_eq (keep 6 (by omega)) h6,
      RationalAccumulator.blank_of_eq (keep 8 (by omega)) h8,
      RationalAccumulator.blank_of_eq (keep 9 (by omega)) h9⟩,
      RationalAccumulator.blank_of_eq (keep 7 (by omega)) hs.seven,
      RationalAccumulator.blank_of_eq (keep 37 (by omega)) hs.pack,?_⟩
    exact RationalAccumulator.blank_of_eq (keep 752 (by omega)) hs.probe
  · exact ⟨hf.inputHead,hf.randomCursor,hf.output,
      fun j _ hj => hf.tapes j hj,
      fun j hj h24 h25 h26 h27 h28 h29 => hf.registers j (by omega) h24 h25 h26 h27 h28 h29⟩

#print axioms cursor_test
#print axioms increment_cursor

end Maxwell.Cost.RoutingPorts.Complete
