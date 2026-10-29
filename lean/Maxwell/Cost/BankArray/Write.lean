import Maxwell.Cost.BankArray.Common

namespace Maxwell.Cost.BankArray
open Structured
open RationalAccumulator (Blank)

def writeCode (widthBank indexBank baseBank payloadBank : ℕ) : Code :=
  .seq (prepare widthBank indexBank baseBank payloadBank) (.seq ArrayAccess.writeCode cleanup)

/-- A finite array write from persistent bank words, with an exact memory
interval update. The payload bank and tape 7 remain available to the caller. -/
theorem write_executes {n : ℕ} (widthBank indexBank baseBank payloadBank : ℕ)
    (hw : 10 ≤ widthBank) (hi : 10 ≤ indexBank) (hb : 10 ≤ baseBank) (hp : 10 ≤ payloadBank)
    (input : List Bool) (tape : ℕ → Bool)
    (width index base payload : List Bool) (words : Vector (List Bool) n) (i : Fin n)
    (wbank ibank bbank pbank : ℤ) (hwidth : 0 < width.length)
    (hindex : addressValue index = i.val) (hpayload : payload.length = addressValue width)
    (s : Store) (hscratch : Scratch s.val)
    (hwidthBank : s.val.tapes widthBank = BitTape.shifted width wbank)
    (hindexBank : s.val.tapes indexBank = BitTape.shifted index ibank)
    (hbaseBank : s.val.tapes baseBank = BitTape.shifted base bbank)
    (hpayloadBank : s.val.tapes payloadBank = BitTape.shifted payload pbank)
    (harray : BitArray.Represents s.val.memory (addressValue base) (addressValue width) words) :
    ∃ cost, ∃ t : Store, cost ≤ costCap width index base payload ∧
      Executes input tape (writeCode widthBank indexBank baseBank payloadBank) cost s t ∧
      t.val.memory = MemoryWord.writeBits s.val.memory (addressValue base+i.val*addressValue width) payload ∧
      BitArray.Represents t.val.memory (addressValue base) (addressValue width) (words.set i payload) ∧
      Scratch t.val ∧ t.val.tapes 7 = s.val.tapes 7 ∧ Frame s.val t.val := by
  rcases hscratch with ⟨⟨ao,h0⟩,⟨wo,h1⟩,⟨zo,h2⟩,⟨yo,h3⟩,
    ⟨io,h5⟩,⟨po,h6⟩,⟨bo,h8⟩,⟨saved,h9⟩⟩
  obtain ⟨p,ep,htapes,pf⟩ := prepare_executes widthBank indexBank baseBank payloadBank hw hi hb hp
    input tape width index base payload wo io bo po wbank ibank bbank pbank s h1 h5 h8 h6
    hwidthBank hindexBank hbaseBank hpayloadBank
  have hready : ArrayAccess.Ready p.val width index base ao wo zo yo io bo saved := by
    constructor
    · simpa [htapes] using h0
    · simp [htapes]
    · simpa [htapes] using h2
    · simpa [htapes] using h3
    · simp [htapes]
    · simp [htapes]
    · simpa [htapes] using h9
  obtain ⟨wcost,w,address,addressOrigin,hwcost,ew,hw5,_,hwlen,hw6,hwmem,hwarray,restored,wf,hw7⟩ :=
    ArrayAccess.write_executes input tape width index base payload words i ao wo zo yo io bo saved po
      hwidth hindex hpayload p hready (by simpa [pf.2.2.2.1] using harray) (by simp [htapes])
  obtain ⟨widthOrigin,hw1⟩ := restored.width
  obtain ⟨t,et,ttapes,tf⟩ := cleanup_executes input tape width address payload base
    widthOrigin addressOrigin po bo w hw1 hw5 hw6 restored.base
  have frame : Frame s.val t.val := by
    refine ⟨tf.1.trans (wf.1.trans pf.1),tf.2.1.trans (wf.2.1.trans pf.2.1),
      tf.2.2.1.trans (wf.2.2.1.trans pf.2.2.1),?_,?_⟩
    · intro j hj
      have hj1 : j ≠ 1 := by omega
      have hj5 : j ≠ 5 := by omega
      have hj6 : j ≠ 6 := by omega
      have hj8 : j ≠ 8 := by omega
      simp only [ttapes,Function.update_apply,hj1,hj5,hj6,hj8,↓reduceIte]
      rw [wf.2.2.2.1 j (by omega),htapes]
      simp [hj1,hj5,hj6,hj8]
    · intro j hj h24 h25 h26 h27 h28 h29
      exact (tf.2.2.2.2 j hj h24 h25 h26 h27 h28 h29).trans
        ((wf.2.2.2.2 j hj h24 h25 h26 h27 h28 h29).trans
          (pf.2.2.2.2 j hj h24 h25 h26 h27 h28 h29))
  refine ⟨_,t,?_,ep.seq (ew.seq et),?_,?_,?_,?_,frame⟩
  · dsimp [costCap]
    omega
  · rw [tf.2.2.2.1,hwmem,pf.2.2.2.1]
  · simpa only [tf.2.2.2.1] using hwarray
  · refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
    · obtain ⟨o,ho⟩ := restored.zero
      exact ⟨o,by simpa [ttapes] using ho⟩
    · exact ⟨widthOrigin+width.length,by simp [ttapes]⟩
    · obtain ⟨o,ho⟩ := restored.scratch
      exact ⟨o,by simpa [ttapes] using ho⟩
    · exact ⟨yo+index.length,by simpa [ttapes] using restored.multiply⟩
    · exact ⟨addressOrigin+address.length,by simp [ttapes]⟩
    · exact ⟨po+payload.length,by simp [ttapes]⟩
    · exact ⟨bo+base.length,by simp [ttapes]⟩
    · exact ⟨saved+width.length,by simpa [ttapes] using restored.saved⟩
  · simpa only [ttapes,htapes,Function.update_apply,show (7:ℕ) ≠ 1 by omega,
      show (7:ℕ) ≠ 5 by omega,show (7:ℕ) ≠ 6 by omega,show (7:ℕ) ≠ 8 by omega,↓reduceIte] using hw7

theorem write_run {n : ℕ} (widthBank indexBank baseBank payloadBank : ℕ)
    (hw : 10 ≤ widthBank) (hi : 10 ≤ indexBank) (hb : 10 ≤ baseBank) (hp : 10 ≤ payloadBank)
    (input : List Bool) (tape : ℕ → Bool)
    (width index base payload : List Bool) (words : Vector (List Bool) n) (i : Fin n)
    (wbank ibank bbank pbank : ℤ) (hwidth : 0 < width.length)
    (hindex : addressValue index = i.val) (hpayload : payload.length = addressValue width)
    (s : Store) (hscratch : Scratch s.val)
    (hwidthBank : s.val.tapes widthBank = BitTape.shifted width wbank)
    (hindexBank : s.val.tapes indexBank = BitTape.shifted index ibank)
    (hbaseBank : s.val.tapes baseBank = BitTape.shifted base bbank)
    (hpayloadBank : s.val.tapes payloadBank = BitTape.shifted payload pbank)
    (harray : BitArray.Represents s.val.memory (addressValue base) (addressValue width) words) :
    ∃ t : Store,
      (runPriced ((writeCode widthBank indexBank baseBank payloadBank).compile.next input tape)
        (costCap width index base payload+1) s.val).finished =
          some (t.place (writeCode widthBank indexBank baseBank payloadBank).size) ∧
      (runPriced ((writeCode widthBank indexBank baseBank payloadBank).compile.next input tape)
        (costCap width index base payload+1) s.val).instructions ≤ costCap width index base payload ∧
      t.val.memory = MemoryWord.writeBits s.val.memory (addressValue base+i.val*addressValue width) payload ∧
      BitArray.Represents t.val.memory (addressValue base) (addressValue width) (words.set i payload) ∧
      Scratch t.val ∧ t.val.tapes 7 = s.val.tapes 7 ∧ Frame s.val t.val := by
  obtain ⟨cost,t,hcost,he,ht⟩ := write_executes widthBank indexBank baseBank payloadBank hw hi hb hp
    input tape width index base payload words i wbank ibank bbank pbank hwidth hindex hpayload s hscratch
    hwidthBank hindexBank hbaseBank hpayloadBank harray
  have hr := he.compiled_run (costCap width index base payload+1) (by omega)
  exact ⟨t,hr.1,hr.2.symm ▸ hcost,ht⟩


theorem write_bank {n : ℕ} (widthBank indexBank baseBank payloadBank : ℕ)
    (hw : 10 ≤ widthBank) (hi : 10 ≤ indexBank) (hb : 10 ≤ baseBank) (hp : 10 ≤ payloadBank)
    (input : List Bool) (tape : ℕ → Bool)
    (width index base payload : List Bool) (words : Vector (List Bool) n) (i : Fin n)
    (hwidth : 0 < width.length) (hindex : addressValue index = i.val)
    (hpayload : payload.length = addressValue width) (s : Store) (hscratch : Scratch s.val)
    (hwidthBank : Word s.val widthBank width) (hindexBank : Word s.val indexBank index)
    (hbaseBank : Word s.val baseBank base) (hpayloadBank : Word s.val payloadBank payload)
    (harray : BitArray.Represents s.val.memory (addressValue base) (addressValue width) words) :
    ∃ cost, ∃ t : Store, cost ≤ costCap width index base payload ∧
      Executes input tape (writeCode widthBank indexBank baseBank payloadBank) cost s t ∧
      t.val.memory = MemoryWord.writeBits s.val.memory (addressValue base+i.val*addressValue width) payload ∧
      BitArray.Represents t.val.memory (addressValue base) (addressValue width) (words.set i payload) ∧
      Scratch t.val ∧ t.val.tapes 7 = s.val.tapes 7 ∧ Frame s.val t.val := by
  obtain ⟨wo,hwo⟩ := hwidthBank
  obtain ⟨io,hio⟩ := hindexBank
  obtain ⟨bo,hbo⟩ := hbaseBank
  obtain ⟨po,hpo⟩ := hpayloadBank
  exact write_executes widthBank indexBank baseBank payloadBank hw hi hb hp input tape
    width index base payload words i wo io bo po hwidth hindex hpayload s hscratch hwo hio hbo hpo harray

end Maxwell.Cost.BankArray
