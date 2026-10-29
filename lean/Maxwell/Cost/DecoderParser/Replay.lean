import Maxwell.Cost.DecoderParser.MetadataProduct
import Maxwell.Cost.DecoderParser.ArchiveRewind
import Maxwell.Cost.Structured.Counted

namespace Maxwell.Cost.DecoderParser.Replay
open Structured

/-- Only the named tapes change; the loaded bit memory is preserved. -/
structure Frame (work : Finset ℕ) (s t : BitRAMState) : Prop where
  address : t.address = s.address
  memory : t.memory = s.memory
  randomCursor : t.randomCursor = s.randomCursor
  output : t.output = s.output
  tapes : ∀ j ∉ work, t.tapes j = s.tapes j

theorem Frame.trans {work : Finset ℕ} {s t u : BitRAMState}
    (h : Frame work s t) (k : Frame work t u) : Frame work s u :=
  ⟨k.address.trans h.address, k.memory.trans h.memory,
    k.randomCursor.trans h.randomCursor, k.output.trans h.output,
    fun i hi => (k.tapes i hi).trans (h.tapes i hi)⟩

theorem Frame.mono {a b : Finset ℕ} {s t : BitRAMState} (h : Frame a s t)
    (hab : a ⊆ b) : Frame b s t :=
  ⟨h.address, h.memory, h.randomCursor, h.output,
    fun i hi => h.tapes i (fun hh => hi (hab hh))⟩

def retreat : Code := Code.atom .inputLeft

def retreated (s : BitRAMState) : BitRAMState :=
  {s with pc := 1, inputHead := s.inputHead - 1}

theorem retreat_steps (input : List Bool) (tape : ℕ → Bool) (s : Store) :
    Executes input tape retreat 2 s (Store.ofState (retreated s.val)) := by
  apply Executes.atom (extra := 0)
  · simp [BitRAM.next, s.property, retreated]
  · rfl

/-- A real binary countdown performs the message-length input rewind. -/
theorem countdown_steps (input : List Bool) (tape : ℕ → Bool)
    (word : List Bool) (s : Store) (hword : s.val.tapes 63 = BitTape.ofList word) :
    ∃ cost t finalWord,
      Executes input tape (Counted.code 63 retreat) cost s t ∧
      cost ≤ (addressValue word + 1) * (13 * word.length + 15) + 2 * addressValue word ∧
      t.val.inputHead = s.val.inputHead - addressValue word ∧
      t.val.tapes 63 = BitTape.ofList finalWord ∧ finalWord.length = word.length ∧
      Frame {63} s.val t.val := by
  let invariant := fun n : ℕ => fun t : Store =>
    t.val.inputHead = s.val.inputHead - (addressValue word : ℤ) + n ∧ Frame {63} s.val t.val
  have stable : ∀ n a b, Counted.Frame 63 a b → invariant n a → invariant n b := by
    intro n a b hf hi
    rcases hf with ⟨ha, hh, hm, hr, ho, ht, _⟩
    exact ⟨hh.trans hi.1, hi.2.trans ⟨ha, hm, hr, ho, fun j hj => ht j (by simpa using hj)⟩⟩
  have bodyCorrect : ∀ n xs a, invariant (n + 1) a →
      a.val.tapes 63 = BitTape.ofList xs → addressValue xs = n →
      ∃ bodyCost b, Executes input tape retreat bodyCost a b ∧
        invariant n b ∧ b.val.tapes 63 = BitTape.ofList xs ∧ bodyCost ≤ 2 := by
    intro n xs a hi hw _
    refine ⟨2, Store.ofState (retreated a.val), retreat_steps input tape a, ?_, hw, le_rfl⟩
    refine ⟨?_, ?_⟩
    · change a.val.inputHead - 1 = _
      have hh := hi.1
      dsimp [invariant] at hh
      omega
    · exact ⟨hi.2.address, hi.2.memory, hi.2.randomCursor, hi.2.output, hi.2.tapes⟩
  have initial : invariant (addressValue word) s :=
    ⟨by simp, ⟨rfl, rfl, rfl, rfl, fun _ _ => rfl⟩⟩
  obtain ⟨cost, t, finalWord, he, hi, hw, hl, _, hc⟩ :=
    Counted.executes 63 retreat input tape invariant (fun _ => 2) stable bodyCorrect
      (addressValue word) word s rfl hword initial
  refine ⟨cost, t, finalWord, he, ?_, ?_, hw, hl, hi.2⟩
  · simpa [Finset.sum_const, Nat.mul_comm] using hc
  · simpa [invariant] using hi.1

/-- The loader's actual final address supplies the rewind count. -/
def code : Code := .seq (.call (Rewind.program 61))
  (.seq (.call (WordTransfer.clone 61 63))
    (.seq (Counted.code 63 retreat) (.call ArchiveRewind.program)))

def program : BitRAM := code.compile

def costBound (B n archived : ℕ) : ℕ :=
  19 * B + 23 + ((n + 1) * (13 * B + 15) + 2 * n) + (6 * archived + 6)

/-- Replay preserves all loaded memory and all metadata tapes. Archive18
returns to its first bit, and the sequential input returns to the target. -/
theorem steps (input : List Bool) (tape : ℕ → Bool) (address archive : List Bool)
    (s : Store) (ha : s.val.tapes 61 = BitTape.shiftedEnd address 0)
    (hc : s.val.tapes 63 = BitTape.blank)
    (harchive : s.val.tapes 18 = BitTape.shiftedEnd archive 0) :
    ∃ cost t finalCounter,
      Executes input tape code cost s t ∧
      cost ≤ costBound address.length (addressValue address) archive.length ∧
      t.val.inputHead = s.val.inputHead - addressValue address - archive.length ∧
      t.val.tapes 18 = BitTape.ofList archive ∧
      t.val.tapes 61 = BitTape.ofList address ∧
      t.val.tapes 63 = BitTape.ofList finalCounter ∧ finalCounter.length = address.length ∧
      Frame {18, 61, 63} s.val t.val := by
  obtain ⟨er, hra⟩ := WordTransfer.rewind_shifted 61 0 input tape address s.val s.property ha
  let r := Store.ofState (Rewind.finishAt 61 0 s.val)
  have erh := Executes.call (Rewind.program 61) s _ _ er (by rfl)
  have fr : Frame {61} s.val r.val := by
    refine ⟨rfl, rfl, rfl, rfl, ?_⟩
    intro j hj
    simp only [Finset.mem_singleton] at hj
    simp [r, Store.ofState, Rewind.finishAt, hj]
  have hr63 : r.val.tapes 63 = BitTape.blank := (fr.tapes 63 (by simp)).trans hc
  obtain ⟨c, ec, hcp, hc61, hc63, fc⟩ := WordTransfer.clone_steps 61 63 (by decide)
    input tape address 0 0 r.val r.property hra hr63
  have ech := Executes.call (WordTransfer.clone 61 63) r _ _ ec (by
    simp [WordTransfer.clone, hcp, Copy.program, Rewind.program, BitRAMInstruction.relocate])
  let c' := Store.ofState c
  have fc' : Frame {63} r.val c'.val := by
    refine ⟨fc.1, fc.2.2.1, fc.2.2.2.1, fc.2.2.2.2.1, ?_⟩
    intro j hj
    by_cases hj61 : j = 61
    · subst j
      exact hc61.trans hra.symm
    · exact fc.2.2.2.2.2.1 j hj61 (by simpa using hj)
  have hcword : c'.val.tapes 63 = BitTape.ofList address := by
    change c.tapes 63 = _
    simpa [BitTape.shifted, BitTape.ofList] using hc63
  obtain ⟨dc, d, finalWord, ed, hdc, hdi, hd63, hdlen, fd⟩ :=
    countdown_steps input tape address c' hcword
  have fp : Frame {61, 63} s.val d.val :=
    ((fr.mono (by decide)).trans (fc'.mono (by decide))).trans (fd.mono (by decide))
  have hdarchive := (fp.tapes 18 (by simp)).trans harchive
  obtain ⟨ea, hai, hat, ham, har, hao, haf⟩ := ArchiveRewind.executes input tape archive d hdarchive
  let t := Store.ofState (ArchiveRewind.finish archive.length d.val)
  have fa : Frame {18} d.val t.val :=
    ⟨rfl, ham, har, hao, fun j hj => haf j (by simpa using hj)⟩
  refine ⟨_, t, finalWord, erh.seq (ech.seq (ed.seq ea)), ?_, ?_, hat, ?_,
    (fa.tapes 63 (by simp)).trans hd63, hdlen,
    (fp.mono (by decide)).trans (fa.mono (by decide))⟩
  · dsimp [costBound]
    omega
  · change (ArchiveRewind.finish archive.length d.val).inputHead = _
    have hci : c'.val.inputHead = s.val.inputHead := fc.2.1
    rw [hai, hdi, hci]
  · have hdt : d.val.tapes 61 = BitTape.shifted address 0 := (fd.tapes 61 (by simp)).trans hc61
    simpa [BitTape.shifted, BitTape.ofList] using (fa.tapes 61 (by simp)).trans hdt

def loadCode : Code := .seq MetadataProduct.loadCode code

def loadProgram : BitRAM := loadCode.compile

def loadCostBound (i f samples archived : ℕ) : ℕ :=
  MetadataProduct.loadCostBound i f samples +
    costBound (samples * (1 + i + f)).bits.length (samples * (1 + i + f)) archived

/-- The complete metadata-driven load and rewind has no supplied total-count
or input-head-reset instruction. It is ready for the linear second pass. -/
theorem load_messages_steps {ι : Type*} {n : ℕ} (D : Target.WeightedDecoder ι n)
    (messages : D.Messages) (preceding suffix : List Bool) (randomTape : ℕ → Bool)
    (s : Store) (hhead : s.val.inputHead = preceding.length)
    (hblank : ∀ j ∈ MetadataProduct.work, s.val.tapes j = BitTape.blank)
    (haddress : s.val.tapes 61 = BitTape.blank)
    (hcounter : s.val.tapes 63 = BitTape.blank)
    (harchive : s.val.tapes 18 = BitTape.shiftedEnd preceding 0)
    (hi : s.val.tapes 41 = BitTape.ofList D.format.integerBits.bits)
    (hf : s.val.tapes 42 = BitTape.ofList D.format.fractionalBits.bits)
    (hs : s.val.tapes 43 = BitTape.ofList D.sampleCount.bits) :
    ∃ cost t,
      Executes (preceding ++ (Codec.messages D messages ++ suffix)) randomTape loadCode cost s t ∧
      cost ≤ loadCostBound D.format.integerBits D.format.fractionalBits D.sampleCount preceding.length ∧
      t.val.inputHead = 0 ∧ t.val.tapes 18 = BitTape.ofList preceding ∧
      t.val.memory = MemoryWord.writeBits s.val.memory 0 (Codec.messages D messages) ∧
      t.val.randomCursor = s.val.randomCursor ∧ t.val.output = s.val.output ∧
      (∀ j, j ∉ MetadataProduct.work → j ≠ 18 → j ≠ 61 → j ≠ 63 → t.val.tapes j = s.val.tapes j) ∧
      (∀ j ∈ ({0, 1, 2, 3, 64} : Finset ℕ), ∃ origin : ℤ,
        t.val.tapes j = {BitTape.blank with head := origin}) := by
  obtain ⟨lc, l, address, el, hlc, hli, hlm, hla, hlav, hlal, hlr, hlo, hlf, hls⟩ :=
    MetadataProduct.load_messages_steps D messages preceding suffix randomTape s hhead hblank haddress hi hf hs
  have hl63 : l.val.tapes 63 = BitTape.blank := (hlf 63 (by decide) (by decide)).trans hcounter
  have hl18 : l.val.tapes 18 = BitTape.shiftedEnd preceding 0 :=
    (hlf 18 (by decide) (by decide)).trans harchive
  obtain ⟨rc, r, counter, er, hrc, hri, hr18, _, _, _, fr⟩ :=
    steps (preceding ++ (Codec.messages D messages ++ suffix)) randomTape address preceding l hla hl63 hl18
  refine ⟨lc + rc, r, el.seq er, ?_, ?_, hr18, fr.memory.trans hlm,
    fr.randomCursor.trans hlr, fr.output.trans hlo, ?_, ?_⟩
  · have hmon : costBound address.length (addressValue address) preceding.length ≤
        costBound (D.sampleCount * D.format.width).bits.length
          (D.sampleCount * D.format.width) preceding.length := by
      rw [hlav]
      dsimp [costBound]
      gcongr
    have hh := Nat.add_le_add hlc (hrc.trans hmon)
    simpa only [loadCostBound, Target.FixedPointFormat.width] using hh
  · rw [hri, hli, hlav, hhead]
    omega
  · intro j hj hj18 hj61 hj63
    exact (fr.tapes j (by simp [hj18, hj61, hj63])).trans (hlf j hj hj61)
  · intro j hj
    obtain ⟨origin, ho⟩ := hls j hj
    have hn : j ∉ ({18, 61, 63} : Finset ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj ⊢
      omega
    exact ⟨origin, (fr.tapes j hn).trans ho⟩

end Maxwell.Cost.DecoderParser.Replay
