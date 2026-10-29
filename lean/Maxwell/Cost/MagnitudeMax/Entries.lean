import Maxwell.Cost.MagnitudeMax.SourceLoop
import Maxwell.Cost.MagnitudeMax.Save

namespace Maxwell.Cost.MagnitudeMax.Entries

open Structured RationalAccumulator

def code : Code := .seq (DecoderParser.readNatural 14)
  (.seq (.call (WordTransfer.clone 14 79)) (.seq (Code.atom (.literal 33 false)) SourceLoop.code))

def price (entries : List LogEntries.Entry) (B : ℕ) : ℕ :=
  36 * entries.length.bits.length + 35 + SourceLoop.price entries.length.bits entries B

def Frame (s t : BitRAMState) : Prop :=
  t.address = s.address ∧ t.memory = s.memory ∧ t.randomCursor = s.randomCursor ∧ t.output = s.output ∧
  (∀ i, 4 ≤ i → i ≠ 10 → i ≠ 12 → i ≠ 13 → i ≠ 14 → i ≠ 15 → i ≠ 16 →
    i ≠ 18 → i ≠ 22 → i ≠ 24 → i ≠ 79 → (i < 30 ∨ 36 < i) → t.tapes i = s.tapes i)

theorem executes (entries : List LogEntries.Entry) (current : Pair) (B : ℕ)
    (preceding suffix archive : List Bool) (tape : ℕ → Bool) (s : Store)
    (hhead : s.val.inputHead = preceding.length) (hcounter : s.val.tapes 14 = BitTape.blank)
    (hcountSave : Blank s.val 79)
    (hpositive : 0 < current.2)
    (hcurrent : current.1.bits.length ≤ B ∧ current.2.bits.length ≤ B)
    (hwidth : ∀ p ∈ entries, SourceLoop.Width B p)
    (hbank : Bank s.val (bankOf current)) (hready : Scratch s.val 0)
    (hparser : LogEntry.Ready s.val) (harchive : s.val.tapes 18 = BitTape.atEnd archive)
    (hprevious : s.val.tapes 22 = BitTape.atEnd []) (hboundaries : s.val.tapes 24 = BitTape.atEnd []) :
    ∃ cost, ∃ t : Store, cost ≤ price entries B ∧
      Executes (preceding ++ (Codec.list LogEntries.encodeEntry entries ++ suffix)) tape code cost s t ∧
      t.val.inputHead = s.val.inputHead + (Codec.list LogEntries.encodeEntry entries).length ∧
      Bank t.val (bankOf (scan current (SourceLoop.values entries))) ∧ Scratch t.val 0 ∧ LogEntry.Ready t.val ∧
      t.val.tapes 18 = BitTape.atEnd (archive ++ LogEntries.records entries) ∧
      t.val.tapes 22 = BitTape.atEnd (SourceGrouping.lastWord [] entries) ∧
      t.val.tapes 24 = BitTape.atEnd (SourceGrouping.markers [] false entries) ∧
      Word t.val 79 entries.length ∧ Frame s.val t.val := by
  let input := preceding ++ (Codec.list LogEntries.encodeEntry entries ++ suffix)
  obtain ⟨u, hu, huhead, huword, hu10, huf⟩ := DecoderParser.readNatural_steps 14 (by decide)
    entries.length preceding (LogEntries.records entries ++ suffix) tape s hhead hparser.1 hcounter
  have hi : preceding ++ (Codec.nat entries.length ++ (LogEntries.records entries ++ suffix)) = input := by
    simp [input, Codec.list, LogEntries.records, List.append_assoc]
  rw [hi] at hu
  obtain ⟨w, hw, hw79, hwhead, hwf⟩ := Save.clone 14 79 entries.length (by decide) input tape u
    ⟨0, by simpa using huword⟩ (blank_of_eq (huf.tapes 79 (by simp)) hcountSave)
  let v := Store.ofState (w.val.setRegister 33 false)
  have hv := Executes.literal input tape w 33 false
  have huother (i : ℕ) (hi : i ≠ 14) (h79 : i ≠ 79) : v.val.tapes i = s.val.tapes i :=
    (hwf.tapes i (by simpa using h79)).trans (huf.tapes i (by simpa using hi))
  have hubank : Bank v.val (bankOf current) := by
    intro i hi hi'
    exact word_of_eq (huother i (by omega) (by omega)) (hbank i hi hi')
  have huready : Scratch v.val 0 :=
    ⟨blank_of_eq (huother 0 (by decide) (by decide)) hready.1,
      word_of_eq (huother 1 (by decide) (by decide)) hready.2.1,
      blank_of_eq (huother 2 (by decide) (by decide)) hready.2.2.1,
      blank_of_eq (huother 3 (by decide) (by decide)) hready.2.2.2⟩
  have huparser : LogEntry.Ready v.val :=
    ⟨(hwf.tapes 10 (by simp)).trans hu10, (huother 15 (by decide) (by decide)).trans hparser.2.1,
      (huother 16 (by decide) (by decide)).trans hparser.2.2.1,
      (huother 12 (by decide) (by decide)).trans hparser.2.2.2.1,
      (huother 13 (by decide) (by decide)).trans hparser.2.2.2.2⟩
  have hunext : v.val.inputHead = (preceding ++ Codec.nat entries.length).length := by
    simpa [hhead, v, Store.ofState, BitRAMState.setRegister] using hwhead.trans huhead
  obtain ⟨c, t, hc, ht, hthead, htbank, htready, htparser, htlog, htprev, htbounds, _, htf⟩ :=
    SourceLoop.executes entries current B entries.length.bits [] false (preceding ++ Codec.nat entries.length)
      suffix archive [] tape v hunext (addressValue_bits entries.length)
      ((hwf.tapes 14 (by simp)).trans huword) hpositive hcurrent
      hwidth (by simp) hubank huready huparser ((huother 18 (by decide) (by decide)).trans harchive)
      ((huother 22 (by decide) (by decide)).trans hprevious) ((huother 24 (by decide) (by decide)).trans hboundaries)
      (by simp [v, Store.ofState, BitRAMState.setRegister])
  have hi' : (preceding ++ Codec.nat entries.length) ++ (LogEntries.records entries ++ suffix) = input := by
    simp [input, Codec.list, LogEntries.records, List.append_assoc]
  rw [hi'] at ht
  refine ⟨21 * entries.length.bits.length + 16 + ((15 * entries.length.bits.length + 17) + (2 + c)), t, by dsimp [price]; omega,
    hu.seq (hw.seq (hv.seq ht)), ?_, htbank, htready, htparser, htlog, htprev, ?_, ?_, ?_⟩
  · simp only [Codec.list, List.length_append]
    dsimp only [LogEntries.records] at hthead
    change t.val.inputHead = w.val.inputHead + _ at hthead
    omega
  · simpa using htbounds
  · exact word_of_eq (htf.2.2.2.2 79 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (Or.inr (by decide))) hw79
  · refine ⟨htf.1.trans (hwf.address.trans huf.address), htf.2.1.trans (hwf.memory.trans huf.memory),
      htf.2.2.1.trans (hwf.randomCursor.trans huf.randomCursor),
      htf.2.2.2.1.trans (hwf.output.trans huf.output), ?_⟩
    intro i h4 h10 h12 h13 h14 h15 h16 h18 h22 h24 h79 hb
    exact (htf.2.2.2.2 i h4 h10 h12 h13 h14 h15 h16 h18 h22 h24 hb).trans (huother i h14 h79)

end Maxwell.Cost.MagnitudeMax.Entries
