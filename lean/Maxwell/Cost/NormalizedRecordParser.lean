import Maxwell.Cost.NormalizedRecordParser.Header
import Maxwell.Cost.NormalizedRecordParser.Payload
import Maxwell.Cost.SourceCircuit.NormalizedRecord

/-! The normalized coefficients are parsed from the writable archive produced
by the finite normalization program. No host operation changes the immutable
input. Every archive read, movement, payload copy and rewind is charged. -/

namespace Maxwell.Cost.NormalizedRecordParser
open Structured

def code : Code := .seq (readNatural 15)
  (.seq (readNatural 16) (.seq (.call signProgram) Payload.code))

def work : Finset ℕ := {15,16,83,85}

private theorem cursor_bit (preceding : List Bool) (b : Bool) (suffix : List Bool) :
    (cursor (preceding ++ (b :: suffix)) preceding.length).read = some b := by
  simp [BitTape.read, BitTape.ofList]

private theorem cursor_payload (preceding bits suffix : List Bool) (k : ℕ) (hk : k < bits.length) :
    (cursor (preceding ++ (bits ++ suffix)) preceding.length).cells
      ((preceding.length : ℤ) + k) = bits[k]? := by
  have hz : 0 ≤ (preceding.length : ℤ) + k := by omega
  have hn : ((preceding.length : ℤ) + k).toNat = preceding.length + k := by omega
  simp [BitTape.ofList, hz, hn, List.getElem?_append, hk]

theorem executes (input : List Bool) (randomTape : ℕ → Bool)
    (row column : ℕ) (negative : Bool) (bits preceding suffix : List Bool)
    (clockOrigin outputOrigin : ℤ) (s : Store)
    (hsource : s.val.tapes 85 = cursor
      (preceding ++ (SourceCircuit.normalizedRecord row column negative bits ++ suffix)) preceding.length)
    (h10 : s.val.tapes 10 = BitTape.blank)
    (h15 : s.val.tapes 15 = BitTape.blank) (h16 : s.val.tapes 16 = BitTape.blank)
    (h83 : s.val.tapes 83 = {BitTape.blank with head := outputOrigin})
    (h82 : s.val.tapes 82 = BitTape.shifted (2^bits.length).bits clockOrigin) :
    ∃ cost t, Executes input randomTape code cost s t ∧
      cost ≤ 34*(row.bits.length+column.bits.length)+18*bits.length+54 ∧
      t.val.tapes 15 = BitTape.atEnd row.bits ∧ t.val.tapes 16 = BitTape.atEnd column.bits ∧
      t.val.registers 23 = negative ∧ t.val.tapes 83 = BitTape.shifted bits outputOrigin ∧
      t.val.tapes 85 = cursor
        (preceding ++ (SourceCircuit.normalizedRecord row column negative bits ++ suffix))
        (preceding.length + (SourceCircuit.normalizedRecord row column negative bits).length) ∧
      t.val.inputHead = s.val.inputHead ∧ Frame work s.val t.val := by
  let beforeColumn := preceding ++ Codec.nat row
  let beforeSign := beforeColumn ++ Codec.nat column
  let beforeBits := beforeSign ++ [negative]
  obtain ⟨ca, a, ea, caBound, ha85, ha10, ha15, hai, _, haf⟩ :=
    readNatural_executes 15 (by decide) (by decide) input randomTape row preceding
      (Codec.nat column ++ (negative :: (bits ++ suffix))) s
      (by simpa [SourceCircuit.normalizedRecord, List.append_assoc] using hsource) h10 h15
  have ha16 : a.val.tapes 16 = BitTape.blank := (haf.tapes 16 (by decide)).trans h16
  have haSource : a.val.tapes 85 = cursor
      (beforeColumn ++ (Codec.nat column ++ (negative :: (bits ++ suffix)))) beforeColumn.length := by
    simpa [beforeColumn, List.append_assoc] using ha85
  obtain ⟨cb, b, eb, cbBound, hb85, _, hb16, hbi, _, hbf⟩ :=
    readNatural_executes 16 (by decide) (by decide) input randomTape column beforeColumn
      (negative :: (bits ++ suffix)) a haSource ha10 ha16
  have hbSource : b.val.tapes 85 = cursor (beforeSign ++ (negative :: (bits ++ suffix))) beforeSign.length := by
    simpa [beforeSign, List.append_assoc] using hb85
  have eSign := sign_executes input randomTape negative b (by rw [hbSource]; exact cursor_bit _ _ _)
  let c := Store.ofState (signFinish negative b.val)
  have hcSource : c.val.tapes 85 = cursor (beforeBits ++ (bits ++ suffix)) beforeBits.length := by
    simp [c, Store.ofState, signFinish, hbSource, beforeBits, List.append_assoc]
  have hc83 : c.val.tapes 83 = {BitTape.blank with head := outputOrigin} := by
    simpa [c, Store.ofState, signFinish] using
      ((hbf.tapes 83 (by decide)).trans (haf.tapes 83 (by decide))).trans h83
  have hc82 : c.val.tapes 82 = BitTape.shifted (2^bits.length).bits clockOrigin := by
    simpa [c, Store.ofState, signFinish] using
      ((hbf.tapes 82 (by decide)).trans (haf.tapes 82 (by decide))).trans h82
  have hcBits : ∀ k < bits.length, (c.val.tapes 85).cells ((c.val.tapes 85).head+k) = bits[k]? := by
    intro k hk
    rw [hcSource]
    exact cursor_payload beforeBits bits suffix k hk
  obtain ⟨t, et, _, ht85, ht83, hti, hta, htm, htr, hto, hts, htapes⟩ :=
    Payload.executes input randomTape bits clockOrigin outputOrigin c hc82 hcBits hc83
  have hcFrame : Frame {85} b.val c.val := by
    have h := sign_frame negative b.val
    exact ⟨h.address,h.memory,h.randomCursor,h.output,h.tapes⟩
  have htFrame : Frame {83,85} c.val t.val := by
    refine ⟨hta, htm, htr, hto, ?_⟩
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
    exact htapes i hi.1 hi.2
  have hframe : Frame work s.val t.val :=
    ((haf.mono (by decide)).trans (hbf.mono (by decide))).trans
      ((hcFrame.mono (by decide)).trans (htFrame.mono (by decide)))
  refine ⟨ca+cb+4+(18*bits.length+16), t, ?_, by omega, ?_, ?_, ?_, ht83, ?_,
    hti.trans (hbi.trans hai), hframe⟩
  · convert ea.seq (eb.seq (eSign.seq et)) using 1 <;> first | rfl | omega
  · simpa [c, Store.ofState, signFinish] using
      (htapes 15 (by decide) (by decide)).trans ((hbf.tapes 15 (by decide)).trans ha15)
  · simpa [c, Store.ofState, signFinish] using (htapes 16 (by decide) (by decide)).trans hb16
  · simpa [c, Store.ofState, signFinish] using hts
  · simpa [hcSource, beforeBits, beforeSign, beforeColumn,
      SourceCircuit.normalizedRecord, List.append_assoc, add_assoc, add_comm, add_left_comm] using ht85

/-- Actual one-time rewind after the normalizer has written the archive.
The finite parser above subsequently advances monotonically through it. -/
def rewindCode : Code := .call (Rewind.program 85)

theorem rewind_executes (input : List Bool) (randomTape : ℕ → Bool)
    (archive : List Bool) (s : Store) (h85 : s.val.tapes 85 = BitTape.atEnd archive) :
    ∃ t, Executes input randomTape rewindCode (4*archive.length+6) s t ∧
      t.val.tapes 85 = BitTape.ofList archive ∧ t.val.inputHead = s.val.inputHead ∧
      Frame {85} s.val t.val := by
  have hs := Rewind.atEnd_steps 85 input randomTape archive s.val s.property h85
  let t := Store.ofState (Rewind.finish 85 s.val)
  refine ⟨t, .call _ s _ _ hs (by simp [Rewind.program, Rewind.finish]),
    Rewind.finish_tape 85 archive s.val h85, rfl, ⟨rfl,rfl,rfl,rfl,?_⟩⟩
  intro i hi
  simp only [Finset.mem_singleton] at hi
  simp [t, Store.ofState, Rewind.finish, hi]

theorem run (input : List Bool) (randomTape : ℕ → Bool)
    (row column : ℕ) (negative : Bool) (bits preceding suffix : List Bool)
    (clockOrigin outputOrigin : ℤ) (s : Store)
    (hsource : s.val.tapes 85 = cursor
      (preceding ++ (SourceCircuit.normalizedRecord row column negative bits ++ suffix)) preceding.length)
    (h10 : s.val.tapes 10 = BitTape.blank)
    (h15 : s.val.tapes 15 = BitTape.blank) (h16 : s.val.tapes 16 = BitTape.blank)
    (h83 : s.val.tapes 83 = {BitTape.blank with head := outputOrigin})
    (h82 : s.val.tapes 82 = BitTape.shifted (2^bits.length).bits clockOrigin) :
    ∃ (cost : ℕ) (t : Store), (runPriced (code.compile.next input randomTape)
        (34*(row.bits.length+column.bits.length)+18*bits.length+55) s.val).finished =
          some (t.place code.size) ∧
      (runPriced (code.compile.next input randomTape)
        (34*(row.bits.length+column.bits.length)+18*bits.length+55) s.val).instructions = cost ∧
      cost ≤ 34*(row.bits.length+column.bits.length)+18*bits.length+54 ∧
      t.val.tapes 15 = BitTape.atEnd row.bits ∧ t.val.tapes 16 = BitTape.atEnd column.bits ∧
      t.val.registers 23 = negative ∧ t.val.tapes 83 = BitTape.shifted bits outputOrigin ∧
      t.val.inputHead = s.val.inputHead ∧ Frame work s.val t.val := by
  obtain ⟨cost,t,he,hcost,h15',h16',h23',h83',_,hi,hf⟩ := executes input randomTape row column
    negative bits preceding suffix clockOrigin outputOrigin s hsource h10 h15 h16 h83 h82
  have hr := he.compiled_run (34*(row.bits.length+column.bits.length)+18*bits.length+55) (by omega)
  exact ⟨cost,t,hr.1,hr.2,hcost,h15',h16',h23',h83',hi,hf⟩

end Maxwell.Cost.NormalizedRecordParser
