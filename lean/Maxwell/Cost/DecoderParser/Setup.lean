import Maxwell.Cost.DecoderParser.Prepare
import Maxwell.Cost.DecoderParser.Output
import Maxwell.Cost.DecoderParser.EvaluatorState
import Maxwell.Cost.DecoderConstants

namespace Maxwell.Cost.DecoderParser
open Structured
open RationalAccumulator (Bank Scratch Word Blank)

def setupCode : Code := .seq prepareCode (.seq DecoderConstants.code
  (.seq Output.headerCode (readNatural 72)))

def setupPrice {n : ℕ} (I : Target.Instance n) : ℕ := preparePrice I +
  DecoderConstants.costBound I.decoder.format.integerBits I.decoder.format.fractionalBits +
  (20*n.bits.length+24) + (21*n.bits.length+16)

structure SetupState {n : ℕ} (I : Target.Instance n) (w : I.decoder.Messages)
    (s : BitRAMState) : Prop where
  ready : EvalReady I.decoder.format s
  bank : Bank s (fun _ => 0)
  messages : BitArray.Represents s.memory 0 I.decoder.format.width (messageWords I.decoder w)
  counter : s.tapes 72 = BitTape.ofList n.bits
  supportCounter : s.tapes 73 = BitTape.blank
  inputHead : s.inputHead = (beforeRows I ++ Codec.nat n).length
  output : s.output = (Codec.nat n).reverse
  randomCursor : s.randomCursor = 0
  metadata : DecoderMetadata I s

/-- All decoder setup is one actual fixed program. Every stored format
constant and every message bit is produced or loaded by its finite execution. -/
theorem setup_steps {n : ℕ} (I : Target.Instance n) (w : I.decoder.Messages)
    (randomTape : ℕ → Bool) :
    ∃ cost, ∃ t : Store, Executes (Codec.target I ++ Codec.messages I.decoder w)
      randomTape setupCode cost (Store.ofState BitRAMState.initial) t ∧
      cost ≤ setupPrice I ∧ SetupState I w t.val := by
  let input := Codec.target I ++ Codec.messages I.decoder w
  obtain ⟨ca, a, ea, hca, hahead, hameta, _, hamem, harandom, haoutput, hab, hafree⟩ :=
    prepare_steps I w randomTape
  have hblank (i : ℕ) (hi : i < 4 ∨ (64 ≤ i ∧ i ≤ 68)) : Blank a.val i := by
    by_cases hlow : i < 4
    · exact hab i (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega)
    by_cases h64 : i = 64
    · exact hab i (by simp [h64])
    refine ⟨0, ?_⟩
    exact hafree i (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) h64
  have ha41 : Word a.val 41 I.decoder.format.integerBits :=
    ⟨0, by simpa [BitTape.ofList, BitTape.shifted] using hameta.integerBits⟩
  have ha42 : Word a.val 42 I.decoder.format.fractionalBits :=
    ⟨0, by simpa [BitTape.ofList, BitTape.shifted] using hameta.fractionalBits⟩
  obtain ⟨cb, b, hcb, eb, hb64, hb66, hb67, hbb, hb65, _, hbf⟩ :=
    DecoderConstants.executes input randomTape _ _ a ha41 ha42 hblank
  have hb40 : Word b.val 40 n := ⟨0, by
    rw [hbf.2.2.2.2.2.1 40 (by decide) (Or.inl (by decide)), hameta.dimension]
    simp [BitTape.ofList, BitTape.shifted]⟩
  have hbwidth : Word b.val 64 I.decoder.format.width := by
    simpa [Target.FixedPointFormat.width, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hb64
  obtain ⟨c, ec, hco, hcf⟩ := Output.header input randomTape n b hb40
  have hc10 : c.val.tapes 10 = BitTape.blank :=
    (congrFun hcf.2.2.2.2.1 10).trans ((hbf.2.2.2.2.2.1 10 (by decide) (Or.inl (by decide))).trans
      (hafree 10 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)))
  have hc72 : c.val.tapes 72 = BitTape.blank :=
    (congrFun hcf.2.2.2.2.1 72).trans ((hbf.2.2.2.2.2.1 72 (by decide) (Or.inr (by decide))).trans
      (hafree 72 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)))
  have hchead : c.val.inputHead = (beforeRows I).length :=
    hcf.2.1.trans (hbf.2.1.trans hahead)
  let suffix := (rowPayload I.decoder).flatMap (wire rowShape) ++ Codec.messages I.decoder w
  have hinput : beforeRows I ++ (Codec.nat n ++ suffix) = input := by
    simp [input, suffix, target_beforeRows, Codec.list, rowPayload, List.append_assoc]
  obtain ⟨t, et, hthead, ht72, _, htf⟩ := readNatural_steps 72 (by decide) n
    (beforeRows I) suffix randomTape c hchead hc10 hc72
  rw [hinput] at et
  have tkeep (i : ℕ) (hi : 4 ≤ i) (hmid : i < 64 ∨ 68 < i) (h72 : i ≠ 72) :
      t.val.tapes i = a.val.tapes i :=
    (htf.tapes i (by simpa using h72)).trans ((congrFun hcf.2.2.2.2.1 i).trans
      (hbf.2.2.2.2.2.1 i hi hmid))
  have tfromb (i : ℕ) (h72 : i ≠ 72) : t.val.tapes i = b.val.tapes i :=
    (htf.tapes i (by simpa using h72)).trans (congrFun hcf.2.2.2.2.1 i)
  have tb (i : ℕ) (hi : i < 4) : Blank t.val i :=
    RationalAccumulator.blank_of_eq (tfromb i (by omega)) (hbb i hi)
  have tfree (i : ℕ) (hi : 4 ≤ i) (hmid : i < 64 ∨ 68 < i)
      (h18 : i ≠ 18) (h40 : i ≠ 40) (h41 : i ≠ 41) (h42 : i ≠ 42) (h43 : i ≠ 43)
      (h44 : i ≠ 44) (h60 : i ≠ 60) (h61 : i ≠ 61) (h63 : i ≠ 63) (h72 : i ≠ 72) :
      t.val.tapes i = BitTape.blank :=
    (tkeep i hi hmid h72).trans (hafree i (by omega) (by omega) (by omega) (by omega)
      h18 h40 h41 h42 h43 h44 h60 h61 h63 (by omega))
  have tmem : t.val.memory = MemoryWord.writeBits (fun _ => false) 0 (Codec.messages I.decoder w) :=
    htf.memory.trans (hcf.2.2.1.trans (hbf.2.2.1.trans hamem))
  refine ⟨ca+(cb+((20*n.bits.length+24)+(21*n.bits.length+16))),t,
    ea.seq (eb.seq (ec.seq et)), by unfold setupPrice; omega, ?_⟩
  refine ⟨?_, ?_, ?_, ht72, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨⟨tb 0 (by decide), (RationalAccumulator.zero_word_iff_blank _ _).mpr
        (tb 1 (by decide)), tb 2 (by decide), tb 3 (by decide)⟩, ?_, ?_,
      RationalAccumulator.word_of_eq (tfromb 64 (by decide)) hbwidth,
      RationalAccumulator.word_of_eq (tfromb 66 (by decide)) hb66,
      RationalAccumulator.word_of_eq (tfromb 67 (by decide)) hb67⟩
    · intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      by_cases h65 : i = 65
      · subst i
        exact RationalAccumulator.blank_of_eq (tfromb 65 (by decide)) hb65
      · refine ⟨0, tfree i (by omega) (Or.inl (by omega)) (by omega) (by omega)
          (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega)⟩
    · intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      exact tfree i (by omega) (Or.inl (by omega)) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  · intro i hi hj
    apply (RationalAccumulator.zero_word_iff_blank _ _).mpr
    refine ⟨0, tfree i (by omega) (Or.inl (by omega)) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)⟩
  · rw [tmem]
    exact messages_represent I.decoder w _
  · exact tfree 73 (by decide) (Or.inr (by decide)) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · simpa only [hchead, List.length_append, Nat.cast_add] using hthead
  · rw [htf.output, hco, hbf.2.2.2.2.1, haoutput, List.append_nil]
  · exact htf.randomCursor.trans (hcf.2.2.2.1.trans (hbf.2.2.2.1.trans harandom))
  · refine ⟨(tkeep 40 (by decide) (Or.inl (by decide)) (by decide)).trans hameta.dimension,
      (tkeep 41 (by decide) (Or.inl (by decide)) (by decide)).trans hameta.integerBits,
      (tkeep 42 (by decide) (Or.inl (by decide)) (by decide)).trans hameta.fractionalBits,
      (tkeep 43 (by decide) (Or.inl (by decide)) (by decide)).trans hameta.sampleCount,
      (tkeep 44 (by decide) (Or.inl (by decide)) (by decide)).trans hameta.rowCount⟩

end Maxwell.Cost.DecoderParser
