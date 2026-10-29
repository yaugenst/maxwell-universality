import Maxwell.Cost.DecoderParser.SecondPass
import Maxwell.Cost.DecoderParser.Replay
import Maxwell.Cost.RationalAccumulator.Bank

namespace Maxwell.Cost.DecoderParser
open Structured

def prepareCode : Code := .seq retainedTargetCode (.seq Replay.loadCode secondPassPrefix)

def preparePrice {n : ℕ} (I : Target.Instance n) : ℕ := retainedTargetPrice I +
  (Replay.loadCostBound I.decoder.format.integerBits I.decoder.format.fractionalBits
    I.decoder.sampleCount (Codec.target I).length +
    (11*(Codec.target I).length+10+price beforeRowsShape (beforeRowsPayload I)))

/-- The actual decoder front end: parse the physical target, load every
fixed-width message into indexed memory, rewind once, and reach the first
weighted row. All counts come from the encoded metadata. -/
theorem prepare_steps {n : ℕ} (I : Target.Instance n) (w : I.decoder.Messages)
    (randomTape : ℕ → Bool) :
    ∃ (cost : ℕ) (t : Store),
      Executes (Codec.target I ++ Codec.messages I.decoder w) randomTape prepareCode cost
        (Store.ofState BitRAMState.initial) t ∧ cost ≤ preparePrice I ∧
      t.val.inputHead = (beforeRows I).length ∧ DecoderMetadata I t.val ∧ Ready 0 t.val ∧
      t.val.memory = MemoryWord.writeBits (fun _ => false) 0 (Codec.messages I.decoder w) ∧
      t.val.randomCursor = 0 ∧ t.val.output = [] ∧
      (∀ i ∈ ({0,1,2,3,64} : Finset ℕ), RationalAccumulator.Blank t.val i) ∧
      (∀ i, i ≠ 0 → i ≠ 1 → i ≠ 2 → i ≠ 3 → i ≠ 18 →
        i ≠ 40 → i ≠ 41 → i ≠ 42 → i ≠ 43 → i ≠ 44 →
        i ≠ 60 → i ≠ 61 → i ≠ 63 → i ≠ 64 → t.val.tapes i = BitTape.blank) := by
  obtain ⟨a,s,es,has,hsh,hsl,hsm,hsr,hsf⟩ := retainedTarget_steps I
    (Codec.messages I.decoder w) randomTape
  have hb (i : ℕ) (hi : i ∈ MetadataProduct.work) : s.val.tapes i = BitTape.blank := by
    apply hsf.tapes i
    simp only [MetadataProduct.work,Finset.mem_insert,Finset.mem_singleton] at hi ⊢
    omega
  have h61 : s.val.tapes 61 = BitTape.blank := hsf.tapes 61 (by decide)
  have h63 : s.val.tapes 63 = BitTape.blank := hsf.tapes 63 (by decide)
  obtain ⟨b,u,eu,hbu,huh,hu18,hum,hur,huo,hut,hus⟩ := Replay.load_messages_steps I.decoder w
    (Codec.target I) [] randomTape s hsh hb h61 h63
    (by simpa [BitTape.shiftedEnd,BitTape.shifted,BitTape.atEnd,BitTape.ofList] using hsl)
    hsm.integerBits hsm.fractionalBits hsm.sampleCount
  simp only [List.append_nil] at eu
  have hready : Ready 0 u.val := by
    refine ⟨(hut 10 (by decide) (by decide) (by decide) (by decide)).trans hsr.1,
      (hut 11 (by decide) (by decide) (by decide) (by decide)).trans hsr.2.1,
      (hut 45 (by decide) (by decide) (by decide) (by decide)).trans hsr.2.2.1,?_⟩
    intro i hi hi60
    exact (hut i (by simp [MetadataProduct.work];omega) (by omega) (by omega) (by omega)).trans
      (hsr.2.2.2 i hi hi60)
  obtain ⟨c,t,et,hct,hth,_,htr,htf⟩ := secondPassPrefix_steps I
    (Codec.messages I.decoder w) randomTape u huh hready hu18
  have hmeta (i : ℕ) (h40 : 40 ≤ i) (h44 : i ≤ 44) : t.val.tapes i = s.val.tapes i :=
    (htf.tapes i (by simp;omega)).trans
      (hut i (by simp [MetadataProduct.work];omega) (by omega) (by omega) (by omega))
  refine ⟨a+(b+c),t,es.seq (eu.seq et),by dsimp [preparePrice];omega,hth,?_,htr,?_,?_,?_,?_,?_⟩
  · exact ⟨(hmeta 40 (by decide) (by decide)).trans hsm.dimension,
      (hmeta 41 (by decide) (by decide)).trans hsm.integerBits,
      (hmeta 42 (by decide) (by decide)).trans hsm.fractionalBits,
      (hmeta 43 (by decide) (by decide)).trans hsm.sampleCount,
      (hmeta 44 (by decide) (by decide)).trans hsm.rowCount⟩
  · exact htf.memory.trans (hum.trans (congrArg (fun f => MemoryWord.writeBits f 0
      (Codec.messages I.decoder w)) hsf.memory))
  · exact htf.randomCursor.trans (hur.trans hsf.randomCursor)
  · exact htf.output.trans (huo.trans hsf.output)
  · intro i hi
    obtain ⟨origin,ho⟩ := hus i hi
    refine ⟨origin,(htf.tapes i ?_).trans ho⟩
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi ⊢
    omega
  · intro i h0 h1 h2 h3 h18 h40 h41 h42 h43 h44 h60 h61 h63 h64
    exact (htf.tapes i (by simpa using h18)).trans
      ((hut i (by simp [MetadataProduct.work,h0,h1,h2,h3,h60,h64]) h18 h61 h63).trans
        (hsf.tapes i (by simp [h18,h40,h41,h42,h43,h44])))

end Maxwell.Cost.DecoderParser
