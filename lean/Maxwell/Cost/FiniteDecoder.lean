import Maxwell.Cost.FiniteDecoder.Setup
import Maxwell.Cost.DecoderParser.EvaluatorBounds
import Maxwell.Cost.DecoderParser.Costs

namespace Maxwell.Cost.FiniteDecoder
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.DecoderParser
set_option maxRecDepth 4096

/-- One uniform deterministic finite program for every target dimension,
format, rational stencil, and fixed-width message bit pattern. -/
def code : Code := .seq setupCode (Counted.code 72 rowCode)

def program : BitRAM := code.compile

/-- The cap depends only on the stored decoder description, and is identical for every
message. Zero words are used solely to evaluate this width-based bound. -/
def costCap {ι : Type*} {n : ℕ} (D : Target.WeightedDecoder ι n) : ℕ := setupPrice D+
  ((n+1)*(13*n.bits.length+15)+
    ((rows D).map (rowPrice D (zeroMessages D) (decoderWidth D))).sum)

/-- The full public decoding contract follows from actual charged execution
of the parser, loader, two counted loops and rational output writer. -/
theorem executes_from {ι : Type*} {n : ℕ} (D : Target.WeightedDecoder ι n) (w : D.Messages)
    (preceding : List Bool) (randomTape : ℕ → Bool) (start : Store)
    (hh : start.val.inputHead=preceding.length)
    (hz : ∀ i, start.val.tapes i=BitTape.blank) :
    ∃ cost, ∃ t : Store, cost ≤ costCap D ∧
      Executes (preceding++(description D++Codec.messages D w)) randomTape code cost start t ∧
      (∃ emitted, Codec.RepresentsOutput (decoderWidth D+2) (D.decode w) emitted ∧
        t.val.output=emitted.reverse++start.val.output) ∧
      t.val.randomCursor=start.val.randomCursor := by
  obtain ⟨sc,s,es,hsc,hs⟩ := setup_from D w preceding randomTape start hh hz
  obtain ⟨rc,t,_,pairs,_,hrc,et,_,_,_,_,hpairs,hto,_,_,_,_,_,_,_,htf⟩ :=
    rows_steps D w (rows D) n.bits (preceding++beforeRows D++Codec.nat n)
      (Codec.messages D w) randomTape (fun _ => 0) (decoderWidth D)
      (by simp [Algebra.CoreShort]) (decoderWidth_spec D w)
      rfl rfl rfl rfl s hs.inputHead hs.ready hs.bank hs.messages hs.supportCounter hs.counter
      (by simp)
  have hi : (preceding++beforeRows D++Codec.nat n)++((rows D).flatMap rowWire++Codec.messages D w)=
      preceding++(description D++Codec.messages D w) := by rw [description_rows];simp [List.append_assoc]
  rw [hi] at et
  refine ⟨sc+rc,t,?_,es.seq et,?_,htf.randomCursor.trans hs.randomCursor⟩
  · have hp : ((rows D).map (rowPrice D w (decoderWidth D))).sum=
        ((rows D).map (rowPrice D (zeroMessages D) (decoderWidth D))).sum := by
      congr 1
      apply List.map_congr_left
      intro row _
      exact rowPrice_messages D w (zeroMessages D) _ row
    rw [rows_length,hp] at hrc
    dsimp [costCap]
    omega
  · refine ⟨Codec.nat n++pairs.flatMap Codec.RationalPair.encode,
      rows_represents D w _ pairs hpairs,?_⟩
    rw [hto,hs.output,List.reverse_append,List.append_assoc]

theorem executes {ι : Type*} {n : ℕ} (D : Target.WeightedDecoder ι n) (w : D.Messages) (randomTape : ℕ → Bool) :
    ∃ cost, ∃ t : Store, cost ≤ costCap D ∧
      Executes (description D++Codec.messages D w) randomTape code cost
        (Store.ofState BitRAMState.initial) t ∧
      Codec.RepresentsOutput (decoderWidth D+2) (D.decode w) t.val.output.reverse ∧
      t.val.randomCursor=0 := by
  obtain ⟨cost,t,hc,he,⟨emitted,ho,ht⟩,hr⟩ :=
    executes_from D w [] randomTape (Store.ofState BitRAMState.initial) rfl (fun _ => rfl)
  refine ⟨cost,t,hc,by simpa using he,?_,hr⟩
  simpa [ht,Store.ofState,BitRAMState.initial] using ho

/-- Capped execution uses the same input-only cap for every message pattern,
including values that fail any solver accuracy or physical good-event test. -/
theorem run {ι : Type*} {n : ℕ} (D : Target.WeightedDecoder ι n) (w : D.Messages) (randomTape : ℕ → Bool) :
    ∃ stop : BitRAMState,
      (runPriced (program.next (description D++Codec.messages D w) randomTape)
        (costCap D+1) BitRAMState.initial).finished=some stop ∧
      (runPriced (program.next (description D++Codec.messages D w) randomTape)
        (costCap D+1) BitRAMState.initial).instructions ≤ costCap D ∧
      Codec.RepresentsOutput (decoderWidth D+2) (D.decode w) stop.output.reverse ∧
      stop.randomCursor=0 := by
  obtain ⟨cost,t,hc,he,ho,hr⟩ := executes D w randomTape
  have hh := he.compiled_run (costCap D+1) (by omega)
  exact ⟨t.place code.size,hh.1,hh.2.symm ▸ hc,ho,hr⟩

#print axioms executes
#print axioms executes_from
#print axioms run

end Maxwell.Cost.FiniteDecoder
