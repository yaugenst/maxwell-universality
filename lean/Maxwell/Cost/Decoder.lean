import Maxwell.Cost.DecoderParser.Setup
import Maxwell.Cost.DecoderParser.EvaluatorBounds
import Maxwell.Cost.DecoderParser.Costs

namespace Maxwell.Cost.Decoder
open Structured DecoderParser
set_option maxRecDepth 4096

/-- One uniform deterministic finite program for every target dimension,
format, rational stencil, and fixed-width message bit pattern. -/
def code : Code := .seq setupCode (Counted.code 72 rowCode)

def program : BitRAM := code.compile

/-- The cap depends only on the stored target, and is identical for every
message. Zero words are used solely to evaluate this width-based bound. -/
def costCap {n : ℕ} (I : Target.Instance n) : ℕ := setupPrice I+
  ((n+1)*(13*n.bits.length+15)+
    ((rows I.decoder).map (rowPrice I.decoder (zeroMessages I.decoder) (decoderWidth I.decoder))).sum)

/-- The full public decoding contract follows from actual charged execution
of the parser, loader, two counted loops and rational output writer. -/
theorem executes {n : ℕ} (I : Target.Instance n) (w : I.decoder.Messages) (randomTape : ℕ → Bool) :
    ∃ cost, ∃ t : Store, cost ≤ costCap I ∧
      Executes (Codec.target I++Codec.messages I.decoder w) randomTape code cost
        (Store.ofState BitRAMState.initial) t ∧
      Codec.RepresentsOutput (decoderWidth I.decoder+2) (I.decoder.decode w) t.val.output.reverse ∧
      t.val.randomCursor=0 := by
  obtain ⟨sc,s,es,hsc,hs⟩ := setup_steps I w randomTape
  obtain ⟨rc,t,_,pairs,_,hrc,et,_,_,_,_,hpairs,hto,_,_,_,_,_,_,_,htf⟩ :=
    rows_steps I.decoder w (rows I.decoder) n.bits (beforeRows I++Codec.nat n)
      (Codec.messages I.decoder w) randomTape (fun _ => 0) (decoderWidth I.decoder)
      (by simp [Algebra.CoreShort]) (decoderWidth_spec I.decoder w)
      rfl rfl rfl rfl s hs.inputHead hs.ready hs.bank hs.messages hs.supportCounter hs.counter
      (by simp)
  have hi : (beforeRows I++Codec.nat n)++((rows I.decoder).flatMap rowWire++Codec.messages I.decoder w)=
      Codec.target I++Codec.messages I.decoder w := by rw [target_rows];simp [List.append_assoc]
  rw [hi] at et
  refine ⟨sc+rc,t,?_,es.seq et,?_,htf.randomCursor.trans hs.randomCursor⟩
  · have hp : ((rows I.decoder).map (rowPrice I.decoder w (decoderWidth I.decoder))).sum=
        ((rows I.decoder).map (rowPrice I.decoder (zeroMessages I.decoder) (decoderWidth I.decoder))).sum := by
      congr 1
      apply List.map_congr_left
      intro row _
      exact rowPrice_messages I.decoder w (zeroMessages I.decoder) _ row
    rw [rows_length,hp] at hrc
    dsimp [costCap]
    omega
  · have ho : t.val.output.reverse=Codec.nat n++pairs.flatMap Codec.RationalPair.encode := by
      rw [hto,hs.output,List.reverse_append,List.reverse_reverse,List.reverse_reverse]
    rw [ho]
    exact rows_represents I.decoder w _ pairs hpairs

/-- Capped execution uses the same input-only cap for every message pattern,
including values that fail any solver accuracy or physical good-event test. -/
theorem run {n : ℕ} (I : Target.Instance n) (w : I.decoder.Messages) (randomTape : ℕ → Bool) :
    ∃ stop : BitRAMState,
      (runPriced (program.next (Codec.target I++Codec.messages I.decoder w) randomTape)
        (costCap I+1) BitRAMState.initial).finished=some stop ∧
      (runPriced (program.next (Codec.target I++Codec.messages I.decoder w) randomTape)
        (costCap I+1) BitRAMState.initial).instructions ≤ costCap I ∧
      Codec.RepresentsOutput (decoderWidth I.decoder+2) (I.decoder.decode w) stop.output.reverse ∧
      stop.randomCursor=0 := by
  obtain ⟨cost,t,hc,he,ho,hr⟩ := executes I w randomTape
  have hh := he.compiled_run (costCap I+1) (by omega)
  exact ⟨t.place code.size,hh.1,hh.2.symm ▸ hc,ho,hr⟩

end Maxwell.Cost.Decoder
