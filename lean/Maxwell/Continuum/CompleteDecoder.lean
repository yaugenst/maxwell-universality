import Maxwell.Continuum.ContinuumDescriptionSchema
import Maxwell.Cost.FiniteDecoder

/-! One uniform decoder for the tagged vacuum and computed wire formats.
The computed branch actually parses and discards the entire physical record
before executing the same weighted decoder on the following message stream. -/

namespace Maxwell.Continuum.CompleteDecoder
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.DecoderParser
set_option maxRecDepth 4096

def readTag : BitRAM := ⟨[.readSequential 23,.inputRight,.halt]⟩

def afterTag (tag : Bool) : Store := Store.ofState
  {BitRAMState.initial with inputHead:=1,registers:=Function.update (fun _ => false) 23 tag}

theorem readTag_executes (tag : Bool) (suffix : List Bool) (randomTape : ℕ→Bool) :
    Executes (tag::suffix) randomTape (.call readTag) 3
      (Store.ofState BitRAMState.initial) (afterTag tag) := by
  apply Executes.call readTag _
    {BitRAMState.initial with pc:=2,inputHead:=1,registers:=Function.update (fun _ => false) 23 tag} 2
  · apply executeInstructions_sound (instructions:=2)
    simp [executeInstructions,readTag,BitRAM.next,Store.ofState,BitRAMState.initial,
      BitRAMState.setRegister,inputBit]
  · rfl

def computedCode : Code := .seq (skip DescriptionSchema.shape) Cost.FiniteDecoder.code
def code : Code := .seq (.call readTag) (.branch 23 computedCode Cost.FiniteDecoder.code)
def program : BitRAM := code.compile

def computedCost {ι : Type*} {n : ℕ} (payload : Payload DescriptionSchema.shape)
    (D : Target.WeightedDecoder ι n) : ℕ :=
  4+skipPrice DescriptionSchema.shape payload+Cost.FiniteDecoder.costCap D

def vacuumCost {ι : Type*} {n : ℕ} (D : Target.WeightedDecoder ι n) : ℕ :=
  4+Cost.FiniteDecoder.costCap D

theorem computed_executes {ι : Type*} {n : ℕ}
    (payload : Payload DescriptionSchema.shape) (D : Target.WeightedDecoder ι n)
    (w : D.Messages) (randomTape : ℕ→Bool) :
    ∃ cost t, cost≤computedCost payload D ∧
      Executes (true::(wire DescriptionSchema.shape payload++
        (Cost.FiniteDecoder.description D++Codec.messages D w))) randomTape code cost
        (Store.ofState BitRAMState.initial) t ∧
      Codec.RepresentsOutput (decoderWidth D+2) (D.decode w) t.val.output.reverse ∧
      t.val.randomCursor=0 := by
  obtain ⟨a,u,eu,ha,huh,huf⟩ := skip_correct DescriptionSchema.shape (by decide) payload
    [true] (Cost.FiniteDecoder.description D++Codec.messages D w) randomTape (afterTag true) rfl
      (by simp [Ready,afterTag,Store.ofState,BitRAMState.initial]) rfl
  obtain ⟨b,t,hb,et,⟨emitted,he,hto⟩,htr⟩ :=
    Cost.FiniteDecoder.executes_from D w ([true]++wire DescriptionSchema.shape payload)
      randomTape u huh (fun i => by
        simpa [afterTag,Store.ofState,BitRAMState.initial] using (huf.tapes i (by simp)))
  simp only [List.cons_append,List.nil_append] at eu et
  refine ⟨3+(1+(a+b)),t,by dsimp [computedCost];omega,
    (readTag_executes true _ randomTape).seq (Executes.yes (by simp [afterTag,Store.ofState])
      (eu.seq et)),?_,htr.trans huf.randomCursor⟩
  simpa [hto,huf.output,afterTag,Store.ofState,BitRAMState.initial] using he

theorem vacuum_executes {ι : Type*} {n : ℕ} (D : Target.WeightedDecoder ι n)
    (w : D.Messages) (randomTape : ℕ→Bool) :
    ∃ cost t, cost≤vacuumCost D ∧
      Executes (false::(Cost.FiniteDecoder.description D++Codec.messages D w)) randomTape code cost
        (Store.ofState BitRAMState.initial) t ∧
      Codec.RepresentsOutput (decoderWidth D+2) (D.decode w) t.val.output.reverse ∧
      t.val.randomCursor=0 := by
  obtain ⟨cost,t,hc,he,⟨emitted,ho,ht⟩,hr⟩ :=
    Cost.FiniteDecoder.executes_from D w [false] randomTape (afterTag false) rfl (fun _ => rfl)
  simp only [List.singleton_append] at he
  refine ⟨3+(1+cost),t,by dsimp [vacuumCost];omega,
    (readTag_executes false _ randomTape).seq (Executes.no (by simp [afterTag,Store.ofState]) he),?_,hr⟩
  simpa [ht,afterTag,Store.ofState,BitRAMState.initial] using ho

theorem computed_run {ι : Type*} {n : ℕ}
    (payload : Payload DescriptionSchema.shape) (D : Target.WeightedDecoder ι n)
    (w : D.Messages) (randomTape : ℕ→Bool) :
    ∃ stop,
      (program.run (true::(wire DescriptionSchema.shape payload++
        (Cost.FiniteDecoder.description D++Codec.messages D w))) randomTape (computedCost payload D+1)).finished=
        some stop ∧
      Codec.RepresentsOutput (decoderWidth D+2) (D.decode w) stop.output.reverse ∧
      stop.randomCursor=0 := by
  obtain ⟨cost,t,hc,he,ho,hr⟩ := computed_executes payload D w randomTape
  exact ⟨t.place code.size,(he.compiled_run (computedCost payload D+1) (by omega)).1,ho,hr⟩

theorem vacuum_run {ι : Type*} {n : ℕ} (D : Target.WeightedDecoder ι n)
    (w : D.Messages) (randomTape : ℕ→Bool) :
    ∃ stop,
      (program.run (false::(Cost.FiniteDecoder.description D++Codec.messages D w))
        randomTape (vacuumCost D+1)).finished=some stop ∧
      Codec.RepresentsOutput (decoderWidth D+2) (D.decode w) stop.output.reverse ∧
      stop.randomCursor=0 := by
  obtain ⟨cost,t,hc,he,ho,hr⟩ := vacuum_executes D w randomTape
  exact ⟨t.place code.size,(he.compiled_run (vacuumCost D+1) (by omega)).1,ho,hr⟩

#print axioms computed_run
#print axioms vacuum_run

end Maxwell.Continuum.CompleteDecoder
