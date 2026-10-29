import Maxwell.Cost.RealPrivate.AccessSemantics

namespace Maxwell.Cost.RealPrivate
open RealSimulation.Control

noncomputable def wordOutput (s : Store) (origin count : ℕ) (value : ℝ) : Store :=
  (putWord s (slot origin 1 count) value).put realOutputLength (count+1)

def indexOutput (s : Store) (origin count value : ℕ) : Store :=
  (s.put (slot origin 1 count) value).put indexOutputLength (count+1)

theorem Represents.wordOutput {origin : ℕ} {source : RAMState} {written : List ℕ}
    {s : Store} (h : Represents origin source written s.val) (value : ℝ) :
    Represents origin {source with output:=value::source.output} written
      (RealPrivate.wordOutput s origin source.output.length value).val := by
  have hn (bank a j : ℕ) (hj : j<256) : slot origin bank a≠j := slot_ne_small h.high bank a j hj
  have hz (a : ℕ) : slot origin 0 a≠slot origin 1 source.output.length :=
    slot_different (by decide) (by decide) (by decide)
  refine ⟨h.high,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,h.random_cursor⟩
  · simpa [RealPrivate.wordOutput,putWord,originRegister,realOutputLength] using h.origin_word
  · simpa [RealPrivate.wordOutput,putWord,zeroRegister,realOutputLength] using h.zero
  · simpa [RealPrivate.wordOutput,putWord,oneRegister,realOutputLength] using h.one
  · simpa [RealPrivate.wordOutput,putWord,sourcePC,realOutputLength] using h.pc
  · intro a
    simpa [RealPrivate.wordOutput,putWord,Store.put,hz] using h.words a
  · intro a
    simpa [RealPrivate.wordOutput,putWord,hn,realOutputLength] using h.indices a
  · simp [RealPrivate.wordOutput]
  · simpa [RealPrivate.wordOutput,putWord,indexOutputLength,realOutputLength] using h.index_output_length
  · intro j hj
    simp only [List.length_cons] at hj
    by_cases he : j=source.output.length
    · subst j
      simp [RealPrivate.wordOutput,putWord,Store.put,List.reverse_cons]
    · have hj' : j<source.output.length := by omega
      simpa [RealPrivate.wordOutput,putWord,Store.put,he,List.reverse_cons,
        List.getElem?_append_left (show j<source.output.reverse.length by simpa using hj')]
        using h.real_output j hj'
  · intro j hj
    simpa [RealPrivate.wordOutput,putWord,hn,realOutputLength] using h.index_output j hj
  · simpa [RealPrivate.wordOutput,putWord,logLength,realOutputLength] using h.log_length
  · intro j hj
    simpa [RealPrivate.wordOutput,putWord,hn,realOutputLength] using h.log_cells j hj

theorem Represents.indexOutput {origin : ℕ} {source : RAMState} {written : List ℕ}
    {s : Store} (h : Represents origin source written s.val) (value : ℕ) :
    Represents origin {source with indexOutput:=value::source.indexOutput} written
      (RealPrivate.indexOutput s origin source.indexOutput.length value).val := by
  have hn (bank a j : ℕ) (hj : j<256) : slot origin bank a≠j := slot_ne_small h.high bank a j hj
  have hnr (j : ℕ) (hj : j<256) : j≠slot origin 1 source.indexOutput.length :=
    (hn 1 source.indexOutput.length j hj).symm
  have hz (a : ℕ) : slot origin 0 a≠slot origin 1 source.indexOutput.length :=
    slot_different (by decide) (by decide) (by decide)
  have hl (a : ℕ) : slot origin 2 a≠slot origin 1 source.indexOutput.length :=
    slot_different (by decide) (by decide) (by decide)
  refine ⟨h.high,?_,?_,?_,?_,h.words,?_,?_,?_,h.real_output,?_,?_,?_,h.random_cursor⟩
  · simpa [RealPrivate.indexOutput,hnr,originRegister,indexOutputLength] using h.origin_word
  · simpa [RealPrivate.indexOutput,hnr,zeroRegister,indexOutputLength] using h.zero
  · simpa [RealPrivate.indexOutput,hnr,oneRegister,indexOutputLength] using h.one
  · simpa [RealPrivate.indexOutput,hnr,sourcePC,indexOutputLength] using h.pc
  · intro a
    simpa [RealPrivate.indexOutput,hz,hn,indexOutputLength] using h.indices a
  · simpa [RealPrivate.indexOutput,hnr,realOutputLength,indexOutputLength] using h.real_output_length
  · simp [RealPrivate.indexOutput]
  · intro j hj
    simp only [List.length_cons] at hj
    by_cases he : j=source.indexOutput.length
    · subst j
      simp [RealPrivate.indexOutput,hn,indexOutputLength,List.reverse_cons]
    · have hj' : j<source.indexOutput.length := by omega
      simpa [RealPrivate.indexOutput,hn,indexOutputLength,he,List.reverse_cons,
        List.getElem?_append_left (show j<source.indexOutput.reverse.length by simpa using hj')]
        using h.index_output j hj'
  · simpa [RealPrivate.indexOutput,hnr,logLength,indexOutputLength] using h.log_length
  · intro j hj
    simpa [RealPrivate.indexOutput,hl,hn,indexOutputLength] using h.log_cells j hj

theorem output_instruction (externalInput : RAMInput) (tape : ℕ→Bool)
    {L : Layout} {origin : ℕ} {source : RAMState} {written : List ℕ}
    (s : Store) (h : Represents origin source written s.val) (src : ℕ) :
    ∃ t, Executes externalInput tape (instruction L (.output src)) 25 s t ∧
      Represents origin {source with pc:=source.pc+1,output:=source.words src::source.output} written t.val ∧
      CallerFrame origin s.val t.val := by
  have hg := getWord_correct externalInput tape s h src 0 (by decide)
  let a := worded s src 0
  let address := slot origin 1 source.output.length
  let b := a.put pointerRegister address
  let c := putWord b address (source.words src)
  let d := c.put realOutputLength (source.output.length+1)
  have ha : Represents origin source written a.val := hg.2.1
  have hb : Represents origin source written b.val := hg.2.1.put_scratch pointerRegister address
    (by simp [ProtectedIndex,pointerRegister,zeroRegister,oneRegister])
  have ep : Executes externalInput tape (bankPointer 1 realOutputLength) 13 a b := by
    simpa only [ha.origin_word,ha.real_output_length] using
      bankPointer_executes externalInput tape a 1 realOutputLength (by decide)
  have hv : b.val.words 0=source.words src := hg.2.2.1
  have es : Executes externalInput tape (realStore pointerRegister 0) 2 b c := by
    simpa only [show b.val.indices pointerRegister=address by simp [b],hv] using
      realStore_executes externalInput tape b pointerRegister 0
  have hl : c.val.indices realOutputLength=source.output.length := hb.real_output_length
  have ho : c.val.indices oneRegister=1 := hb.one
  have el : Executes externalInput tape (add realOutputLength realOutputLength oneRegister) 2 c d := by
    simpa only [hl,ho] using add_executes externalInput tape c realOutputLength realOutputLength oneRegister
  have hd : Represents origin {source with output:=source.words src::source.output} written d.val :=
    hb.wordOutput (source.words src)
  have pc := incrementPC_correct externalInput tape d hd
  refine ⟨_,hg.1.seq (ep.seq (es.seq (el.seq pc.1))),pc.2.1,?_⟩
  exact hg.2.2.2.trans
    ((callerFrame_put a origin pointerRegister address (Or.inl (by decide))).trans
      ((callerFrame_word b origin address (source.words src) (Or.inr (slot_ge_origin _ _ _))).trans
        ((callerFrame_put c origin realOutputLength _ (Or.inr (Or.inl (by decide)))).trans pc.2.2)))

theorem outputIndex_instruction (externalInput : RAMInput) (tape : ℕ→Bool)
    {L : Layout} {origin : ℕ} {source : RAMState} {written : List ℕ}
    (s : Store) (h : Represents origin source written s.val) (src : ℕ) :
    ∃ t, Executes externalInput tape (instruction L (.outputIndex src)) 25 s t ∧
      Represents origin {source with pc:=source.pc+1,indexOutput:=source.indices src::source.indexOutput} written t.val ∧
      CallerFrame origin s.val t.val := by
  have hg := getIndex_correct externalInput tape s h src valueRegister (by decide)
  let a := indexed s src valueRegister
  let address := slot origin 1 source.indexOutput.length
  let b := a.put pointerRegister address
  let c := b.put address (source.indices src)
  let d := c.put indexOutputLength (source.indexOutput.length+1)
  have ha : Represents origin source written a.val := hg.2.1
  have hb : Represents origin source written b.val := hg.2.1.put_scratch pointerRegister address
    (by simp [ProtectedIndex,pointerRegister,zeroRegister,oneRegister])
  have ep : Executes externalInput tape (bankPointer 1 indexOutputLength) 13 a b := by
    simpa only [ha.origin_word,ha.index_output_length] using
      bankPointer_executes externalInput tape a 1 indexOutputLength (by decide)
  have hv : b.val.indices valueRegister=source.indices src := by
    have av : a.val.indices valueRegister=source.indices src := hg.2.2.1
    simpa [b,valueRegister,pointerRegister] using av
  have es : Executes externalInput tape (save pointerRegister valueRegister) 2 b c := by
    simpa only [show b.val.indices pointerRegister=address by simp [b],hv] using
      save_executes externalInput tape b pointerRegister valueRegister
  have hn (j : ℕ) (hj : j<256) : j≠address :=
    (slot_ne_small h.high 1 source.indexOutput.length j hj).symm
  have hl : c.val.indices indexOutputLength=source.indexOutput.length := by
    simpa [c,hn indexOutputLength (by decide)] using hb.index_output_length
  have ho : c.val.indices oneRegister=1 := by
    simpa [c,hn oneRegister (by decide)] using hb.one
  have el : Executes externalInput tape (add indexOutputLength indexOutputLength oneRegister) 2 c d := by
    simpa only [hl,ho] using add_executes externalInput tape c indexOutputLength indexOutputLength oneRegister
  have hd : Represents origin {source with indexOutput:=source.indices src::source.indexOutput} written d.val :=
    hb.indexOutput (source.indices src)
  have pc := incrementPC_correct externalInput tape d hd
  refine ⟨_,hg.1.seq (ep.seq (es.seq (el.seq pc.1))),pc.2.1,?_⟩
  exact hg.2.2.2.trans
    ((callerFrame_put a origin pointerRegister address (Or.inl (by decide))).trans
      ((callerFrame_put b origin address (source.indices src) (Or.inr (Or.inr (slot_ge_origin _ _ _)))).trans
        ((callerFrame_put c origin indexOutputLength _ (Or.inr (Or.inl (by decide)))).trans pc.2.2)))

end Maxwell.Cost.RealPrivate
