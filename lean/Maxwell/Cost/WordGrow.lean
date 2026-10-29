import Maxwell.Cost.WordPenultimate

namespace Maxwell.Cost.WordGrow
open Structured

def block (workTape : ℕ) (bit : Bool) : BitRAM := ⟨[
  .literal 26 bit,.writeTape workTape 26,.tapeRight workTape,.halt]⟩

def changed (workTape : ℕ) (bit : Bool) (s : BitRAMState) : BitRAMState :=
  {s with
    pc := 3
    registers := Function.update s.registers 26 bit
    tapes := Function.update s.tapes workTape
      {head := (s.tapes workTape).head+1
       cells := ((s.tapes workTape).write (some bit)).cells}}

theorem block_steps (workTape : ℕ) (bit : Bool) (input : List Bool) (tape : ℕ → Bool)
    (s : BitRAMState) (hpc : s.pc=0) :
    PricedSteps ((block workTape bit).next input tape) 3 s (changed workTape bit s) := by
  apply executeInstructions_sound (instructions:=3)
  simp [executeInstructions,block,BitRAM.next,hpc,BitRAMState.setRegister,BitRAMState.setTape,changed,BitTape.write]

theorem changed_word (workTape : ℕ) (bit : Bool) (bits : List Bool) (origin : ℤ)
    (s : BitRAMState) (hw : s.tapes workTape=BitTape.shiftedEnd bits origin) :
    (changed workTape bit s).tapes workTape=BitTape.shiftedEnd (bits++[bit]) origin := by
  simpa only [changed,Function.update_self,hw] using BitTape.shiftedEnd_append_write bits origin bit

theorem changed_frame (workTape : ℕ) (bit : Bool) (s : BitRAMState) :
    WordTransfer.Frame workTape workTape s (changed workTape bit s) := by
  refine ⟨rfl,rfl,rfl,rfl,rfl,?_,?_⟩
  · intro i hi _; simp [changed,hi]
  · intro i _ _ h26 _; simp [changed,h26]

def code (workTape : ℕ) (bit : Bool) : Code :=
  .seq (.call (ScanForward.program workTape))
    (.seq (.call (block workTape bit)) (.call (Rewind.program workTape)))

/-- Append one literal bit, with both complete scans and the write charged. -/
theorem executes (workTape : ℕ) (bit : Bool) (input : List Bool) (tape : ℕ → Bool)
    (bits : List Bool) (origin : ℤ) (s : Store)
    (hw : s.val.tapes workTape=BitTape.shifted bits origin) :
    ∃ t, Executes input tape (code workTape bit) (9*bits.length+18) s t ∧
      t.val.tapes workTape=BitTape.shifted (bits++[bit]) origin ∧
      WordTransfer.Frame workTape workTape s.val t.val := by
  obtain ⟨ef,fw,ff⟩ := ScanForward.shifted_steps workTape origin input tape bits s.val s.property hw
  let f := Store.ofState (ScanForward.finish workTape bits.length s.val)
  have ef' : Executes input tape (.call (ScanForward.program workTape)) (5*bits.length+4) s f :=
    .call _ s _ _ ef (by simp [ScanForward.program,ScanForward.finish])
  have eb := block_steps workTape bit input tape f.val f.property
  let c := Store.ofState (changed workTape bit f.val)
  have eb' : Executes input tape (.call (block workTape bit)) 4 f c :=
    .call _ f _ _ eb (by simp [block,changed])
  have cw : c.val.tapes workTape=BitTape.shiftedEnd (bits++[bit]) origin := changed_word _ _ _ _ _ fw
  obtain ⟨er,rw⟩ := WordTransfer.rewind_shifted workTape origin input tape (bits++[bit]) c.val c.property cw
  let t := Store.ofState (Rewind.finishAt workTape origin c.val)
  have er' : Executes input tape (.call (Rewind.program workTape)) (4*(bits++[bit]).length+6) c t :=
    .call _ c _ _ er (by simp [Rewind.program,Rewind.finishAt])
  refine ⟨t,?_,rw,(WordTransfer.frame_of_copy ff).trans
    ((changed_frame workTape bit f.val).trans (WordTransfer.frame_rewind workTape workTape workTape (Or.inl rfl) origin c.val))⟩
  convert ef'.seq (eb'.seq er') using 1 <;> first | rfl | simp; omega

end Maxwell.Cost.WordGrow
