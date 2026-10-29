import Maxwell.Cost.WordPenultimate
import Maxwell.Cost.TrimShifted

/-! Delete the high padding cell and zero the next-to-last cell of an
actual tape word. This is the physical child-label reduction operation. -/
namespace Maxwell.Cost.WordReduceHalf
open Structured

def block (workTape : ℕ) : BitRAM := ⟨[
  .tapeLeft workTape,.eraseTape workTape,.tapeLeft workTape,
  .literal 26 false,.writeTape workTape 26,.tapeRight workTape,.halt]⟩

def reducedTape (t : BitTape) : BitTape :=
  let a := ({t with head := t.head-1}).write none
  let b := ({a with head := a.head-1}).write (some false)
  {b with head := b.head+1}

def changed (workTape : ℕ) (s : BitRAMState) : BitRAMState :=
  {s with
    pc := 6
    tapes := Function.update s.tapes workTape (reducedTape (s.tapes workTape))
    registers := Function.update s.registers 26 false}

theorem block_steps (workTape : ℕ) (input : List Bool) (tape : ℕ → Bool)
    (s : BitRAMState) (hpc : s.pc = 0) :
    PricedSteps ((block workTape).next input tape) 6 s (changed workTape s) := by
  apply executeInstructions_sound (instructions := 6)
  simp [executeInstructions,block,BitRAM.next,hpc,BitRAMState.setTape,BitRAMState.setRegister,
    BitTape.write,changed,reducedTape]

theorem reducedTape_word (xs : List Bool) (b last : Bool) (origin : ℤ) :
    reducedTape (BitTape.shiftedEnd (xs++[b,last]) origin) =
      BitTape.shiftedEnd (xs++[false]) origin := by
  have he := congrArg BitTape.cells (BitTape.shifted_erase_last (xs++[b]) last origin)
  have hz := congrArg BitTape.cells (WordPenultimate.shifted_write_set (xs++[b]) origin xs.length false (by simp))
  have erase : Function.update (BitTape.shifted (xs++[b,last]) origin).cells
      (origin+xs.length+1) none = (BitTape.shifted (xs++[b]) origin).cells := by
    simpa [BitTape.shiftedBeforeEnd,BitTape.write,List.append_assoc,add_assoc,
      show origin+((xs.length:ℤ)+2)-1=origin+((xs.length:ℤ)+1) by omega] using he
  have zero : Function.update (BitTape.shifted (xs++[b]) origin).cells
      (origin+xs.length) (some false) = (BitTape.shifted (xs++[false]) origin).cells := by
    simpa [BitTape.write] using hz
  apply BitTape.ext
  · simp [reducedTape,BitTape.shiftedEnd,BitTape.write]
    omega
  · have result := (congrArg (fun f => Function.update f (origin+xs.length) (some false)) erase).trans zero
    simpa [reducedTape,BitTape.shiftedEnd,BitTape.write,add_assoc,
      show origin+((xs.length:ℤ)+2)-1=origin+xs.length+1 by omega,
      show origin+((xs.length:ℤ)+2)-1-1=origin+xs.length by omega,
      show origin+((xs.length:ℤ)+1)-1=origin+xs.length by omega] using result

theorem changed_frame (workTape : ℕ) (s : BitRAMState) :
    WordTransfer.Frame workTape workTape s (changed workTape s) := by
  refine ⟨rfl,rfl,rfl,rfl,rfl,?_,?_⟩
  · intro i hi _; simp [changed,hi]
  · intro i _ _ h26 _; simp [changed,h26]

def code (workTape : ℕ) : Code := .seq (.call (ScanForward.program workTape))
  (.seq (.call (block workTape)) (.call (Rewind.program workTape)))

/-- Both scans and the six-instruction mutation are executed and charged. -/
theorem executes (workTape : ℕ) (input : List Bool) (tape : ℕ → Bool)
    (xs : List Bool) (b last : Bool) (origin : ℤ) (s : Store)
    (hw : s.val.tapes workTape = BitTape.shifted (xs++[b,last]) origin) :
    ∃ t, Executes input tape (code workTape) (9*xs.length+31) s t ∧
      t.val.tapes workTape = BitTape.shifted (xs++[false]) origin ∧
      WordTransfer.Frame workTape workTape s.val t.val := by
  obtain ⟨ef,fw,ff⟩ := ScanForward.shifted_steps workTape origin input tape (xs++[b,last]) s.val s.property hw
  let f := Store.ofState (ScanForward.finish workTape (xs++[b,last]).length s.val)
  have ef' : Executes input tape (.call (ScanForward.program workTape))
      (5*(xs++[b,last]).length+4) s f :=
    .call _ s _ _ ef (by simp [ScanForward.program,ScanForward.finish])
  have fword : f.val.tapes workTape = BitTape.shiftedEnd (xs++[b,last]) origin := fw
  let c := Store.ofState (changed workTape f.val)
  have eb : Executes input tape (.call (block workTape)) 7 f c :=
    .call _ f _ _ (block_steps workTape input tape f.val f.property) (by simp [block,changed])
  have cw : c.val.tapes workTape = BitTape.shiftedEnd (xs++[false]) origin := by
    simpa only [c,Store.ofState,changed,Function.update_self,fword] using reducedTape_word xs b last origin
  obtain ⟨er,hr⟩ := WordTransfer.rewind_shifted workTape origin input tape (xs++[false]) c.val c.property cw
  let t := Store.ofState (Rewind.finishAt workTape origin c.val)
  have er' : Executes input tape (.call (Rewind.program workTape))
      (4*(xs++[false]).length+6) c t :=
    .call _ c _ _ er (by simp [Rewind.program,Rewind.finishAt])
  refine ⟨t,?_,hr,?_⟩
  · convert ef'.seq (eb.seq er') using 1 <;> first | rfl | simp; omega
  · exact (WordTransfer.frame_of_copy ff).trans ((changed_frame workTape f.val).trans
      (WordTransfer.frame_rewind workTape workTape workTape (Or.inl rfl) origin c.val))

end Maxwell.Cost.WordReduceHalf
