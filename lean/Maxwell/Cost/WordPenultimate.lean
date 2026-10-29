import Maxwell.Cost.ScanForward
import Maxwell.Cost.WordTransfer
import Maxwell.Cost.Structured.Correctness

/-! A literal tape operation flips the next-to-last stored bit. Its intended
use is the source pairing on padded binary token labels. -/
namespace Maxwell.Cost.WordPenultimate
open Structured

def block (workTape : ℕ) : BitRAM := ⟨[
  .tapeLeft workTape,.tapeLeft workTape,.readTape workTape 26 27,
  .bitNot 26 26,.writeTape workTape 26,.tapeRight workTape,.tapeRight workTape,.halt]⟩

def changed (workTape : ℕ) (b : Bool) (s : BitRAMState) : BitRAMState :=
  {s with
    pc := 7
    tapes := Function.update s.tapes workTape
      {s.tapes workTape with cells := Function.update (s.tapes workTape).cells ((s.tapes workTape).head-2) (some (!b))}
    registers := Function.update (Function.update s.registers 26 (!b)) 27 true}

theorem block_steps (workTape : ℕ) (input : List Bool) (tape : ℕ → Bool)
    (s : BitRAMState) (b : Bool) (hpc : s.pc=0)
    (hr : (s.tapes workTape).cells ((s.tapes workTape).head-2)=some b) :
    PricedSteps ((block workTape).next input tape) 8 s (changed workTape b s) := by
  apply executeInstructions_sound (instructions := 7)
  simp [executeInstructions,block,BitRAM.next,hpc,BitRAMState.setTape,BitRAMState.setRegister,
    BitTape.read,BitTape.write,changed,show (s.tapes workTape).head-1-1=(s.tapes workTape).head-2 by omega,hr]
  constructor
  · funext i
    by_cases h26 : i=26 <;> by_cases h27 : i=27 <;> simp [h26,h27]
  · congr 2
    omega

theorem shifted_write_set (word : List Bool) (origin : ℤ) (i : ℕ) (b : Bool)
    (hi : i < word.length) :
    ({BitTape.shifted word origin with head := origin+i}).write (some b) =
      {BitTape.shifted (word.set i b) origin with head := origin+i} := by
  apply BitTape.ext
  · rfl
  · funext p
    simp only [BitTape.write,BitTape.shifted]
    by_cases hp : p=origin+(i:ℤ)
    · subst p; simp [hi]
    · rw [Function.update_of_ne hp]
      by_cases hpoint : origin ≤ p
      · have hne : i ≠ (p-origin).toNat := by omega
        simp [hpoint,List.getElem?_set_ne hne]
      · simp [hpoint]

theorem changed_word (workTape : ℕ) (preceding : List Bool) (b last : Bool) (origin : ℤ)
    (s : BitRAMState) (hw : s.tapes workTape=BitTape.shiftedEnd (preceding++[b,last]) origin) :
    (changed workTape b s).tapes workTape=BitTape.shiftedEnd (preceding++[!b,last]) origin := by
  have hc := congrArg BitTape.cells (shifted_write_set (preceding++[b,last]) origin preceding.length (!b) (by simp))
  apply BitTape.ext
  · simp [changed,hw,BitTape.shiftedEnd,BitTape.shifted]
  · simpa [changed,hw,BitTape.shiftedEnd,BitTape.write,BitTape.shifted,add_assoc,
      show origin+((preceding.length:ℤ)+2)-2=origin+preceding.length by omega] using hc

theorem changed_frame (workTape : ℕ) (b : Bool) (s : BitRAMState) :
    WordTransfer.Frame workTape workTape s (changed workTape b s) := by
  refine ⟨rfl,rfl,rfl,rfl,rfl,?_,?_⟩
  · intro i hi _; simp [changed,hi]
  · intro i _ _ h26 h27; simp [changed,h26,h27]

def code (workTape : ℕ) : Code := .seq (.call (ScanForward.program workTape))
  (.seq (.call (block workTape)) (.call (Rewind.program workTape)))

/-- The scan, bit flip, and rewind are all executed and charged. -/
theorem executes (workTape : ℕ) (input : List Bool) (tape : ℕ → Bool)
    (preceding : List Bool) (b last : Bool) (origin : ℤ) (s : Store)
    (hw : s.val.tapes workTape=BitTape.shifted (preceding++[b,last]) origin) :
    ∃ t, Executes input tape (code workTape) (9*(preceding.length+2)+19) s t ∧
      t.val.tapes workTape=BitTape.shifted (preceding++[!b,last]) origin ∧
      WordTransfer.Frame workTape workTape s.val t.val := by
  obtain ⟨ef,fw,ff⟩ := ScanForward.shifted_steps workTape origin input tape (preceding++[b,last]) s.val s.property hw
  let f := Store.ofState (ScanForward.finish workTape (preceding++[b,last]).length s.val)
  have ef' : Executes input tape (.call (ScanForward.program workTape))
      (5*(preceding++[b,last]).length+4) s f :=
    .call _ s _ _ ef (by simp [ScanForward.program,ScanForward.finish])
  have fword : f.val.tapes workTape=BitTape.shiftedEnd (preceding++[b,last]) origin := fw
  have fr : (f.val.tapes workTape).cells ((f.val.tapes workTape).head-2)=some b := by
    simp [fword,BitTape.shiftedEnd,BitTape.shifted,List.getElem?_append,
      show origin+((preceding.length:ℤ)+2)-2=origin+preceding.length by omega]
  have eb := block_steps workTape input tape f.val b f.property fr
  let c := Store.ofState (changed workTape b f.val)
  have eb' : Executes input tape (.call (block workTape)) 9 f c :=
    .call _ f _ _ eb (by simp [block,changed])
  have cw : c.val.tapes workTape=BitTape.shiftedEnd (preceding++[!b,last]) origin := changed_word _ _ _ _ _ _ fword
  obtain ⟨er,rw⟩ := WordTransfer.rewind_shifted workTape origin input tape (preceding++[!b,last]) c.val c.property cw
  let t := Store.ofState (Rewind.finishAt workTape origin c.val)
  have er' : Executes input tape (.call (Rewind.program workTape))
      (4*(preceding++[!b,last]).length+6) c t :=
    .call _ c _ _ er (by simp [Rewind.program,Rewind.finishAt])
  refine ⟨t,?_,rw,?_⟩
  · convert ef'.seq (eb'.seq er') using 1 <;> first | rfl | simp; omega
  · exact (WordTransfer.frame_of_copy ff).trans ((changed_frame workTape b f.val).trans
      (WordTransfer.frame_rewind workTape workTape workTape (Or.inl rfl) origin c.val))

end Maxwell.Cost.WordPenultimate
