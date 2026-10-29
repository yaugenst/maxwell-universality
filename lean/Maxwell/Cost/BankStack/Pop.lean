import Maxwell.Cost.BankStack.Push
import Maxwell.Cost.NormalizeWord

namespace Maxwell.Cost.BankStack
open Structured
open BankArray (Word)
open RationalAccumulator (Blank)

def popCode (stack clock target : ℕ) : Code :=
  .seq (SourceCircuit.WordStack.code stack clock target) (.call (NormalizeWord.program target))

theorem pop (stack clockBank target : ℕ)
    (ha : 10 ≤ stack) (ht : 10 ≤ target)
    (hac : stack≠clockBank) (hat : stack≠target) (hct : clockBank≠target)
    (input : List Bool) (tape : ℕ → Bool)
    (bits clock preceding : List Bool) (hclock : clock.length=bits.length)
    (s : Store) (hstack : s.val.tapes stack=BitTape.atEnd (preceding++bits))
    (hblank : Blank s.val target) (hclockBank : Word s.val clockBank clock)
    (scratch : BankArray.Scratch s.val) (h7 : Blank s.val 7) :
    ∃ cost t, cost≤31*bits.length+28 ∧ Executes input tape (popCode stack clockBank target) cost s t ∧
      t.val.tapes stack=BitTape.atEnd preceding ∧ Word t.val target (addressValue bits).bits ∧
      t.val.tapes clockBank=s.val.tapes clockBank ∧ BankArray.Scratch t.val ∧ Blank t.val 7 ∧
      t.val.memory=s.val.memory ∧ SourceCircuit.Frame {stack,target} s.val t.val := by
  obtain ⟨targetOrigin,htarget⟩ := hblank
  obtain ⟨co,hclockBank⟩ := hclockBank
  obtain ⟨p,ep,pstack,ptarget,pclock,_,pmemory,pframe,pkeep⟩ :=
    SourceCircuit.WordStack.executes stack clockBank target hac hat hct input tape bits preceding clock
      targetOrigin co s hclock hstack htarget hclockBank
  obtain ⟨nc,t,hnc,en,tpc,ttarget,_,nf⟩ := NormalizeWord.simulation target (targetOrigin-bits.length) input tape bits
    p.val p.property ptarget
  let finalStore := Store.ofState t
  have et : Executes input tape (.call (NormalizeWord.program target)) (nc+1) p finalStore :=
    .call _ p t nc en (by simp [NormalizeWord.program,tpc,ScanForward.program,TapeOps.trim,Rewind.program,BitRAMInstruction.relocate])
  have nf' : SourceCircuit.Frame {stack,target} p.val finalStore.val :=
    ⟨nf.2.1,nf.2.2.2.1,nf.2.2.2.2.1,
      fun j _ hj => nf.2.2.2.2.2.1 j (by simp_all),
      nf.2.2.2.2.2.2 23 (by omega) (by omega) (by omega) (by omega),
      fun j hj => nf.2.2.2.2.2.2 j (by omega) (by omega) (by omega) (by omega)⟩
  have keepSmall (i : ℕ) (hi : i<10) : finalStore.val.tapes i=s.val.tapes i :=
    (nf.2.2.2.2.2.1 i (by omega)).trans (pkeep i (by omega) (by omega))
  exact ⟨15*bits.length+10+(nc+1),finalStore,by omega,ep.seq et,
    (nf.2.2.2.2.2.1 stack hat).trans pstack,⟨targetOrigin-bits.length,ttarget⟩,
    (nf.2.2.2.2.2.1 clockBank hct).trans pclock,
    SourceCircuit.scratch_of_tapes scratch keepSmall,
    RationalAccumulator.blank_of_eq (keepSmall 7 (by omega)) h7,
    nf.2.2.1.trans pmemory,pframe.trans nf'⟩

/-- Exact inverse on canonical natural banks; padding does not change the value. -/
theorem pop_canonical (stack clockBank target : ℕ)
    (ha : 10 ≤ stack) (ht : 10 ≤ target)
    (hac : stack≠clockBank) (hat : stack≠target) (hct : clockBank≠target)
    (input : List Bool) (tape : ℕ → Bool) (value : ℕ) (clock preceding : List Bool)
    (hfit : value.bits.length≤clock.length) (s : Store)
    (hstack : s.val.tapes stack=BitTape.atEnd (preceding++FixedWidth.bits clock.length value.bits))
    (hblank : Blank s.val target) (hclockBank : Word s.val clockBank clock)
    (scratch : BankArray.Scratch s.val) (h7 : Blank s.val 7) :
    ∃ cost t, cost≤31*clock.length+28 ∧ Executes input tape (popCode stack clockBank target) cost s t ∧
      t.val.tapes stack=BitTape.atEnd preceding ∧ Word t.val target value.bits ∧
      t.val.tapes clockBank=s.val.tapes clockBank ∧ BankArray.Scratch t.val ∧ Blank t.val 7 ∧
      t.val.memory=s.val.memory ∧ SourceCircuit.Frame {stack,target} s.val t.val := by
  obtain ⟨cost,t,hcost,he,hs,hw,hc,hsc,h7,hm,hf⟩ := pop stack clockBank target ha ht hac hat hct
    input tape (FixedWidth.bits clock.length value.bits) clock preceding
    (by simp [FixedWidth.bits_length]) s hstack hblank hclockBank scratch h7
  refine ⟨cost,t,by simpa only [FixedWidth.bits_length] using hcost,he,hs,?_,hc,hsc,h7,hm,hf⟩
  simpa only [FixedWidth.bits_value _ _ hfit,addressValue_bits] using hw

end Maxwell.Cost.BankStack
