import Maxwell.Cost.RandomBitsMachine
import Maxwell.Cost.Structured.CounterClear
import Maxwell.Cost.NormalizeWord
import Maxwell.Cost.Structured.Rename

/-! The finite fair-bit reader followed by charged canonicalization and
counter cleanup. Its output is a natural operand for subsequent arithmetic. -/
namespace Maxwell.Cost.RandomNatMachine
open Structured RationalAccumulator

def code : Code := .seq RandomBitsMachine.code
  (.seq (.call (Rewind.program 241))
    (.seq (.call (NormalizeWord.program 241)) (.call (TapeOps.clear 240))))

def costBound (n : ℕ) : ℕ := RandomBitsMachine.cap n+20*n+6*n.bits.length+28

theorem executes (input : List Bool) (tape : ℕ→Bool) (n : ℕ) (s : Store)
    (count : Word s.val 240 n) (blank : Blank s.val 241) :
    ∃cost t,Executes input tape code cost s t ∧ cost≤costBound n ∧
      Word t.val 241 (addressValue (RandomBitsMachine.bits tape s.val.randomCursor n)) ∧
      Blank t.val 240 ∧ t.val.randomCursor=s.val.randomCursor+n ∧
      RandomBitsMachine.Frame s.val t.val := by
  obtain ⟨co,hco⟩ := count
  obtain ⟨wo,hwo⟩ := blank
  obtain ⟨c0,a,e0,h0,wa,ra,fa,finalWord,wc,hl⟩ :=
    RandomBitsMachine.executes input tape n co wo s hco hwo
  let bits := RandomBitsMachine.bits tape s.val.randomCursor n
  have bitsLength : bits.length=n := by simp [bits,RandomBitsMachine.bits]
  have rewind := WordTransfer.rewind_shifted 241 wo input tape bits a.val a.property wa
  let b := Store.ofState (Rewind.finishAt 241 wo a.val)
  have e1 : Executes input tape (.call (Rewind.program 241)) (4*n+6) a b := by
    simpa only [bitsLength] using Executes.call _ a _ _ rewind.1
      (by simp [Rewind.program,Rewind.finishAt])
  have f1 := NormalizeWord.rewind_frame 241 wo a.val
  obtain ⟨c2,u,h2,e2,pc2,w2,_,f2⟩ := NormalizeWord.simulation 241 wo input tape bits
    b.val b.property rewind.2
  let c := Store.ofState u
  have ec : Executes input tape (.call (NormalizeWord.program 241)) (c2+1) b c :=
    .call _ b u _ e2 (by simp [NormalizeWord.program,pc2,ScanForward.program,TapeOps.trim,
      Rewind.program,BitRAMInstruction.relocate])
  have cw : c.val.tapes 240=BitTape.shifted finalWord co :=
    (f2.2.2.2.2.2.1 240 (by decide)).trans
      ((f1.2.2.2.2.2.1 240 (by decide)).trans wc)
  obtain ⟨t,et,bt,ft⟩ := RuntimeCounter.clear_executes 240 input tape finalWord co c cw
  refine ⟨c0+((4*n+6)+((c2+1)+(6*finalWord.length+4))),t,
    e0.seq (e1.seq (ec.seq et)),?_,?_,bt,?_,?_⟩
  · rw [hl,bitsLength] at *
    unfold costBound
    omega
  · exact word_of_eq (ft.tapes 241 (by simp)) ⟨wo,w2⟩
  · exact ft.randomCursor.trans (f2.2.2.2.1.trans (f1.2.2.2.1.trans ra))
  · refine ⟨ft.address.trans (f2.1.trans (f1.1.trans fa.address)),
      ft.inputHead.trans (f2.2.1.trans (f1.2.1.trans fa.inputHead)),
      ft.memory.trans (f2.2.2.1.trans (f1.2.2.1.trans fa.memory)),
      ft.output.trans (f2.2.2.2.2.1.trans (f1.2.2.2.2.1.trans fa.output)),?_⟩
    intro i hi hj
    exact (ft.tapes i (by simpa using hi)).trans
      ((f2.2.2.2.2.2.1 i hj).trans ((f1.2.2.2.2.2.1 i hj).trans (fa.tapes i hi hj)))

#print axioms executes

def codeOn (p : Equiv.Perm ℕ) : Code := .call (code.compile.renameTapes p)

theorem executes_on (p : Equiv.Perm ℕ) (input : List Bool) (tape : ℕ→Bool) (n : ℕ) (s : Store)
    (count : Word s.val (p 240) n) (blank : Blank s.val (p 241)) :
    ∃cost t,Executes input tape (codeOn p) cost s t ∧ cost≤costBound n+1 ∧
      Word t.val (p 241) (addressValue (RandomBitsMachine.bits tape s.val.randomCursor n)) ∧
      Blank t.val (p 240) ∧ t.val.randomCursor=s.val.randomCursor+n ∧
      RandomBitsMachine.Frame s.val t.val (p 240) (p 241) := by
  let a := s.renameTapes p.symm
  have ac : Word a.val 240 n := by
    simpa only [Word,a,Store.renameTapes,BitRAMState.renameTapes,Equiv.symm_symm,Function.comp_apply] using count
  have ab : Blank a.val 241 := by
    simpa only [Blank,a,Store.renameTapes,BitRAMState.renameTapes,Equiv.symm_symm,Function.comp_apply] using blank
  obtain ⟨c,u,eu,cu,wu,bu,ru,fu⟩ := executes input tape n a ac ab
  let t := u.renameTapes p
  have et : Executes input tape (codeOn p) (c+1) s t := by
    simpa only [a,t,codeOn,Store.renameTapes_symm] using eu.renamed_call p
  refine ⟨c+1,t,et,Nat.add_le_add_right cu 1,?_,?_,ru,?_,?_,?_,?_,?_⟩
  · simpa only [Word,t,a,Store.renameTapes,BitRAMState.renameTapes,Function.comp_apply,
      Equiv.symm_apply_apply] using wu
  · simpa only [Blank,t,Store.renameTapes,BitRAMState.renameTapes,Function.comp_apply,
      Equiv.symm_apply_apply] using bu
  · exact fu.address
  · exact fu.inputHead
  · exact fu.memory
  · exact fu.output
  · intro i hi hj
    have first : p.symm i≠240 := by intro h;apply hi;rw [←h,p.apply_symm_apply]
    have second : p.symm i≠241 := by intro h;apply hj;rw [←h,p.apply_symm_apply]
    simpa only [t,a,Store.renameTapes,BitRAMState.renameTapes,Function.comp_apply,
      Equiv.symm_symm,Equiv.apply_symm_apply] using fu.tapes (p.symm i) first second

#print axioms executes_on
end Maxwell.Cost.RandomNatMachine
