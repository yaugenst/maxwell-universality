import Maxwell.Continuum.NaturalBankDivMod
import Maxwell.Cost.WordReplace
import Maxwell.Cost.NormalizeWord

/-! A padded runtime counter is copied and trimmed by actual fixed code
before it enters the canonical natural arithmetic register bank. -/

namespace Maxwell.Continuum.RationalDataflow.NaturalImport

open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 2500000

def code (source target : ℕ) : Code :=
  .seq (WordReplace.code source target) (.call (NormalizeWord.program target))

theorem executes (allIds : Finset ℕ) (source target : ℕ) (ht : target∈allIds)
    (hne : source≠target) (v : ℕ → ℕ) (xs : List Bool)
    (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (hs : NatAssign.Bank allIds v s.val) (hx : BankArray.Word s.val source xs) :
    ∃ cost t, Executes input tape (code source target) cost s t ∧
      cost≤6*(v target).bits.length+31*xs.length+39 ∧
      NatAssign.Bank allIds (Function.update v target (addressValue xs)) t.val ∧
      BinaryPrecision.Frame {target} s.val t.val := by
  obtain ⟨u,e0,wu,f0⟩ := WordReplace.executes source target hne input tape xs (v target).bits s hx (hs target ht)
  obtain ⟨origin,ho⟩ := wu
  obtain ⟨cost,t,hcost,et,hpc,word,_,f1⟩ := NormalizeWord.simulation target origin input tape xs u.val u.property ho
  have e1 : Executes input tape (.call (NormalizeWord.program target)) (cost+1) u (Store.ofState t) :=
    .call _ u t _ et (by
      simp [NormalizeWord.program,hpc,ScanForward.program,TapeOps.trim,Rewind.program,BitRAMInstruction.relocate])
  have frame : BinaryPrecision.Frame {target} s.val (Store.ofState t).val := by
    refine ⟨f1.1.trans f0.1,f1.2.1.trans f0.2.1,f1.2.2.1.trans f0.2.2.1,f1.2.2.2.1.trans f0.2.2.2.1,
      f1.2.2.2.2.1.trans f0.2.2.2.2.1,?_⟩
    intro k hk
    have he : k≠target := by simpa only [Finset.mem_singleton] using hk
    exact (f1.2.2.2.2.2.1 k he).trans (f0.2.2.2.2.2.1 k he)
  refine ⟨(6*(v target).bits.length+15*xs.length+21)+(cost+1),Store.ofState t,e0.seq e1,
    by omega,?_,frame⟩
  intro k hk
  by_cases he : k=target
  · subst k
    rw [Function.update_self]
    exact ⟨origin,word⟩
  · simpa only [Function.update_of_ne he] using RationalAccumulator.word_of_eq
      (frame.tapes k (by simpa only [Finset.mem_singleton] using he)) (hs k hk)

#print axioms executes

end Maxwell.Continuum.RationalDataflow.NaturalImport
