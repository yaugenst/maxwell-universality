import Maxwell.Cost.DecoderConstants.Helpers
import Maxwell.Cost.WordLength
import Maxwell.Cost.BinaryPrecision

namespace Maxwell.Cost.RoutingPorts
open Structured RationalAccumulator

def powerCode (source counter target : ℕ) : Code :=
  .seq (PowerOfTwo.code source counter target) (.call (Rewind.program target))

theorem power (source counter target : ℕ) (hsc : source ≠ counter)
    (hst : source ≠ target) (hct : counter ≠ target)
    (input : List Bool) (tape : ℕ → Bool) (n : ℕ) (s : Store)
    (hw : Word s.val source n) (hc : Blank s.val counter) (ht : Blank s.val target) :
    ∃ cost t, Executes input tape (powerCode source counter target) cost s t ∧
      cost ≤ (n+1)*(13*n.bits.length+25)+21*n.bits.length+27 ∧
      Word t.val target (2^n) ∧ Blank t.val counter ∧
      BinaryPrecision.Frame {counter,target} s.val t.val := by
  obtain ⟨so,hso⟩ := hw
  obtain ⟨co,hco⟩ := hc
  obtain ⟨o,ho⟩ := ht
  obtain ⟨cost,p,ep,hcost,_hps,hpc,hpt,pf⟩ := PowerOfTwo.executes source counter target hsc hst hct
    input tape n.bits so co o s hso hco ho
  simp only [RationalAccumulator.address_bits] at hcost hpt
  obtain ⟨hr,hrword⟩ := WordTransfer.rewind_shifted target o input tape (2^n).bits p.val p.property hpt
  let t := Store.ofState (Rewind.finishAt target o p.val)
  have et : Executes input tape (.call (Rewind.program target)) (4*(2^n).bits.length+6) p t :=
    .call _ _ _ _ hr rfl
  have rf := WordTransfer.frame_rewind counter target target (Or.inr rfl) o p.val
  have fp : BinaryPrecision.Frame {counter,target} s.val p.val :=
    ⟨pf.1,pf.2.1,pf.2.2.1,pf.2.2.2.1,pf.2.2.2.2.1,fun i hi =>
      pf.2.2.2.2.2.1 i (by simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hi; exact hi.1)
        (by simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hi; exact hi.2)⟩
  have ft : BinaryPrecision.Frame {counter,target} p.val t.val :=
    ⟨rf.1,rf.2.1,rf.2.2.1,rf.2.2.2.1,rf.2.2.2.2.1,fun i hi =>
      rf.2.2.2.2.2.1 i (by simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hi; exact hi.1)
        (by simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hi; exact hi.2)⟩
  refine ⟨_,t,ep.seq et,?_,⟨o,hrword⟩,?_,fp.trans ft⟩
  · have hlen : (2^n).bits.length=n+1 := by simp [PowerOfTwo.power_bits]
    rw [hlen]; nlinarith
  · refine ⟨co+n.bits.length,?_⟩
    simpa only [t,Store.ofState,Rewind.finishAt,BitRAMState.setTape,
      Function.update_of_ne hct] using hpc

/-- Counting a stored word's bits is another actual tape scan. -/
theorem wordLength (source target : ℕ) (hne : source ≠ target)
    (input : List Bool) (tape : ℕ → Bool) (n : ℕ) (s : Store)
    (hw : Word s.val source n) (ht : Blank s.val target) :
    ∃ cost t, Executes input tape (WordLength.code source target) cost s t ∧
      cost ≤ 48*(n.bits.length+1)^2+1 ∧ Word t.val target n.bits.length ∧
      BinaryPrecision.Frame {target} s.val t.val := by
  obtain ⟨so,hso⟩ := hw
  obtain ⟨o,ho⟩ := ht
  obtain ⟨cost,t,he,hcost,hts,htt,hf⟩ := WordLength.executes source target hne
    input tape n.bits so o s hso ho
  refine ⟨cost,t,he,hcost,⟨o,htt⟩,hf.1,hf.2.1,hf.2.2.1,hf.2.2.2.1,hf.2.2.2.2.1,?_⟩
  intro i hi
  by_cases hs : i=source
  · subst i; exact hts.trans hso.symm
  · exact hf.2.2.2.2.2.1 i hs (by simpa using hi)

end Maxwell.Cost.RoutingPorts
