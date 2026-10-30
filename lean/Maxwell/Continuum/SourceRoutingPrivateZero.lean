import Maxwell.Continuum.SourceRoutingZeroExecution

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.PrivateZero
open Structured
open RationalAccumulator (Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 1800000

def banks : Finset ℕ := ZeroHeap.banks.image PrivateNode.shift
def Clean (s : Store) : Prop := ∀i∈banks,Blank s.val i
def code : Code := .call (ZeroHeap.code.compile.renameTapes PrivateNode.relocation)

structure Frame (s t : BitRAMState) : Prop where
  inputHead : t.inputHead=s.inputHead
  randomCursor : t.randomCursor=s.randomCursor
  output : t.output=s.output
  tapes : ∀i,i=4 ∨ 10 ≤ i→i≠37→i∉banks→t.tapes i=s.tapes i

theorem frame {s t : Store} (hf : ZeroHeap.Frame (s.renameTapes PrivateNode.relocation.symm).val t.val) :
    Frame s.val (t.renameTapes PrivateNode.relocation).val := by
  refine ⟨hf.inputHead,hf.randomCursor,hf.output,?_⟩
  intro i hi h37 hn
  have hlo : PrivateNode.shift i=4 ∨ 10 ≤ PrivateNode.shift i := by
    rcases hi with rfl|hi
    · exact Or.inl (PrivateNode.shift_small 4 (by omega))
    · exact Or.inr (PrivateNode.shift_large i hi)
  have hneq : PrivateNode.shift i≠37 := by
    intro he
    have hh:=congrArg PrivateNode.shift he
    rw [PrivateNode.shift_involutive,PrivateNode.shift_small 37 (by omega)] at hh
    exact h37 hh
  have hnot : PrivateNode.shift i∉ZeroHeap.banks := by
    intro hm
    apply hn
    exact Finset.mem_image.mpr ⟨PrivateNode.shift i,hm,PrivateNode.shift_involutive i⟩
  have hh:=hf.tapes (PrivateNode.shift i) hlo hneq hnot
  change t.val.tapes (PrivateNode.shift i)=s.val.tapes (PrivateNode.shift (PrivateNode.shift i)) at hh
  rw [PrivateNode.shift_involutive] at hh
  exact hh

theorem controls_fixed (i : ℕ) (hi : i∈ZeroHeap.controls) : PrivateNode.shift i=i := by
  simp only [ZeroHeap.controls,Finset.mem_insert,Finset.mem_singleton] at hi
  exact PrivateNode.shift_fixed i (by omega) (by omega)

theorem executes (q : ℕ→ℕ) (B : ℕ) (hB : 1 ≤ B)
    (hq : ∀i∈ZeroHeap.controls,(q i).bits.length ≤ B) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : PrivateVisit.Clean s) (hb : Clean s)
    (hi : ∀i∈ZeroHeap.controls,RationalAccumulator.Word s.val i (q i)) :
    ∃steps t,Executes input tape code steps s t ∧ steps ≤ 2^31*(q 801+1)*(B+2)^2 ∧
      PrivateVisit.Clean t ∧ Clean t ∧
      (∀i∈ZeroHeap.controls,RationalAccumulator.Word t.val i (q i)) ∧
      (∀p,q 800 ≤ p→p<q 800+q 801→t.val.memory p=false) ∧
      Memory.Frame (q 800) (q 801) s.val.memory t.val.memory ∧ Frame s.val t.val := by
  have inputWords : ∀i∈ZeroHeap.controls,RationalAccumulator.Word
      (s.renameTapes PrivateNode.relocation.symm).val i (q i) := by
    intro i hi'
    apply RationalAccumulator.word_of_eq _ (hi i hi')
    rw [PrivateNode.relocation_symm,PrivateNode.renamed_tape,controls_fixed i hi']
  have blank : ∀i∈ZeroHeap.banks,Blank (s.renameTapes PrivateNode.relocation.symm).val i := by
    intro i hi'
    exact hb (PrivateNode.shift i) (Finset.mem_image.mpr ⟨i,hi',rfl⟩)
  obtain ⟨steps,u,he,hcost,zu,bu,iu,mu,fu,gu⟩:=ZeroHeap.executes q B hB hq input tape
    (s.renameTapes PrivateNode.relocation.symm) hs blank inputWords
  let t:=u.renameTapes PrivateNode.relocation
  have ec : Executes input tape code (steps+1) s t := by
    simpa only [code,Store.renameTapes_symm] using he.renamed_call PrivateNode.relocation
  have clean : PrivateVisit.Clean t := by
    change NodeVisit.Clean ((u.renameTapes PrivateNode.relocation).renameTapes PrivateNode.relocation.symm).val
    rw [show (u.renameTapes PrivateNode.relocation).renameTapes PrivateNode.relocation.symm=u by
      simpa only [Equiv.symm_symm] using Store.renameTapes_symm PrivateNode.relocation.symm u]
    exact zu
  refine ⟨steps+1,t,ec,?_,clean,?_,?_,mu,fu,frame gu⟩
  · have hpos : 1 ≤ (q 801+1)*(B+2)^2 := Nat.succ_le_of_lt (by positivity)
    nlinarith only [hcost,hpos]
  · intro i hi'
    obtain ⟨j,hj,rfl⟩:=Finset.mem_image.mp hi'
    obtain ⟨origin,ho⟩:=bu j hj
    refine ⟨origin,?_⟩
    exact ((PrivateNode.renamed_tape u (PrivateNode.shift j)).trans
      (congrArg u.val.tapes (PrivateNode.shift_involutive j))).trans ho
  · intro i hi'
    apply RationalAccumulator.word_of_eq _ (iu i hi')
    exact (PrivateNode.renamed_tape u i).trans (congrArg u.val.tapes (controls_fixed i hi'))

#print axioms executes
end Maxwell.Cost.RoutingPorts.Complete.Tree.PrivateZero
