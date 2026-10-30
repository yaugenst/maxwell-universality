import Maxwell.Continuum.SourceRoutingAssemblyExecution

/-! Reverse label assembly uses the same reserved routing workspace as
the forward split. All source archives and tree-controller words survive. -/

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.PrivateAssembly
open Structured
set_option maxRecDepth 16384
set_option maxHeartbeats 1800000

def code : Code := .call (Assembly.code.compile.renameTapes PrivateNode.relocation)

theorem controls_fixed (i : ℕ) (hi : i∈Assembly.controls) : PrivateNode.shift i=i := by
  simp only [Assembly.controls,Finset.mem_Icc] at hi
  exact PrivateNode.shift_fixed i (by omega) (by omega)

theorem executes (q : ℕ→ℕ) (k B : ℕ) (hB : 1 ≤ B)
    (hn : q 801=2*2^k) (hw : q 802=k+2) (hq : ∀i∈Assembly.controls,(q i).bits.length ≤ B)
    (data : ColorAssemble.Data k) (hsep : ColorAssemble.Separated (Assembly.layout q) k)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : PrivateVisit.Clean s)
    (hi : ∀i∈Assembly.controls,RationalAccumulator.Word s.val i (q i))
    (hcolors : BitArray.Represents s.val.memory (Assembly.layout q).colors 1 (ColorPass.colorWords data.colors))
    (hl : BitArray.Represents s.val.memory (Assembly.layout q).leftForward (Assembly.layout q).childWidth
      (DoublingPass.words (Assembly.layout q).childWidth data.left))
    (hr : BitArray.Represents s.val.memory (Assembly.layout q).rightForward (Assembly.layout q).childWidth
      (DoublingPass.words (Assembly.layout q).childWidth data.right)) :
    ∃steps t,Executes input tape code steps s t ∧ steps ≤ 2^45*(q 801+1)*(B+2)^2 ∧
      ColorAssemble.Represents (Assembly.layout q) t.val.memory data
        (ColorAssemble.finalOutput (Assembly.layout q) data) ∧
      PrivateVisit.Clean t ∧ PrivateNode.Frame s.val t.val ∧
      ColorAssemble.MemoryFrame (Assembly.layout q) k s.val.memory t.val.memory := by
  have renamed : ∀i∈Assembly.controls,RationalAccumulator.Word
      (s.renameTapes PrivateNode.relocation.symm).val i (q i) := by
    intro i hi'
    apply RationalAccumulator.word_of_eq _ (hi i hi')
    rw [PrivateNode.relocation_symm,PrivateNode.renamed_tape,controls_fixed i hi']
  obtain ⟨steps,u,he,hcost,rep,zu,fu,mu⟩:=Assembly.executes q k B hB hn hw hq data hsep
    input tape (s.renameTapes PrivateNode.relocation.symm) hs renamed hcolors hl hr
  let t:=u.renameTapes PrivateNode.relocation
  have execution : Executes input tape code (steps+1) s t := by
    simpa only [code,Store.renameTapes_symm] using he.renamed_call PrivateNode.relocation
  have clean : PrivateVisit.Clean t := by
    change NodeVisit.Clean ((u.renameTapes PrivateNode.relocation).renameTapes PrivateNode.relocation.symm).val
    rw [show (u.renameTapes PrivateNode.relocation).renameTapes PrivateNode.relocation.symm=u by
      simpa only [Equiv.symm_symm] using Store.renameTapes_symm PrivateNode.relocation.symm u]
    exact zu
  refine ⟨steps+1,t,execution,?_,rep,clean,PrivateNode.frame fu,mu⟩
  have hpos : 1 ≤ (q 801+1)*(B+2)^2 := Nat.succ_le_of_lt (by positivity)
  nlinarith only [hcost,hpos]

#print axioms executes
end Maxwell.Cost.RoutingPorts.Complete.Tree.PrivateAssembly
