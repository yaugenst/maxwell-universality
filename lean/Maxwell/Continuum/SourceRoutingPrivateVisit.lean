import Maxwell.Continuum.SourceRoutingNodeVisit

/-! The complete reusable visit runs on reserved tapes 840..956.
Its five runtime control words and all source archives are preserved. -/

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.PrivateVisit
open Structured
set_option maxRecDepth 16384
set_option maxHeartbeats 1800000

def code : Code := .call (NodeVisit.code.compile.renameTapes PrivateNode.relocation)
def Clean (s : Store) : Prop := NodeVisit.Clean (s.renameTapes PrivateNode.relocation.symm).val

theorem controls_fixed (i : ℕ) (hi : i∈NodeSetup.controls) : PrivateNode.shift i=i := by
  simp only [NodeSetup.controls,Finset.mem_insert,Finset.mem_singleton] at hi
  exact PrivateNode.shift_fixed i (by omega) (by omega)

theorem inputs_renamed (q : ℕ→ℕ) (s : Store) (hs : NodeVisit.Inputs q s.val) :
    NodeVisit.Inputs q (s.renameTapes PrivateNode.relocation.symm).val := by
  intro i hi
  apply RationalAccumulator.word_of_eq _ (hs i hi)
  rw [PrivateNode.relocation_symm,PrivateNode.renamed_tape,controls_fixed i hi]

theorem inputs_back (q : ℕ→ℕ) (s : Store) (hs : NodeVisit.Inputs q s.val) :
    NodeVisit.Inputs q (s.renameTapes PrivateNode.relocation).val := by
  simpa only [PrivateNode.relocation_symm] using inputs_renamed q s hs

theorem executes (q : ℕ→ℕ) (k B : ℕ) (hn : q 801=2*2^k) (hw : q 802=k+2)
    (hq : ∀i∈NodeSetup.controls,(q i).bits.length ≤ B)
    (data : ChildPermutation.Data k) (hcolors : data.colors=BinarySplit.colors k data.target)
    (hsource : IncidenceEncoding.Separated (q 803) ((q 801)*(q 802)) (q 804) ((q 801)*(q 802)))
    (hforward : q 803+(q 801)*(q 802) ≤ q 800)
    (hbackward : q 804+(q 801)*(q 802) ≤ q 800)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : Clean s) (hin : NodeVisit.Inputs q s.val)
    (hf : BitArray.Represents s.val.memory (q 803) (q 802)
      (DoublingPass.words (q 802) (Vector.ofFn data.target)))
    (hb : BitArray.Represents s.val.memory (q 804) (q 802)
      (DoublingPass.words (q 802) (Vector.ofFn data.target.symm))) :
    ∃steps t, Executes input tape code steps s t ∧ steps ≤ NodeVisit.bound q k B+1 ∧
      ChildPermutation.Represents ((Node.layout (NodeSetup.descriptor q)).child (2*2^k)) t.val.memory data
        (ChildPermutation.finalOutputs ((Node.layout (NodeSetup.descriptor q)).child (2*2^k)).childWidth data) ∧
      Clean t ∧ NodeVisit.Inputs q t.val ∧ PrivateNode.Frame s.val t.val ∧
      SplitNode.MemoryFrame (Node.layout (NodeSetup.descriptor q)) k s.val.memory t.val.memory := by
  obtain ⟨steps,u,he,hcost,hu,hclean,hinputs,hframe,hmem⟩ := NodeVisit.executes q k B hn hw hq data
    hcolors hsource hforward hbackward input tape (s.renameTapes PrivateNode.relocation.symm)
    hs (inputs_renamed q s hin) hf hb
  let t := u.renameTapes PrivateNode.relocation
  have execution : Executes input tape code (steps+1) s t := by
    simpa only [code,Store.renameTapes_symm] using he.renamed_call PrivateNode.relocation
  have clean : Clean t := by
    have hr : (u.renameTapes PrivateNode.relocation).renameTapes PrivateNode.relocation.symm=u := by
      simpa only [Equiv.symm_symm] using Store.renameTapes_symm PrivateNode.relocation.symm u
    change NodeVisit.Clean ((u.renameTapes PrivateNode.relocation).renameTapes PrivateNode.relocation.symm).val
    rw [hr]
    exact hclean
  exact ⟨steps+1,t,execution,by omega,hu,clean,inputs_back q u hinputs,PrivateNode.frame hframe,hmem⟩

#print axioms executes

end Maxwell.Cost.RoutingPorts.Complete.Tree.PrivateVisit
