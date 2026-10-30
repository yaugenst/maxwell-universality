import Maxwell.Continuum.SourceRoutingNodeExecution
import Maxwell.Cost.Structured.Rename

/-! Fixed routing work tapes occupy 840..956. The original source graph
metadata and the later rational coefficient bank are preserved. -/

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.PrivateNode
open Structured
open RationalAccumulator (Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 1800000

def shift (i : ℕ) : ℕ :=
  if 80 ≤ i ∧ i ≤ 196 then i+760 else
  if 840 ≤ i ∧ i ≤ 956 then i-760 else i

theorem shift_source (i : ℕ) (hi : 80 ≤ i ∧ i ≤ 196) : shift i=i+760 := by
  simp [shift,hi]

theorem shift_target (i : ℕ) (hi : 840 ≤ i ∧ i ≤ 956) : shift i=i-760 := by
  have hn : ¬(80 ≤ i ∧ i ≤ 196) := by omega
  simp [shift,hn,hi]

theorem shift_fixed (i : ℕ) (hs : ¬(80 ≤ i ∧ i ≤ 196))
    (ht : ¬(840 ≤ i ∧ i ≤ 956)) : shift i=i := by
  simp only [shift,hs,ht,ite_false]

theorem shift_involutive : Function.Involutive shift := by
  intro i
  by_cases hs : 80 ≤ i ∧ i ≤ 196
  · rw [shift_source i hs,shift_target (i+760) (by omega)]
    omega
  · by_cases ht : 840 ≤ i ∧ i ≤ 956
    · rw [shift_target i ht,shift_source (i-760) (by omega)]
      omega
    · rw [shift_fixed i hs ht,shift_fixed i hs ht]

def relocation : Equiv.Perm ℕ := ⟨shift,shift,shift_involutive,shift_involutive⟩
@[simp] theorem relocation_symm : relocation.symm=relocation := rfl

theorem renamed_tape (s : Store) (i : ℕ) :
    (s.renameTapes relocation).val.tapes i=s.val.tapes (shift i) := rfl

theorem shift_small (i : ℕ) (hi : i<80) : shift i=i := shift_fixed i (by omega) (by omega)
theorem shift_large (i : ℕ) (hi : 10 ≤ i) : 10 ≤ shift i := by
  unfold shift
  split_ifs <;> omega

def code : Code := .call (Node.code.compile.renameTapes relocation)
def banks : List ℕ := NodeCleanup.banks.map shift
def Ready (v : ℕ→ℕ) (clock : List Bool) (s : Store) : Prop :=
  Node.Ready v clock (s.renameTapes relocation.symm).val
def Workspace (s : Store) : Prop := DoublingInit.Workspace (s.renameTapes relocation.symm).val

structure Frame (s t : BitRAMState) : Prop where
  inputHead : t.inputHead=s.inputHead
  randomCursor : t.randomCursor=s.randomCursor
  output : t.output=s.output
  tapes : ∀i, i=4 ∨ 10 ≤ i → i≠37 → i∉banks → t.tapes i=s.tapes i

theorem frame {s t : Store}
    (hf : Node.Frame (s.renameTapes relocation.symm).val t.val) :
    Frame s.val (t.renameTapes relocation).val := by
  refine ⟨hf.inputHead,hf.randomCursor,hf.output,?_⟩
  intro i hi h37 hbank
  have hlarge : shift i=4 ∨ 10 ≤ shift i := by
    rcases hi with rfl|hi
    · exact Or.inl (shift_small 4 (by omega))
    · exact Or.inr (shift_large i hi)
  have hn37 : shift i≠37 := by
    intro he
    have hh := congrArg shift he
    rw [shift_involutive,shift_small 37 (by omega)] at hh
    exact h37 hh
  have hn : shift i∉NodeCleanup.banks := by
    intro hh
    exact hbank (List.mem_map.mpr ⟨shift i,hh,shift_involutive i⟩)
  have hh := hf.tapes (shift i) hlarge hn37 hn
  change t.val.tapes (shift i)=s.val.tapes (shift (shift i)) at hh
  rw [shift_involutive i] at hh
  exact hh

theorem executes (v : ℕ→ℕ) (k B : ℕ) (clock : List Bool)
    (hn : v 191=2*2^k) (hw : v 192=k+2) (hc : clock.length=v 192)
    (hv : ∀i∈RoutingAllocator.ids,(v i).bits.length ≤ B)
    (data : ChildPermutation.Data k) (hcolors : data.colors=BinarySplit.colors k data.target)
    (hsource : IncidenceEncoding.Separated (v 193) ((v 191)*(v 192)) (v 194) ((v 191)*(v 192)))
    (hforward : v 193+(v 191)*(v 192) ≤ v 190)
    (hbackward : v 194+(v 191)*(v 192) ≤ v 190)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : Ready v clock s)
    (hf : BitArray.Represents s.val.memory (v 193) (v 192)
      (DoublingPass.words (v 192) (Vector.ofFn data.target)))
    (hb : BitArray.Represents s.val.memory (v 194) (v 192)
      (DoublingPass.words (v 192) (Vector.ofFn data.target.symm))) :
    ∃steps t, Executes input tape code steps s t ∧ steps ≤ Node.costBound v k B+1 ∧
      ChildPermutation.Represents ((Node.layout v).child (2*2^k)) t.val.memory data
        (ChildPermutation.finalOutputs ((Node.layout v).child (2*2^k)).childWidth data) ∧
      Workspace t ∧ (∀i∈banks,Blank t.val i) ∧ Frame s.val t.val ∧
      SplitNode.MemoryFrame (Node.layout v) k s.val.memory t.val.memory := by
  obtain ⟨steps,u,he,hcost,hu,hwork,hblank,hframe,hmem⟩ := Node.executes v k B clock hn hw hc hv data
    hcolors hsource hforward hbackward input tape (s.renameTapes relocation.symm) hs hf hb
  let t := u.renameTapes relocation
  have execution : Executes input tape code (steps+1) s t := by
    simpa only [code,Store.renameTapes_symm] using he.renamed_call relocation
  have workspace : Workspace t := by
    have hr : (u.renameTapes relocation).renameTapes relocation.symm=u := by
      simpa only [Equiv.symm_symm] using Store.renameTapes_symm relocation.symm u
    change DoublingInit.Workspace ((u.renameTapes relocation).renameTapes relocation.symm).val
    rw [hr]
    exact hwork
  refine ⟨steps+1,t,execution,by omega,hu,workspace,?_,frame hframe,hmem⟩
  intro i hi
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi
  obtain ⟨origin,hword⟩ := hblank j hj
  refine ⟨origin,?_⟩
  change u.val.tapes (shift (shift j))={BitTape.blank with head:=origin}
  rw [shift_involutive]
  exact hword

#print axioms shift_involutive
#print axioms executes

end Maxwell.Cost.RoutingPorts.Complete.Tree.PrivateNode
