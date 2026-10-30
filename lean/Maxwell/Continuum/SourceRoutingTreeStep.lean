import Maxwell.Continuum.SourceRoutingTreeDescriptor
import Maxwell.Continuum.SourceRoutingTreeMemory

/-! The fixed inner tree-loop body computes a descriptor, executes the
private split, and advances the stored node index by one. -/

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.Step
open Structured
open RationalAccumulator (Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 2200000

def increment : List NatAssign.Instruction := [.literal 818 1,.add 818 815]
def output (v : ℕ→ℕ) : ℕ→ℕ := NatAssign.values increment (Descriptor.output v)
def wordBound (B : ℕ) : ℕ := 2^24*(4*(B+1)+1)
def cost (v : ℕ→ℕ) (k B : ℕ) : ℕ :=
  2^160*(B+2)^2+(NodeVisit.bound (Descriptor.output v) k (wordBound B)+1)+
    3000*8^2*(wordBound B+2)^2
def code : Code := .seq Descriptor.code (.seq PrivateVisit.code (NatAssign.code increment))

structure Frame (s t : BitRAMState) : Prop where
  inputHead : t.inputHead=s.inputHead
  randomCursor : t.randomCursor=s.randomCursor
  output : t.output=s.output
  tapes : ∀i,i=4 ∨ 10 ≤ i → i≠37 → i∉Division.work → i∉PrivateNode.banks → t.tapes i=s.tapes i

theorem descriptor_width (v : ℕ→ℕ) (B : ℕ) (hB : 3 ≤ B)
    (hw : ∀i∈Division.ids,(v i).bits.length ≤ B) :
    ∀i∈Division.ids,(Descriptor.output v i).bits.length ≤ wordBound B := by
  have lit0 : ∀a∈Descriptor.prepare,a.literalWidth ≤ B := by
    simp [Descriptor.prepare,NatAssign.Instruction.literalWidth]
  have w0 : ∀i∈Division.ids,(NatAssign.values Descriptor.prepare v i).bits.length ≤ 4*(B+1) := by
    intro i hi
    have hh := NatAssign.values_width_bound Division.ids Descriptor.prepare Descriptor.prepare_valid v B hw lit0 i hi
    change _+1 ≤ 4*(B+1) at hh
    omega
  have w1 : ∀i∈Division.ids,(Descriptor.divided v i).bits.length ≤ 4*(B+1) := by
    intro i hi
    by_cases hq : i=816
    · subst i
      have hh := (Maxwell.Continuum.RationalWords.bits_mono (Nat.div_le_self (v 814+v 815) 2)).trans
        (by simpa only [Descriptor.prepare_value] using w0 805 (by decide))
      simpa only [Descriptor.divided,Function.update_self,Function.update_of_ne (by decide : (816 : ℕ)≠817)] using hh
    · by_cases hr : i=817
      · subst i
        have hh := (Maxwell.Continuum.RationalWords.bits_mono (Nat.mod_le (v 814+v 815) 2)).trans
          (by simpa only [Descriptor.prepare_value] using w0 805 (by decide))
        simpa only [Descriptor.divided,Function.update_self] using hh
      · simpa only [Descriptor.divided,Function.update_of_ne hq,Function.update_of_ne hr] using w0 i hi
  have lit1 : ∀a∈Descriptor.finish,a.literalWidth ≤ 4*(B+1) := by
    simp only [Descriptor.finish,List.mem_cons,List.not_mem_nil,or_false]
    intro a ha
    rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals norm_num [NatAssign.Instruction.literalWidth,show (6 : ℕ).bits.length=3 by decide]
    all_goals omega
  intro i hi
  have hh := NatAssign.values_width_bound Division.ids Descriptor.finish Descriptor.finish_valid
    (Descriptor.divided v) (4*(B+1)) w1 lit1 i hi
  exact (Nat.le_add_right _ 1).trans hh

theorem private_keep (i : ℕ) (hi : i∈Division.ids) : i≠37 ∧ i∉PrivateNode.banks := by
  have hlo:=Division.ids_lower i hi
  have h37 : i≠37 := by
    simp only [Division.ids,Division.controls,Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,
      Finset.mem_union,Finset.mem_Icc,Finset.mem_insert,Finset.mem_singleton] at hi
    omega
  refine ⟨h37,?_⟩
  have disjoint : Disjoint Division.ids PrivateNode.banks.toFinset := by decide
  exact fun hm => Finset.disjoint_left.mp disjoint hi (List.mem_toFinset.mpr hm)

theorem executes (v : ℕ→ℕ) (k B : ℕ) (hB : 3 ≤ B) (htwo : v 819=2)
    (hn : v 811=2*2^k) (hw : v 812=k+2)
    (hzero : ∀i∈Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,v i=0)
    (hwords : ∀i∈Division.ids,(v i).bits.length ≤ B)
    (data : ChildPermutation.Data k) (hcolors : data.colors=BinarySplit.colors k data.target)
    (hsource : IncidenceEncoding.Separated (Descriptor.output v 803) ((2*2^k)*(k+2))
      (Descriptor.output v 804) ((2*2^k)*(k+2)))
    (hforward : Descriptor.output v 803+(2*2^k)*(k+2) ≤ Descriptor.output v 800)
    (hbackward : Descriptor.output v 804+(2*2^k)*(k+2) ≤ Descriptor.output v 800)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : NatAssign.Bank Division.ids v s.val)
    (hc : PrivateVisit.Clean s) (h839 : Blank s.val 839)
    (hf : BitArray.Represents s.val.memory (Descriptor.output v 803) (k+2)
      (DoublingPass.words (k+2) (Vector.ofFn data.target)))
    (hb : BitArray.Represents s.val.memory (Descriptor.output v 804) (k+2)
      (DoublingPass.words (k+2) (Vector.ofFn data.target.symm))) :
    ∃steps t, Executes input tape code steps s t ∧ steps ≤ cost v k B ∧
      NatAssign.Bank Division.ids (output v) t.val ∧ PrivateVisit.Clean t ∧ Blank t.val 839 ∧
      ChildPermutation.Represents ((Node.layout (NodeSetup.descriptor (Descriptor.output v))).child (2*2^k))
        t.val.memory data (ChildPermutation.finalOutputs (k+1) data) ∧ Frame s.val t.val ∧
      SplitNode.MemoryFrame (Node.layout (NodeSetup.descriptor (Descriptor.output v))) k s.val.memory t.val.memory := by
  obtain ⟨c0,a,e0,h0,b0,z0,a839,f0⟩ := Descriptor.executes v htwo hzero B hB hwords input tape s hs hc h839
  have wd := descriptor_width v B hB hwords
  have dn : Descriptor.output v 801=2*2^k := (Descriptor.output_count v).trans hn
  have dw : Descriptor.output v 802=k+2 := (Descriptor.output_width v).trans hw
  have control_subset : NodeSetup.controls⊆Division.ids := by decide
  obtain ⟨c1,b,e1,h1,rep,z1,_,f1,m1⟩ := PrivateVisit.executes (Descriptor.output v) k (wordBound B) dn dw
    (fun i hi => wd i (control_subset hi)) data hcolors
    (by simpa only [dn,dw] using hsource) (by simpa only [dn,dw] using hforward)
    (by simpa only [dn,dw] using hbackward) input tape a z0 (fun i hi => b0 i (control_subset hi))
    (by simpa only [f0.memory,dw] using hf) (by simpa only [f0.memory,dw] using hb)
  have b1 : NatAssign.Bank Division.ids (Descriptor.output v) b.val := by
    intro i hi
    exact RationalAccumulator.word_of_eq (f1.tapes i (Or.inr (Division.ids_lower i hi))
      (private_keep i hi).1 (private_keep i hi).2) (b0 i hi)
  have b839 : Blank b.val 839 := RationalAccumulator.blank_of_eq
    (f1.tapes 839 (by omega) (by omega) (by decide)) a839
  have vi : ∀a∈increment,a.Valid Division.ids := by
    simp [increment,NatAssign.Instruction.Valid,Division.ids,Division.controls]
  have li : ∀a∈increment,a.literalWidth ≤ wordBound B := by
    simp [increment,NatAssign.Instruction.literalWidth,wordBound]
    omega
  obtain ⟨c2,t,e2,h2,b2,z2,f2⟩ := Arithmetic.stage increment vi (Descriptor.output v) (wordBound B) wd li
    input tape b b1 z1
  have childWidth : ((Node.layout (NodeSetup.descriptor (Descriptor.output v))).child (2*2^k)).childWidth=k+1 := by
    change Descriptor.output v 802-1=k+1
    rw [dw]; omega
  refine ⟨c0+(c1+c2),t,e0.seq (e1.seq e2),?_,b2,z2,
    RationalAccumulator.blank_of_eq (f2.tapes 839 (by decide)) b839,?_,?_,?_⟩
  · change c2 ≤ 3000*8^2*(wordBound B+2)^2 at h2
    dsimp only [cost]; omega
  · simpa only [f2.memory,childWidth] using rep
  · refine ⟨f2.inputHead.trans (f1.inputHead.trans f0.inputHead),
      f2.randomCursor.trans (f1.randomCursor.trans f0.randomCursor),
      f2.output.trans (f1.output.trans f0.output),?_⟩
    intro i hi h37 hd hp
    exact (f2.tapes i (fun hm => hd (Arithmetic.work_subset hm))).trans
      ((f1.tapes i hi h37 hp).trans (f0.tapes i hd))
  · intro p hp hj
    exact (congrFun f2.memory p).trans ((m1 p hp hj).trans (congrFun f0.memory p))

#print axioms executes
end Maxwell.Cost.RoutingPorts.Complete.Tree.Step
