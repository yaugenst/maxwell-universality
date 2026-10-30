import Maxwell.Continuum.SourceRoutingForwardStart
import Maxwell.Continuum.SourceRoutingTreeRoot

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.RootRun
open Structured
open RationalAccumulator (Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 2200000

structure Setup (v : ℕ→ℕ) (heap rows total : ℕ) : Prop where
  controller : ForwardStart.Setup v heap rows total
  heapWord : v 800=heap
  countWord : v 801=2^(total+rows)
  widthWord : v 802=total+rows+1

def code : Code := .seq PrivateVisit.code (.seq ForwardStart.code RoundTrip.code)
def cost (heap rows total : ℕ) : ℕ :=
  2^180*(2^(total+rows)+1)*(Traversal.width heap rows total+2)^3+
    2^110*(Traversal.width heap rows total+2)^2+RoundTrip.cost heap rows total

theorem executes (v : ℕ→ℕ) (heap rows total : ℕ) (root : Targets.Target rows total)
    (setup : Setup v heap rows total)
    (hsource : IncidenceEncoding.Separated (v 803) ((v 801)*(v 802)) (v 804) ((v 801)*(v 802)))
    (hforward : v 803+(v 801)*(v 802) ≤ heap) (hbackward : v 804+(v 801)*(v 802) ≤ heap)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hb : NatAssign.Bank Division.ids v s.val) (hz : PrivateVisit.Clean s)
    (h839 : Blank s.val 839) (h831 : Blank s.val 831) (h830 : Blank s.val 830)
    (hf : Storage.Permutation rows total root s.val.memory (v 803) (v 802))
    (hi : Storage.Permutation rows total root.symm s.val.memory (v 804) (v 802))
    (leaves : AssemblyTraversal.Frontier heap rows total root 0 s.val.memory) :
    ∃steps t,Executes input tape code steps s t ∧ steps ≤ cost heap rows total ∧
      LabelsAt heap (2^(total+rows)) (total+rows+1) 0 rows total root t.val.memory ∧
      PrivateVisit.Clean t ∧ Blank t.val 839 ∧ Blank t.val 831 ∧ Blank t.val 830 ∧
      (∀i∈Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,Blank t.val i) ∧
      Traversal.Frame s.val t.val ∧
      Memory.Frame heap ((2^total-1)*stride (2^(total+rows)) (total+rows+1)) s.val.memory t.val.memory := by
  cases total with
  | zero => have hh:=setup.controller.positive;omega
  | succ columns =>
      have hn : v 801=2*2^(columns+rows) := by
        simpa only [show columns+1+rows=columns+rows+1 by omega,pow_succ'] using setup.countWord
      have hw : v 802=columns+rows+2 := by have hh:=setup.widthWord;omega
      have hq : ∀i∈NodeSetup.controls,(v i).bits.length ≤ Traversal.width heap rows (columns+1) := by
        intro i hi
        exact setup.controller.words i ((show NodeSetup.controls⊆Division.ids by decide) hi)
      obtain ⟨c0,a,e0,h0,ba,za,a839,out,fa,ma⟩:=Root.executes v rows columns
        (Traversal.width heap rows (columns+1)) hn hw hq root hsource
        (by simpa only [setup.heapWord] using hforward) (by simpa only [setup.heapWord] using hbackward)
        input tape s hb hz h839 hf hi
      rw [setup.heapWord,setup.countWord,setup.widthWord] at out ma
      have rootPrefix:=Traversal.Prefix.root heap rows columns root a.val.memory out
      have global : Memory.Frame heap ((2^(columns+1)-1)*stride (2^(columns+1+rows)) (columns+1+rows+1))
          s.val.memory a.val.memory := by
        apply Traversal.memory_widen heap rows (columns+1) 0 1 (by omega) (by simp)
        simpa only [pow_zero,Nat.sub_self,block,Nat.zero_mul,Nat.add_zero,Nat.one_mul] using ma
      have leavesA:=AssemblyTraversal.Frontier.preserve heap rows (columns+1) root _ _ global leaves
      have firstFrame : Traversal.Frame s.val a.val :=
        ⟨fa.inputHead,fa.randomCursor,fa.output,fun i hi h37 _ hp _ _ => fa.tapes i hi h37 hp⟩
      have a831:=RationalAccumulator.blank_of_eq (fa.tapes 831 (by omega) (by omega) (by decide)) h831
      have a830:=RationalAccumulator.blank_of_eq (fa.tapes 830 (by omega) (by omega) (by decide)) h830
      obtain ⟨c1,b,e1,h1,bb,zb,b839,f1⟩:=ForwardStart.executes v (Traversal.width heap rows (columns+1))
        setup.controller.two (by have hh:=setup.controller.width;omega) setup.controller.zero
        setup.controller.words input tape a ba za a839
      have b831:=RationalAccumulator.blank_of_eq (f1.tapes 831 (by decide)) a831
      have b830:=RationalAccumulator.blank_of_eq (f1.tapes 830 (by decide)) a830
      obtain ⟨c2,t,e2,h2,st,t830⟩:=RoundTrip.executes (ForwardStart.output v) heap rows (columns+1) root
        setup.controller.forward ((ForwardStart.output_other v 810 (by decide)).trans setup.controller.depth)
        input tape b bb zb b839 b831 b830
        (by simpa only [f1.memory] using rootPrefix) (by simpa only [f1.memory] using leavesA)
      have quotientClean : ∀i∈Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,Blank t.val i := by
        intro i hi
        apply (RationalAccumulator.zero_word_iff_blank _ _).mp
        have h:=st.bank i (Finset.mem_union_right _ hi)
        have hzero:=AssemblyTraversal.quotient_zero _ (columns+1)
          (RoundTrip.reverse_setup (ForwardStart.output v) heap rows (columns+1) setup.controller.forward).zero
          (columns+1) i hi
        simpa only [hzero] using h
      refine ⟨c0+(c1+c2),t,e0.seq (e1.seq e2),?_,st.root_labels,st.clean,st.scratch,st.counter,t830,
        quotientClean,(firstFrame.trans (Traversal.Frame.of_level (Level.Frame.of_arithmetic f1))).trans st.frame,?_⟩
      · rw [setup.countWord] at h0
        dsimp only [cost]
        omega
      · have firstMemory : Memory.Frame heap
            ((2^(columns+1)-1)*stride (2^(columns+1+rows)) (columns+1+rows+1)) s.val.memory b.val.memory := by
          simpa only [f1.memory] using global
        exact firstMemory.trans st.memory

#print axioms executes
end Maxwell.Cost.RoutingPorts.Complete.Tree.RootRun
