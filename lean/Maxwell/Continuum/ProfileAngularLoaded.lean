import Maxwell.Continuum.ProfileAngularMachine
import Maxwell.Continuum.PhaseRuntimeDataflowLoaded

/-! The profile sample's stored parameters are loaded by fixed instructions.
Each call restores the phase/glue cleanup invariant for the next DFT term. -/
namespace Maxwell.Continuum.Profile.Runtime
open RationalDataflow RationalTaylor Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 3500000

def angularLoadCode : Code := .seq (WordReplace.code 667 652)
  (.seq (WordReplace.code 668 653) (WordReplace.code 668 640))
def angularLoadedCode : Code := .seq angularLoadCode angularCode

private theorem parameter_outside (S : Finset ℕ) (i : ℕ) (hi : i∈({640,652,653}:Finset ℕ)) :
    i∉RationalDataflow.workspace S := by
  apply RationalDataflow.outside_workspace S i
  simp only [Finset.mem_insert,Finset.mem_singleton] at hi
  omega

private theorem clean_parameter_copy {s t : Store} {i : ℕ} (hi : i∈({640,652,653}:Finset ℕ))
    (hp : Phase.Runtime.Clean s.val) (hg : Glue.Clean s.val)
    (hf : WordReplace.Frame i s.val t.val) : Phase.Runtime.Clean t.val ∧ Glue.Clean t.val := by
  constructor
  · intro j hj
    apply blank_of_eq (hf.2.2.2.2.2.1 j _) (hp j hj)
    intro he
    subst j
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl|rfl|rfl
    · exact (show (640:ℕ)∉PhaseMachine.Runtime.ids by decide)
        (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hj))
    · exact (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).1 rfl
    · exact (Finset.mem_erase.mp hj).1 rfl
  · intro j hj
    apply blank_of_eq (hf.2.2.2.2.2.1 j _) (hg j hj)
    intro he
    subst j
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl|rfl|rfl
    · exact (Finset.mem_erase.mp hj).1 rfl
    · exact (show (652:ℕ)∉GlueMachine.Runtime.ids by decide) (Finset.mem_of_mem_erase hj)
    · exact (show (653:ℕ)∉GlueMachine.Runtime.ids by decide) (Finset.mem_of_mem_erase hj)

private theorem parameter_copy_frame {S : Finset ℕ} {s t : Store} {i : ℕ}
    (hi : i∈({640,652,653}:Finset ℕ)) (f : WordReplace.Frame i s.val t.val) :
    BinaryPrecision.Frame (angularWorkspace S) s.val t.val := by
  refine ⟨f.1,f.2.1,f.2.2.1,f.2.2.2.1,f.2.2.2.2.1,?_⟩
  intro j hj
  apply f.2.2.2.2.2.1 j
  intro he
  subst j
  apply hj
  simp only [Finset.mem_insert,Finset.mem_singleton] at hi
  rcases hi with rfl|rfl|rfl
  · exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_union_right _ (by decide)))
  · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_union_right _ (by decide)))
  · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_union_right _ (by decide)))

theorem angular_load_executes (S : Finset ℕ) (P Qold Nold Gold W : ℕ)
    (hP : (P+4).bits.length≤W) (hQ : Qold.bits.length≤W) (hN : Nold.bits.length≤W)
    (hG : Gold.bits.length≤W) (_hW : 1≤W) (v : ℕ→Parts)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hr : Ready S v s)
    (hp : Phase.Runtime.Clean s.val) (hg : Glue.Clean s.val)
    (hqo : Word s.val 652 Qold) (hno : Word s.val 653 Nold) (hgo : Word s.val 640 Gold)
    (hone : Word s.val 667 1) (hpn : Word s.val 668 (P+4)) :
    ∃cost t,Executes input tape angularLoadCode cost s t ∧ cost≤96*(W+1) ∧
      Ready S v t ∧ Phase.Runtime.Clean t.val ∧ Glue.Clean t.val ∧
      Word t.val 652 1 ∧ Word t.val 653 (P+4) ∧ Word t.val 640 (P+4) ∧
      BinaryPrecision.Frame (angularWorkspace S) s.val t.val := by
  obtain ⟨s0,e0,q0,f0⟩ := WordReplace.executes 667 652 (by decide) input tape (1:ℕ).bits Qold.bits s hone hqo
  have r0 := hr.wordReplace_frame (parameter_outside S 652 (by decide)) f0
  obtain ⟨p0,g0⟩ := clean_parameter_copy (by decide : (652:ℕ)∈{640,652,653}) hp hg f0
  obtain ⟨s1,e1,n1,f1⟩ := WordReplace.executes 668 653 (by decide) input tape (P+4).bits Nold.bits s0
    (word_of_eq (f0.2.2.2.2.2.1 668 (by decide)) hpn) (word_of_eq (f0.2.2.2.2.2.1 653 (by decide)) hno)
  have r1 := r0.wordReplace_frame (parameter_outside S 653 (by decide)) f1
  obtain ⟨p1,g1⟩ := clean_parameter_copy (by decide : (653:ℕ)∈{640,652,653}) p0 g0 f1
  obtain ⟨t,e2,g2,f2⟩ := WordReplace.executes 668 640 (by decide) input tape (P+4).bits Gold.bits s1
    (word_of_eq ((f1.2.2.2.2.2.1 668 (by decide)).trans (f0.2.2.2.2.2.1 668 (by decide))) hpn)
    (word_of_eq ((f1.2.2.2.2.2.1 640 (by decide)).trans (f0.2.2.2.2.2.1 640 (by decide))) hgo)
  have r2 := r1.wordReplace_frame (parameter_outside S 640 (by decide)) f2
  obtain ⟨p2,z2⟩ := clean_parameter_copy (by decide : (640:ℕ)∈{640,652,653}) p1 g1 f2
  refine ⟨_,t,e0.seq (e1.seq e2),?_,r2,p2,z2,
    word_of_eq ((f2.2.2.2.2.2.1 652 (by decide)).trans (f1.2.2.2.2.2.1 652 (by decide))) q0,
    word_of_eq (f2.2.2.2.2.2.1 653 (by decide)) n1,g2,
    (parameter_copy_frame (S := S) (by decide) f0).trans
      ((parameter_copy_frame (by decide) f1).trans (parameter_copy_frame (by decide) f2))⟩
  simp only [Nat.one_bits,List.length_singleton]
  omega

theorem angular_loaded_executes (S : Finset ℕ) (hS : ({0,1,2,3,4}:Finset ℕ)⊆S)
    (P Qold Nold Gold W : ℕ) (v : ℕ→Parts) (hw : WidthBank S W v) (hW : 10≤W)
    (hP : (P+4).bits.length≤W) (hQ : Qold.bits.length≤W) (hN : Nold.bits.length≤W)
    (hG : Gold.bits.length≤W) (hx : (v 0).Valid)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hr : Ready S v s)
    (hp : Phase.Runtime.Clean s.val) (hg : Glue.Clean s.val)
    (hqo : Word s.val 652 Qold) (hno : Word s.val 653 Nold) (hgo : Word s.val 640 Gold)
    (hone : Word s.val 667 1) (hpn : Word s.val 668 (P+4)) :
    ∃cost t,Executes input tape angularLoadedCode cost s t ∧ cost≤96*(W+1)+angularCost P W ∧
      Ready S (angularValues P v) t ∧ Phase.Runtime.Clean t.val ∧ Glue.Clean t.val ∧
      Word t.val 652 1 ∧ Word t.val 653 (P+4) ∧ Word t.val 640 (P+4) ∧
      BinaryPrecision.Frame (angularWorkspace S) s.val t.val := by
  obtain ⟨c0,s0,e0,h0,r0,p0,g0,q0,n0,gn0,f0⟩ := angular_load_executes S P Qold Nold Gold W
    hP hQ hN hG (by omega) v input tape s hr hp hg hqo hno hgo hone hpn
  obtain ⟨c1,t,e1,h1,r1,p1,g1,q1,n1,gn1,f1⟩ := angular_executes S hS P W v hw hW hP hx
    input tape s0 r0 p0 g0 q0 n0 gn0
  exact ⟨c0+c1,t,e0.seq e1,by omega,r1,p1,g1,q1,n1,gn1,f0.trans f1⟩

#print axioms angular_loaded_executes
end Maxwell.Continuum.Profile.Runtime
