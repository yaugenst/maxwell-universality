import Maxwell.Continuum.MachinFinalBank
import Maxwell.Continuum.RationalArctanRuntimeExtension

/-! The two Machin arctangent calls use a preserved runtime term count.
The countdown and both arctangent index tapes are restored after each call. -/
namespace Maxwell.Continuum.Machin.Runtime
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalTaylor
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

def workspace : Finset ℕ := allWorkspace∪{619,628,632}
structure AuxReady (N : ℕ) (s : BitRAMState) : Prop where
  index : Blank s 619
  two : Blank s 628
  count : Blank s 632
  terms : Word s 631 (N+6)

theorem AuxReady.frame {N : ℕ} {s t : BitRAMState} (h : AuxReady N s)
    (hf : BinaryPrecision.Frame allWorkspace s t) : AuxReady N t := by
  exact ⟨blank_of_eq (hf.tapes 619 (by decide)) h.index,
    blank_of_eq (hf.tapes 628 (by decide)) h.two,
    blank_of_eq (hf.tapes 632 (by decide)) h.count,
    word_of_eq (hf.tapes 631 (by decide)) h.terms⟩

def arctanCall : Code := .seq (WordReplace.code 631 632) (RationalArctan.Runtime.cleanProgram 632)
def callCost (N : ℕ) : ℕ :=
  15*(N+6).bits.length+21+RationalArctan.Runtime.cleanCost (N+6) 8 (N+6).bits.length

theorem arctan_call (N : ℕ) (v : ℕ→ℕ)
    (hw : ∀i∈RationalArctan.ids,(v i).bits.length≤8)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : NatAssign.Bank allIds v s.val) (hz : NatAssign.Scratch s.val) (ha : AuxReady N s.val) :
    ∃cost t,Executes input tape arctanCall cost s t ∧ cost≤callCost N ∧
      NatAssign.Bank allIds (RationalArctan.extendedValues v negativeSigns (N+6)) t.val ∧
      NatAssign.Scratch t.val ∧ AuxReady N t.val ∧ BinaryPrecision.Frame workspace s.val t.val := by
  obtain ⟨u,e0,hu,f0⟩ := WordReplace.executes 631 632 (by decide) input tape (N+6).bits [] s
    ha.terms ((zero_word_iff_blank _ _).mpr ha.count)
  have fc : BinaryPrecision.Frame {632} s.val u.val := by
    refine ⟨f0.1,f0.2.1,f0.2.2.1,f0.2.2.2.1,f0.2.2.2.2.1,?_⟩
    intro i hi
    exact f0.2.2.2.2.2.1 i (by simpa using hi)
  have bu : NatAssign.Bank allIds v u.val := by
    intro i hi
    have hn : i≠632 := by
      intro he;subst i;exact (show 632∉allIds by decide) hi
    exact word_of_eq (fc.tapes i (by simpa using hn)) (hs i hi)
  have zu : NatAssign.Scratch u.val := by
    intro i hi
    exact blank_of_eq (fc.tapes i (by simp only [Finset.mem_singleton];omega)) (hz i hi)
  obtain ⟨origin,hword⟩ := hu
  obtain ⟨c1,t,e1,h1,bt,zt,zc,zi,z2,f1⟩ := RationalArctan.Runtime.clean_extended allIds ids_subset
    632 (N+6) 8 (by decide) (by decide) (by
      intro i hi hn
      simp only [allIds,RationalArctan.ids,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hi hn
      simp only [RationalArctan.Runtime.loopWorkspace,RationalArctan.Runtime.workspace,
        RationalArctan.workspace,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
      omega) v (by decide) hw input tape (N+6).bits origin u (addressValue_bits _)
    hword bu zu (blank_of_eq (fc.tapes 619 (by decide)) ha.index)
    (blank_of_eq (fc.tapes 628 (by decide)) ha.two)
  refine ⟨15*(N+6).bits.length+21+c1,t,?_,by unfold callCost;omega,bt,zt,
    ⟨zi,z2,zc,?_⟩,(fc.mono (by decide)).trans (f1.mono (by decide))⟩
  · simpa only [arctanCall,List.length_nil,Nat.mul_zero,Nat.zero_add] using e0.seq e1
  · exact word_of_eq (f1.tapes 631 (by decide))
      (word_of_eq (fc.tapes 631 (by decide)) ha.terms)

#print axioms arctan_call
end Maxwell.Continuum.Machin.Runtime
