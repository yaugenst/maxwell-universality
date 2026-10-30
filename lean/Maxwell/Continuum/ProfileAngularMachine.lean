import Maxwell.Continuum.ProfileScalarFrames
import Maxwell.Continuum.ProfileRawProducer
import Maxwell.Continuum.PhaseRuntimeDataflowCost
import Maxwell.Continuum.RationalDataflowTrace

/-! One fixed runtime sample evaluator for the literal profile DFT.
Register 0 is its rational argument; register 4 receives the exact glue
approximation. The surrounding bank and stored precision remain reusable. -/
namespace Maxwell.Continuum.Profile.Runtime
open RationalDataflow RationalTaylor Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

def angularMiddle : List Instruction := [.literal 2 1,.binary .sub 3 2 1]
def angularAfterPhase (P : ℕ) (v : ℕ→Parts) : ℕ→Parts :=
  Function.update v 1 (Phase.result cosineSigns 1 (P+4) (v 0))
def angularAfterMiddle (P : ℕ) (v : ℕ→Parts) : ℕ→Parts :=
  evaluate angularMiddle (angularAfterPhase P v)
def angularValues (P : ℕ) (v : ℕ→Parts) : ℕ→Parts :=
  Function.update (angularAfterMiddle P v) 4 (angularParts P (v 0))
def angularCode : Code := .seq (Phase.Runtime.code RationalTaylor.Runtime.cosineCycle 1 0)
  (.seq (program angularMiddle) (Glue.code 4 3))
def angularWorkspace (S : Finset ℕ) : Finset ℕ := Phase.Runtime.workspace S∪Glue.workspace S
def angularMiddleWidth (P W : ℕ) : ℕ := W+2^68*(1+(P+4)+W+12)^4+10
def angularCost (P W : ℕ) : ℕ := Phase.Runtime.costBound 1 (P+4) W+
  (2*operationCost (angularMiddleWidth P W)+1)+Glue.costBound (P+4) (angularMiddleWidth P W)

theorem angularMiddle_value (P : ℕ) (v : ℕ→Parts) :
    angularAfterMiddle P v 3=(Parts.literal 1).sub (Phase.result cosineSigns 1 (P+4) (v 0)) := by
  simp [angularAfterMiddle,angularMiddle,evaluate,Instruction.update,BinaryOp.eval,angularAfterPhase]

theorem angularValues_output (P : ℕ) (v : ℕ→Parts) : angularValues P v 4=angularParts P (v 0) := by
  simp only [angularValues,Function.update_self]

theorem angularValues_value (P : ℕ) (v : ℕ→Parts) (hx : (v 0).Valid) :
    (angularValues P v 4).value=(angularApprox (v 0).value P).center := by
  rw [angularValues_output,angularParts_value P (v 0) hx]

theorem angularMiddle_valid (S : Finset ℕ) (hS : ({0,1,2,3,4}:Finset ℕ)⊆S) :
    ∀a∈angularMiddle,a.Valid S := by
  have h1 := hS (show 1∈({0,1,2,3,4}:Finset ℕ) by decide)
  have h2 := hS (show 2∈({0,1,2,3,4}:Finset ℕ) by decide)
  have h3 := hS (show 3∈({0,1,2,3,4}:Finset ℕ) by decide)
  simpa [angularMiddle,Instruction.Valid] using And.intro h2 (And.intro h3 (And.intro h2 h1))

theorem angular_middle_width (S : Finset ℕ) (P W : ℕ) (v : ℕ→Parts) (hw : WidthBank S W v)
    (h0 : 0∈S) : WidthTrace S (angularMiddleWidth P W) angularMiddle (angularAfterPhase P v) := by
  have hp := Phase.result_width cosineSigns 1 (P+4) W (v 0) (hw 0 h0)
  have hb : W≤angularMiddleWidth P W := by unfold angularMiddleWidth;omega
  have hphase : WidthBank S (angularMiddleWidth P W) (angularAfterPhase P v) :=
    (hw.mono hb).update 1 (hp.mono (by unfold angularMiddleWidth;omega))
  have hone := (Parts.literal_width RationalWords.width_one).mono
    (show 1≤angularMiddleWidth P W by unfold angularMiddleWidth;omega)
  have hmid := hphase.update 2 hone
  have hsub := ((Parts.literal_width RationalWords.width_one).sub hp).mono
    (show 1+(2^68*(1+(P+4)+W+12)^4)+1≤angularMiddleWidth P W by unfold angularMiddleWidth;omega)
  refine ⟨hphase,hone,hmid,trivial,?_⟩
  simpa [Instruction.update,angularAfterPhase,BinaryOp.eval,WidthTrace] using
    hmid.update 3 hsub

theorem angular_executes (S : Finset ℕ) (hS : ({0,1,2,3,4}:Finset ℕ)⊆S)
    (P W : ℕ) (v : ℕ→Parts) (hw : WidthBank S W v) (hW : 10≤W)
    (hP : (P+4).bits.length≤W) (hx : (v 0).Valid)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hr : Ready S v s)
    (hphase : Phase.Runtime.Clean s.val) (hglue : Glue.Clean s.val)
    (hQword : Word s.val 652 1) (hPword : Word s.val 653 (P+4)) (hGword : Word s.val 640 (P+4)) :
    ∃cost t,Executes input tape angularCode cost s t ∧ cost≤angularCost P W ∧
      Ready S (angularValues P v) t ∧ Phase.Runtime.Clean t.val ∧ Glue.Clean t.val ∧
      Word t.val 652 1 ∧ Word t.val 653 (P+4) ∧ Word t.val 640 (P+4) ∧
      BinaryPrecision.Frame (angularWorkspace S) s.val t.val := by
  have hm (i : ℕ) (hi : i≤4) : i∈S := hS (by simp only [Finset.mem_insert,Finset.mem_singleton];omega)
  obtain ⟨c0,s0,e0,h0,r0,z0,q0,p0,f0⟩ := Phase.Runtime.executes S RationalTaylor.Runtime.cosineCycle
    1 (P+4) 1 0 (hm 1 (by decide)) (hm 0 (by decide)) v W hw
    (by simpa only [Nat.one_bits,List.length_singleton] using (show 1≤W by omega)) hP hW
    input tape s hr hphase hQword hPword
  rw [RationalTaylor.Runtime.cosineCycle_signs] at r0
  change Ready S (angularAfterPhase P v) s0 at r0
  have zg0 := glueClean_after_phase hglue z0 r0 f0
  have g0 := phase_preserves_glue_precision S s s0 f0 (P+4) hGword
  obtain ⟨c1,s1,e1,h1,r1,f1⟩ := program_executes S angularMiddle (angularMiddle_valid S hS)
    (angularAfterPhase P v) (angularMiddleWidth P W) (angular_middle_width S P W v hw (hm 0 (by decide)))
    input tape s0 r0
  change Ready S (angularAfterMiddle P v) s1 at r1
  have zp1 := phaseClean_arithmetic z0 r1 f1
  have zg1 := glueClean_arithmetic zg0 r1 f1
  have keep (i : ℕ) (hi : 107 ≤ i ∧ i < 1000) : s1.val.tapes i=s0.val.tapes i :=
    f1.tapes i (RationalDataflow.outside_workspace S i (Or.inr hi))
  have q1 := word_of_eq (keep 652 (by decide)) q0
  have p1 := word_of_eq (keep 653 (by decide)) p0
  have g1 := word_of_eq (keep 640 (by decide)) g0
  have hw1 : WidthBank S (angularMiddleWidth P W) (angularAfterMiddle P v) :=
    (angular_middle_width S P W v hw (hm 0 (by decide))).2.2.2.2
  have hx1 : (angularAfterMiddle P v 3).Valid := by
    rw [angularMiddle_value]
    exact Parts.sub_valid (Parts.literal_valid 1) (Phase.result_valid _ _ _ _ hx)
  obtain ⟨c2,t,e2,h2,r2,z2,g2,f2⟩ := Glue.executes S (P+4) 4 3 (hm 4 (by decide)) (hm 3 (by decide))
    (angularAfterMiddle P v) (angularMiddleWidth P W) hw1
    (hP.trans (by unfold angularMiddleWidth;omega)) (by unfold angularMiddleWidth;omega) hx1
    input tape s1 r1 zg1 g1
  rw [angularMiddle_value] at r2
  change Ready S (angularValues P v) t at r2
  have zp2 := phaseClean_after_glue zp1 z2 r2 f2
  refine ⟨c0+(c1+c2),t,e0.seq (e1.seq e2),?_,r2,zp2,z2,
    glue_preserves_phase_parameter S s1 t f2 652 1 (Or.inl rfl) q1,
    glue_preserves_phase_parameter S s1 t f2 653 (P+4) (Or.inr rfl) p1,g2,?_⟩
  · change c1≤2*operationCost (angularMiddleWidth P W)+1 at h1
    unfold angularCost
    omega
  · apply (f0.mono Finset.subset_union_left).trans
    apply (f1.mono ?_).trans (f2.mono Finset.subset_union_right)
    intro i hi
    apply Finset.mem_union_left
    rcases Finset.mem_union.mp hi with hi|hi
    · exact Finset.mem_union_left _ hi
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ hi)

#print axioms angular_executes
end Maxwell.Continuum.Profile.Runtime
