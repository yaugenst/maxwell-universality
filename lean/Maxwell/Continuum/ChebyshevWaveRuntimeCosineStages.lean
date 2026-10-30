import Maxwell.Continuum.ChebyshevWaveRuntimeCosineFrame
import Maxwell.Continuum.ChebyshevWaveRuntimeCosineCorrect

/-! Actual fixed save, restart and correction stages around the Fourier loops. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalDataflow RationalTaylor
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

def savePairCode : Code := .seq (StoredParts.saveCode 690 8) (StoredParts.saveCode 693 9)
def restorePairCode : Code := .seq (StoredParts.restoreCode 690 2) (StoredParts.restoreCode 693 3)
def clearPairCode : Code := .seq (StoredParts.clearCode 690) (StoredParts.clearCode 693)

theorem stored_arithmetic_frame {base : ℕ} (hb : base=690 ∨ base=693) {x : Parts} {s t : Store}
    (h : StoredParts.Stored base x s.val)
    (f : BinaryPrecision.Frame (RationalDataflow.workspace ids) s.val t.val) :
    StoredParts.Stored base x t.val :=
  stored_sum_frame hb h (f.mono (arithmetic_subset_evaluation.trans (Finset.subset_insert _ _)))

theorem save_pair_executes (Q P B : ℕ) (v : ℕ→Parts) (hw : WidthBank ids B v)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : LoopReady Q P v s)
    (hz : ∀i∈savedPorts,Blank s.val i) :
    ∃cost t,Executes input tape savePairCode cost s t ∧ cost ≤ 126*(B+1) ∧
      LoopReady Q P v t ∧ StoredParts.Stored 690 (v 8) t.val ∧
      StoredParts.Stored 693 (v 9) t.val ∧ BinaryPrecision.Frame savedPorts s.val t.val := by
  have hzero : (⟨0,0,0⟩:Parts).Width B := by simp [Parts.Width]
  have z690 := StoredParts.Stored.blank (fun i hi => hz i (Finset.mem_union_left _ hi))
  have z693 := StoredParts.Stored.blank (fun i hi => hz i (Finset.mem_union_right _ hi))
  obtain ⟨c1,s1,e1,hc1,_,w1,f1⟩ := StoredParts.save_executes ids 690 8 (by decide) (by decide)
    (by decide) v _ B (hw 8 (by decide)) hzero input tape s hs.ready z690
  have r1 := hs.external_frame f1 (by intro i hi;simp only [StoredParts.ports,Finset.mem_insert,Finset.mem_singleton] at hi;omega)
  have z693' := z693.frame f1 (by decide : Disjoint (StoredParts.ports 693) (StoredParts.ports 690))
  obtain ⟨c2,t,e2,hc2,_,w2,f2⟩ := StoredParts.save_executes ids 693 9 (by decide) (by decide)
    (by decide) v _ B (hw 9 (by decide)) hzero input tape s1 r1.ready z693'
  refine ⟨c1+c2,t,e1.seq e2,by omega,
    r1.external_frame f2 (by intro i hi;simp only [StoredParts.ports,Finset.mem_insert,Finset.mem_singleton] at hi;omega),
    w1.frame f2 (by decide),w2,(f1.mono Finset.subset_union_left).trans (f2.mono Finset.subset_union_right)⟩

theorem restore_pair_executes (Q P B : ℕ) (v : ℕ→Parts) (x y : Parts) (hw : WidthBank ids B v)
    (hx : x.Width B) (hy : y.Width B) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : LoopReady Q P v s) (hxs : StoredParts.Stored 690 x s.val) (hys : StoredParts.Stored 693 y s.val) :
    ∃cost t,Executes input tape restorePairCode cost s t ∧ cost ≤ 126*(B+1) ∧
      LoopReady Q P (Function.update (Function.update v 2 x) 3 y) t ∧
      StoredParts.Stored 690 x t.val ∧ StoredParts.Stored 693 y t.val ∧
      BinaryPrecision.Frame (RationalDataflow.workspace ids) s.val t.val := by
  have h2 : cellPorts 2⊆RationalDataflow.workspace ids :=
    (cell_mem (by decide : 2∈ids)).trans Finset.subset_union_right
  have h3 : cellPorts 3⊆RationalDataflow.workspace ids :=
    (cell_mem (by decide : 3∈ids)).trans Finset.subset_union_right
  obtain ⟨c1,s1,e1,hc1,r1,x1,f1⟩ := StoredParts.restore_executes ids 690 2 (by decide) (by decide)
    v x B (hw 2 (by decide)) hx input tape s hs.ready hxs
  have lr1 := hs.arithmetic_frame (f1.mono h2) r1
  have y1 := stored_arithmetic_frame (Or.inr rfl) hys (f1.mono h2)
  obtain ⟨c2,t,e2,hc2,r2,y2,f2⟩ := StoredParts.restore_executes ids 693 3 (by decide) (by decide)
    (Function.update v 2 x) y B (by simpa using hw 3 (by decide)) hy input tape s1 lr1.ready y1
  exact ⟨c1+c2,t,e1.seq e2,by omega,lr1.arithmetic_frame (f2.mono h3) r2,
    stored_arithmetic_frame (Or.inl rfl) x1 (f2.mono h3),y2,(f1.mono h2).trans (f2.mono h3)⟩

theorem clear_pair_executes (Q P B : ℕ) (v : ℕ→Parts) (x y : Parts)
    (hx : x.Width B) (hy : y.Width B) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : LoopReady Q P v s) (hxs : StoredParts.Stored 690 x s.val) (hys : StoredParts.Stored 693 y s.val) :
    ∃cost t,Executes input tape clearPairCode cost s t ∧ cost ≤ 36*B+24 ∧
      LoopReady Q P v t ∧ (∀i∈savedPorts,Blank t.val i) ∧
      BinaryPrecision.Frame savedPorts s.val t.val := by
  obtain ⟨c1,s1,e1,hc1,z1,f1⟩ := StoredParts.clear_executes 690 x B hx input tape s hxs
  have r1 := hs.external_frame f1 (by intro i hi;simp only [StoredParts.ports,Finset.mem_insert,Finset.mem_singleton] at hi;omega)
  have y1 := hys.frame f1 (by decide)
  obtain ⟨c2,t,e2,hc2,z2,f2⟩ := StoredParts.clear_executes 693 y B hy input tape s1 y1
  refine ⟨c1+c2,t,e1.seq e2,by omega,
    r1.external_frame f2 (by intro i hi;simp only [StoredParts.ports,Finset.mem_insert,Finset.mem_singleton] at hi;omega),?_,
    (f1.mono Finset.subset_union_left).trans (f2.mono Finset.subset_union_right)⟩
  intro i hi
  rcases Finset.mem_union.mp hi with hi|hi
  · apply blank_of_eq (f2.tapes i _) (z1 i hi)
    exact fun hm => Finset.disjoint_left.mp
      (by decide : Disjoint (StoredParts.ports 690) (StoredParts.ports 693)) hi hm
  · exact z2 i hi

theorem restart_program_width (B : ℕ) : programWidth restartInstructions (fun _ => B) ≤ 4*(B+1) := by
  simp [restartInstructions,programWidth,RationalDataflow.Instruction.widthUpdate,
    RationalDataflow.Instruction.resultWidth,Parts.literal]
  omega

theorem restart_executes (Q P B : ℕ) (v : ℕ→Parts) (hw : WidthBank ids B v)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : LoopReady Q P v s) :
    ∃cost t,Executes input tape (program restartInstructions) cost s t ∧
      cost ≤ 12*operationCost (4*(B+1))+1 ∧ LoopReady Q P (restartValues v) t ∧
      BinaryPrecision.Frame (RationalDataflow.workspace ids) s.val t.val := by
  have ht := inferred_widthTrace ids restartInstructions restartInstructions_valid (fun _ => B) v hw _
    (hw.mono (by omega)) (restart_program_width B)
  obtain ⟨c,t,e,hc,r,f⟩ := program_executes ids restartInstructions restartInstructions_valid v _ ht input tape s hs.ready
  exact ⟨c,t,e,by simpa only [show restartInstructions.length=12 by rfl] using hc,
    hs.arithmetic_frame f r,f⟩

theorem finish_literals (B : ℕ) (hB : 2 ≤ B) : finishControl.LiteralsFit B := by
  have hz : (Parts.literal 0).Width B := (show (Parts.literal (0:ℚ)).Width 1 from by unfold Parts.Width Parts.literal;decide).mono (by omega)
  have hh : (Parts.literal (1/2)).Width B := (show (Parts.literal (1/2:ℚ)).Width 2 from by norm_num [Parts.Width,Parts.literal];decide).mono hB
  simp [finishControl,Control.prepend,finishInstructions,halveControl,Control.LiteralsFit,
    RationalDataflow.Instruction.LiteralFits,hz]
  simpa using hh

theorem finish_executes (Q P B : ℕ) (v : ℕ→Parts) (hw : WidthBank ids B v) (hg : Good ids v)
    (hB : 2 ≤ B) (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : LoopReady Q P v s) :
    ∃cost t,Executes input tape finishControl.code cost s t ∧ cost ≤ 8*operationCost (256*(B+1))+1 ∧
      LoopReady Q P (finishControl.evaluate v) t ∧
      WidthBank ids (256*(B+1)) (finishControl.evaluate v) ∧
      BinaryPrecision.Frame (RationalDataflow.workspace ids) s.val t.val := by
  have ht := finishControl.automatic_widthTrace ids finishControl_valid v B hw (finish_literals B hB)
  have steps : finishControl.steps=8 := rfl
  rw [steps] at ht
  change finishControl.WidthTrace ids (256*(B+1)) v at ht
  obtain ⟨c,t,e,hc,r,f⟩ := finishControl.executes ids finishControl_valid v _ ht hg
    (finishControl_admissible v) input tape s hs.ready
  exact ⟨c,t,e,by simpa only [steps] using hc,hs.arithmetic_frame f r,ht.result,f⟩

#print axioms save_pair_executes
#print axioms restore_pair_executes
#print axioms finish_executes
end Maxwell.Continuum.Profile.WaveMachine.Runtime
