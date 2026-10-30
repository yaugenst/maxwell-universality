import Maxwell.Continuum.ChebyshevWaveFactor

/-! Runtime loading of an axis frequency and tensor index from preserved
logical registers. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalDataflow RationalTaylor
open RationalDataflow.PartArray
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

theorem FactorReady.arithmetic_frame {n D Q N : ℕ} {a : Table n} {b : Table (2*D)}
    {v w : ℕ→Parts} {s t : Store} (h : FactorReady a Q N b v s)
    (f : BinaryPrecision.Frame (RationalDataflow.workspace tensorBank) s.val t.val)
    (hr : Ready tensorBank w t) : FactorReady a Q N b w t := by
  refine ⟨hr,h.phase.arithmetic_frame f hr,h.floor.arithmetic_frame f,?_,
    h.source.arithmetic_frame tensorBank f hr.2,output_tensor_frame h.output f hr.2,
    blank_of_eq (f.tapes 144 (outside_workspace tensorBank 144 (by decide))) h.power,
    blank_of_eq (f.tapes 146 (outside_workspace tensorBank 146 (by decide))) h.powerCount,
    blank_of_eq (f.tapes 680 (outside_workspace tensorBank 680 (by decide))) h.inner,?_⟩
  · intro i hi
    have hd : Disjoint setupIds (RationalDataflow.workspace tensorBank) := by decide
    exact word_of_eq (f.tapes i (fun hm => Finset.disjoint_left.mp hd hi hm)) (h.setup i hi)
  · intro i hi
    have hr := savedPorts_range i hi
    exact blank_of_eq (f.tapes i (outside_workspace tensorBank i (by omega))) (h.saved i hi)

theorem FactorReady.index_frame {n D Q N : ℕ} {a : Table n} {b : Table (2*D)}
    {v : ℕ→Parts} {s t : Store} (h : FactorReady a Q N b v s)
    (f : WordReplace.Frame 1048 s.val t.val) : FactorReady a Q N b v t := by
  have r := h.ready.wordReplace_frame (by decide : 1048∉RationalDataflow.workspace tensorBank) f
  have fa : BinaryPrecision.Frame (RationalDataflow.workspace (insert 16 tensorBank)) s.val t.val :=
    (StoredParts.copy_frame f).mono (by decide)
  have source := h.source.arithmetic_frame (insert 16 tensorBank) fa r.2
  have output : b.OutputReady t := by
    apply h.output.transfer f.2.2.1 _ source.scratch source.seven
    intro i hi
    apply f.2.2.2.2.2.1 i
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    omega
  refine ⟨r,?_,?_,?_,source,output,
    blank_of_eq (f.2.2.2.2.2.1 144 (by decide)) h.power,
    blank_of_eq (f.2.2.2.2.2.1 146 (by decide)) h.powerCount,
    blank_of_eq (f.2.2.2.2.2.1 680 (by decide)) h.inner,?_⟩
  · intro i hi
    have hip : i∈PhaseMachine.Runtime.ids := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hi)
    have hn : i≠1048 := by intro he;subst i;exact (by decide : 1048∉PhaseMachine.Runtime.ids) hip
    exact blank_of_eq (f.2.2.2.2.2.1 i hn) (h.phase i hi)
  · refine ⟨blank_of_eq (f.2.2.2.2.2.1 4 (by decide)) h.floor.1,?_⟩
    intro i hi
    have hn : i≠1048 := by
      simp only [DyadicFloor.extraIds,NaturalQuotient.workPorts,Finset.mem_union,
        Finset.mem_insert,Finset.mem_singleton] at hi
      omega
    exact blank_of_eq (f.2.2.2.2.2.1 i hn) (h.floor.2 i hi)
  · intro i hi
    have hn : i≠1048 := by intro he;subst i;exact (by decide : 1048∉setupIds) hi
    exact word_of_eq (f.2.2.2.2.2.1 i hn) (h.setup i hi)
  · intro i hi
    have hr := savedPorts_range i hi
    exact blank_of_eq (f.2.2.2.2.2.1 i (by omega)) (h.saved i hi)

def factorLoadCode (frequency index : ℕ) : Code := .seq (partsCopyCode frequency 10)
  (WordReplace.code (positivePort index) 1048)
def factorLoadCost (W : ℕ) : ℕ := RationalDataflow.stageCost W+21*W+21

theorem factorLoad_executes {n D Q N : ℕ} (a : Table n) (b : Table (2*D))
    (W frequency index oldIndex j : ℕ) (hf : frequency∈tensorBank) (hf10 : frequency≠10)
    (hi : index∈tensorBank) (hi17 : 17 ≤ index) (v : ℕ→Parts)
    (hw : WidthBank tensorBank W v) (hj : (v index).positive=j) (hold : oldIndex.bits.length ≤ W)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : FactorReady a Q N b v s)
    (hindex : Word s.val 1048 oldIndex) :
    ∃cost t,Executes input tape (factorLoadCode frequency index) cost s t ∧ cost ≤ factorLoadCost W ∧
      FactorReady a Q N b (Function.update v 10 (v frequency)) t ∧
      WidthBank tensorBank W (Function.update v 10 (v frequency)) ∧ Word t.val 1048 j := by
  obtain ⟨c0,s0,e0,h0,r0,w0,f0⟩ := partsCopy_executes tensorBank frequency 10 hf (by decide) hf10
    v W hw input tape s hs.ready
  have ready0 := hs.arithmetic_frame f0 r0
  have old0 := word_of_eq (f0.tapes 1048 (by decide)) hindex
  have index0 : Word s0.val (positivePort index) j := by
    have h := r0.1 (positivePort index) (cell_mem hi (by simp [cellPorts]))
    simpa only [dataValues_positive,Function.update_of_ne (by omega : index≠10),hj] using h
  obtain ⟨t,e1,index1,f1⟩ := WordReplace.executes (positivePort index) 1048
    (by unfold positivePort;omega) input tape j.bits oldIndex.bits s0 index0 old0
  refine ⟨c0+(6*oldIndex.bits.length+15*j.bits.length+21),t,e0.seq e1,?_,
    ready0.index_frame f1,w0,index1⟩
  have hjw : j.bits.length ≤ W := by simpa only [hj] using (hw index hi).1
  unfold factorLoadCost
  omega

#print axioms factorLoad_executes
end Maxwell.Continuum.Profile.WaveMachine.Runtime
