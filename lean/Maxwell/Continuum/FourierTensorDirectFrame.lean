import Maxwell.Continuum.FourierTensorDirectTerm

/-! The fixed wave calls preserve the separate tensor accumulator, and
the tensor arithmetic preserves all private wave-generator state. -/
namespace Maxwell.Cost

theorem BitRAMInstruction.tapesBelow_mono {a : BitRAMInstruction} {A B : ℕ}
    (h : a.tapesBelow A=true) (hab : A ≤ B) : a.tapesBelow B=true := by
  cases a <;> simp only [tapesBelow,decide_eq_true_eq] at h ⊢ <;> omega

theorem BitRAM.tapesBelow_mono {c : BitRAM} {A B : ℕ}
    (h : c.tapesBelow A=true) (hab : A ≤ B) : c.tapesBelow B=true := by
  apply List.all_eq_true.mpr
  intro a ha
  exact BitRAMInstruction.tapesBelow_mono (List.all_eq_true.mp h a ha) hab

namespace Structured
theorem Code.tapesBelow_mono {c : Code} {A B : ℕ}
    (h : c.tapesBelow A=true) (hab : A ≤ B) : c.tapesBelow B=true := by
  induction c with
  | skip => rfl
  | call c => exact c.tapesBelow_mono h hab
  | seq a b ha hb =>
    simp only [tapesBelow,Bool.and_eq_true] at h ⊢
    exact ⟨ha h.1,hb h.2⟩
  | branch _ a b ha hb =>
    simp only [tapesBelow,Bool.and_eq_true] at h ⊢
    exact ⟨ha h.1,hb h.2⟩
  | loop _ body ih => exact ih h
end Structured
end Maxwell.Cost

namespace Maxwell.Continuum.Profile.WaveMachine.Runtime
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalDataflow
open RationalDataflow.PartArray
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536

theorem axisCode_tapesBelow (i : Fin 3) : (axisCode i).tapesBelow 1096=true := by
  have hp := Code.tapesBelow_mono producer_tapesBelow (by decide : 1048 ≤ 1096)
  have hc := Code.tapesBelow_mono cacheSelect_tapesBelow (by decide : 1049 ≤ 1096)
  simp only [axisCode,factorCode,selectedProducerCode,Code.tapesBelow,Bool.and_eq_true]
  refine ⟨?_,⟨hp,hc⟩,?_⟩
  · fin_cases i <;> decide
  · fin_cases i <;> decide

theorem axesCode_tapesBelow : axesCode.tapesBelow 1096=true := by
  simp only [axesCode,Code.tapesBelow,Bool.and_eq_true]
  exact ⟨axisCode_tapesBelow 0,axisCode_tapesBelow 1,axisCode_tapesBelow 2⟩

def accumulatorValues (low old : ℕ→Parts) (i : ℕ) : Parts :=
  if i∈tensorBank then low i else old i

theorem axes_accumulator_ready {input : List Bool} {tape : ℕ→Bool} {cost : ℕ}
    {s t : Store} {v w : ℕ→Parts} (e : Executes input tape axesCode cost s t)
    (hs : Ready termBank v s) (ht : Ready tensorBank w t) :
    Ready termBank (accumulatorValues w v) t := by
  apply ht.partition hs
  intro j hj hjt i hi
  have hj32 : j=32 := by simpa only [termBank,Finset.mem_insert,hjt,or_false] using hj
  subst j
  apply e.tapesBelow axesCode_tapesBelow
  simp only [cellPorts,Finset.mem_insert,Finset.mem_singleton] at hi
  rcases hi with rfl|rfl|rfl <;> decide

theorem output_term_frame {n : ℕ} {a : Table n} {s t : Store} (h : a.OutputReady s)
    (f : BinaryPrecision.Frame (RationalDataflow.workspace termBank) s.val t.val)
    (hz : NatAssign.Scratch t.val) : a.OutputReady t := by
  have keep (i : ℕ) (hi : i∈({5,6,7,8,9,37,210,212,213,214,215}:Finset ℕ)) :=
    f.tapes i (by
      have hd : Disjoint ({5,6,7,8,9,37,210,212,213,214,215}:Finset ℕ)
          (RationalDataflow.workspace termBank) := by decide
      exact fun hm => Finset.disjoint_left.mp hd hi hm)
  have scratch : BankArray.Scratch t.val :=
    ⟨hz 0 (by decide),hz 1 (by decide),hz 2 (by decide),hz 3 (by decide),
      blank_of_eq (keep 5 (by decide)) h.scratch.2.2.2.2.1,
      blank_of_eq (keep 6 (by decide)) h.scratch.2.2.2.2.2.1,
      blank_of_eq (keep 8 (by decide)) h.scratch.2.2.2.2.2.2.1,
      blank_of_eq (keep 9 (by decide)) h.scratch.2.2.2.2.2.2.2⟩
  apply h.transfer f.memory _ scratch (blank_of_eq (keep 7 (by decide)) h.seven)
  intro i hi
  apply keep
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl <;> decide

theorem FactorReady.term_frame {n D Q N : ℕ} {a : Table n} {b : Table (2*D)}
    {v w : ℕ→Parts} {s t : Store} (h : FactorReady a Q N b v s)
    (f : BinaryPrecision.Frame (RationalDataflow.workspace termBank) s.val t.val)
    (hr : Ready termBank w t) : FactorReady a Q N b w t := by
  refine ⟨hr.restrict (by simp [termBank]),h.phase.arithmetic_frame f hr,
    h.floor.arithmetic_frame f,?_,h.source.arithmetic_frame termBank f hr.2,
    output_term_frame h.output f hr.2,
    blank_of_eq (f.tapes 144 (outside_workspace termBank 144 (by decide))) h.power,
    blank_of_eq (f.tapes 146 (outside_workspace termBank 146 (by decide))) h.powerCount,
    blank_of_eq (f.tapes 680 (outside_workspace termBank 680 (by decide))) h.inner,?_⟩
  · intro i hi
    have hd : Disjoint setupIds (RationalDataflow.workspace termBank) := by decide
    exact word_of_eq (f.tapes i (fun hm => Finset.disjoint_left.mp hd hi hm)) (h.setup i hi)
  · intro i hi
    have hr := savedPorts_range i hi
    exact blank_of_eq (f.tapes i (outside_workspace termBank i (by omega))) (h.saved i hi)

#print axioms axes_accumulator_ready
#print axioms FactorReady.term_frame
end Maxwell.Continuum.Profile.WaveMachine.Runtime
