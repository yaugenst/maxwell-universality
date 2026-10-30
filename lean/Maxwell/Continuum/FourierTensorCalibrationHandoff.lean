import Maxwell.Continuum.FourierTensorComputedWorkspace
import Maxwell.Continuum.RationalDataflowStoredParts

/-! The normalized calibration output becomes the tensor input through
five charged word copies. Both headers then describe the same literal
array; its memory is preserved exactly. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime.CalibrationHandoff
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow PartArray
open RationalAccumulator (Blank)
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

def targets : List ℕ := [200,202,203,204,205]
def changed : Finset ℕ := targets.toFinset

private def copyCode : List ℕ→Code
  | [] => .skip
  | i::rest => .seq (WordReplace.code (i+10) i) (copyCode rest)

def code : Code := copyCode targets

private theorem copy_executes (ports : List ℕ) (word : ℕ→List Bool) (W : ℕ)
    (hp : ∀i∈ports,200 ≤ i ∧ i<210) (hw : ∀i∈ports,(word i).length≤W)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : ∀i∈ports,BankArray.Word s.val (i+10) (word i))
    (ho : WordCleanup.Bounded ports W s.val) :
    ∃cost t,Executes input tape (copyCode ports) cost s t ∧
      cost≤ports.length*(21*W+21)+1 ∧
      (∀i∈ports,BankArray.Word t.val i (word i)) ∧
      BinaryPrecision.Frame ports.toFinset s.val t.val := by
  induction ports generalizing s with
  | nil => exact ⟨1,s,Executes.skip s,by simp,by simp,BinaryPrecision.Frame.refl _ _⟩
  | cons i rest ih =>
    have hi := hp i (by simp)
    obtain ⟨xs,hxs,hx⟩ := ho i (by simp)
    obtain ⟨u,ex,wu,fu⟩ := WordReplace.executes (i+10) i (by omega) input tape
      (word i) xs s (hs i (by simp)) hx
    have frame := StoredParts.copy_frame fu
    have hs' : ∀j∈rest,BankArray.Word u.val (j+10) (word j) := by
      intro j hj
      have hj' := hp j (List.mem_cons_of_mem _ hj)
      exact BankArray.word_of_eq (frame.tapes (j+10) (by simp;omega))
        (hs j (List.mem_cons_of_mem _ hj))
    have ho' : WordCleanup.Bounded rest W u.val := by
      intro j hj
      by_cases hji : j=i
      · subst j
        exact ⟨word i,hw i (by simp),wu⟩
      · obtain ⟨ys,hys,hy⟩ := ho j (List.mem_cons_of_mem _ hj)
        exact ⟨ys,hys,BankArray.word_of_eq (frame.tapes j (by simpa using hji)) hy⟩
    obtain ⟨cr,t,er,hcr,wt,ft⟩ := ih
      (fun j hj => hp j (List.mem_cons_of_mem _ hj))
      (fun j hj => hw j (List.mem_cons_of_mem _ hj)) u hs' ho'
    refine ⟨6*xs.length+15*(word i).length+21+cr,t,ex.seq er,?_,?_,
      (frame.mono (by simp)).trans (ft.mono (by simp))⟩
    · have hiw := hw i (by simp)
      simp only [List.length_cons]
      nlinarith only [hxs,hiw,hcr]
    · intro j hj
      rcases List.mem_cons.mp hj with hji|hj
      · subst j
        by_cases him : i∈rest
        · exact wt i him
        · exact BankArray.word_of_eq (ft.tapes i (by simpa using him)) wu
      · exact wt j hj

def words {n : ℕ} (a : Table n) (i : ℕ) : List Bool :=
  if i=200 then a.width else if i=202 then a.basePositive else if i=203 then a.baseNegative
  else if i=204 then a.baseDenominator else a.clock

theorem executes {n : ℕ} (a : Table n) (H : ℕ)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (ha : a.OutputReady s)
    (hold : WordCleanup.Bounded targets H s.val) :
    ∃cost t,Executes input tape code cost s t ∧
      cost≤128*(H+ModeAllocation.tableWidth a+1) ∧
      a.Ready t ∧ a.OutputReady t ∧ BinaryPrecision.Frame changed s.val t.val := by
  have hmeta := ModeAllocation.tableWidth_spec a
  have source : ∀i∈targets,BankArray.Word s.val (i+10) (words a i) := by
    intro i hi
    simp only [targets,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl
    · simpa [words] using ha.width
    · simpa [words] using ha.basePositive
    · simpa [words] using ha.baseNegative
    · simpa [words] using ha.baseDenominator
    · simpa [words] using ha.clock
  have width : ∀i∈targets,(words a i).length≤H+ModeAllocation.tableWidth a := by
    intro i hi
    simp only [targets,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl
    · simpa [words] using hmeta.width.trans (Nat.le_add_left (ModeAllocation.tableWidth a) H)
    · simpa [words] using hmeta.basePositive.trans (Nat.le_add_left (ModeAllocation.tableWidth a) H)
    · simpa [words] using hmeta.baseNegative.trans (Nat.le_add_left (ModeAllocation.tableWidth a) H)
    · simpa [words] using hmeta.baseDenominator.trans (Nat.le_add_left (ModeAllocation.tableWidth a) H)
    · simpa [words] using hmeta.clock.trans (Nat.le_add_left (ModeAllocation.tableWidth a) H)
  have old : WordCleanup.Bounded targets (H+ModeAllocation.tableWidth a) s.val := by
    intro i hi
    obtain ⟨xs,hxs,hx⟩ := hold i hi
    exact ⟨xs,hxs.trans (Nat.le_add_right _ _),hx⟩
  obtain ⟨cost,t,ex,hcost,wt,ft⟩ := copy_executes targets (words a)
    (H+ModeAllocation.tableWidth a) (by decide) width input tape s source old
  have small (i : ℕ) (hi : i<200) : t.val.tapes i=s.val.tapes i := by
    apply ft.tapes
    simp only [List.mem_toFinset,targets,List.mem_cons,List.not_mem_nil,or_false]
    omega
  have scratch : BankArray.Scratch t.val :=
    ⟨RationalAccumulator.blank_of_eq (small 0 (by decide)) ha.scratch.1,
     RationalAccumulator.blank_of_eq (small 1 (by decide)) ha.scratch.2.1,
     RationalAccumulator.blank_of_eq (small 2 (by decide)) ha.scratch.2.2.1,
     RationalAccumulator.blank_of_eq (small 3 (by decide)) ha.scratch.2.2.2.1,
     RationalAccumulator.blank_of_eq (small 5 (by decide)) ha.scratch.2.2.2.2.1,
     RationalAccumulator.blank_of_eq (small 6 (by decide)) ha.scratch.2.2.2.2.2.1,
     RationalAccumulator.blank_of_eq (small 8 (by decide)) ha.scratch.2.2.2.2.2.2.1,
     RationalAccumulator.blank_of_eq (small 9 (by decide)) ha.scratch.2.2.2.2.2.2.2⟩
  have seven := RationalAccumulator.blank_of_eq (small 7 (by decide)) ha.seven
  have output : a.OutputReady t := by
    apply ha.transfer ft.memory _ scratch seven
    intro i hi
    apply ft.tapes
    simp only [List.mem_toFinset,targets,List.mem_cons,List.not_mem_nil,or_false]
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    omega
  refine ⟨cost,t,ex,?_,?_,output,ft⟩
  · simp only [targets,List.length_cons,List.length_nil] at hcost
    omega
  · refine ⟨scratch,seven,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · simpa [words] using wt 200 (by simp [targets])
    · simpa [words] using wt 202 (by simp [targets])
    · simpa [words] using wt 203 (by simp [targets])
    · simpa [words] using wt 204 (by simp [targets])
    · simpa [words] using wt 205 (by simp [targets])
    · simpa only [ft.memory] using ha.positive
    · simpa only [ft.memory] using ha.negative
    · simpa only [ft.memory] using ha.denominator

#print axioms executes
end Maxwell.Continuum.Profile.WaveMachine.Runtime.CalibrationHandoff
