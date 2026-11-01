import Maxwell.Continuum.ParameterSourceExecution
import Maxwell.Continuum.ParameterOuterPhysicalData
import Maxwell.Cost.Structured.TapeBlockSwap

/-! Reuse the outer search beside the retained source archive by moving
its low scratch bank into fresh tapes. Source input words keep their ports. -/
noncomputable section
namespace Maxwell.Continuum.Parameters.SourceOuter
open Maxwell.Cost Maxwell.Cost.Structured
open RationalAccumulator (Word Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 2600000

def relocation : Equiv.Perm ℕ := TapeBlockSwap.permutation 4 1257 3000 (by decide)
def initial (κ η e : ℕ) (S : Source.SparseSystem) (precision i : ℕ) : ℕ :=
  if i∈SourcePrepare.ports then SourceExecution.values κ η e S precision i else 0
def inputWidth (κ η e : ℕ) (S : Source.SparseSystem) (precision : ℕ) : ℕ :=
  ∑i∈SourcePrepare.ports,(SourceExecution.values κ η e S precision i).bits.length

theorem initial_width (κ η e : ℕ) (S : Source.SparseSystem) (precision i : ℕ) :
    (initial κ η e S precision i).bits.length ≤ inputWidth κ η e S precision := by
  by_cases hi : i∈SourcePrepare.ports
  · simp only [initial,ite_eq_left hi,inputWidth]
    exact Finset.single_le_sum
      (f:=fun j=>(SourceExecution.values κ η e S precision j).bits.length)
      (fun j _=>Nat.zero_le _) hi
  · simp only [initial,ite_eq_right hi,show (0:ℕ).bits.length=0 by decide,Nat.zero_le]

theorem input_fixed (i : ℕ) (hi : i∈SourcePrepare.ports) : relocation i=i := by
  apply TapeBlockSwap.apply_outside
  all_goals simp only [SourcePrepare.ports,SourceBudgetMachine.outputs,
    Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hi
  all_goals omega

theorem renamed_tape (s : Store) (i : ℕ) :
    (s.renameTapes relocation).val.tapes i=s.val.tapes (relocation i) := by
  simp only [Store.renameTapes,BitRAMState.renameTapes,Function.comp_apply,relocation,TapeBlockSwap.symm]

theorem bank {κ η e : ℕ} {S : Source.SparseSystem} {precision : ℕ} {s : Store}
    (h : SourceExecution.Result κ η e S precision s) :
    NatAssign.Bank OuterMachine.ids (initial κ η e S precision) (s.renameTapes relocation).val := by
  intro i hi
  by_cases hp : i∈SourcePrepare.ports
  · rw [initial,ite_eq_left hp]
    exact RationalAccumulator.word_of_eq ((renamed_tape s i).trans (congrArg s.val.tapes (input_fixed i hp)))
      (h.bank i hp)
  · rw [initial,ite_eq_right hp]
    apply (RationalAccumulator.zero_word_iff_blank _ _).mpr
    suffices fresh : Blank s.val (relocation i) by
      obtain ⟨origin,word⟩:=fresh
      exact ⟨origin,(renamed_tape s i).trans word⟩
    have low:=OuterMachine.ids_ge i hi
    have upper : i<2300 := by
      have bound : ∀j∈OuterMachine.ids,j<2300 := by decide +kernel
      exact bound i hi
    by_cases small : i<1261
    · have moved : relocation i=i+3000 := TapeBlockSwap.apply_inside 4 1257 3000 (by decide) i (by omega) small
      rw [moved]
      apply h.fresh _ (by omega)
      have bound : ∀j∈SourcePrepare.work,j≤2340 := by decide +kernel
      intro hin
      have := bound (i+3000) hin
      omega
    · have fixed : relocation i=i := TapeBlockSwap.apply_outside 4 1257 3000 (by decide) i
        (Or.inr (by omega)) (Or.inl (by omega))
      rw [fixed]
      apply h.fresh _ (by omega)
      have separate : ∀j∈OuterMachine.ids,j∉SourcePrepare.ports→1261≤ j→j∉SourcePrepare.work := by decide +kernel
      exact separate i hi hp (by omega)

theorem scratch {κ η e : ℕ} {S : Source.SparseSystem} {precision : ℕ} {s : Store}
    (h : SourceExecution.Result κ η e S precision s) :
    ∀i,i<5→Blank (s.renameTapes relocation).val i := by
  intro i hi
  by_cases small : i<4
  · apply RationalAccumulator.blank_of_eq ((renamed_tape s i).trans (congrArg s.val.tapes ?_)) (h.scratch i small)
    exact TapeBlockSwap.apply_outside 4 1257 3000 (by decide) i (Or.inl small) (Or.inl (by omega))
  · have eq : i=4 := by omega
    subst i
    obtain ⟨origin,word⟩:=h.fresh 3004 (by decide) (by decide +kernel)
    exact ⟨origin,(renamed_tape s 4).trans word⟩

#print axioms bank
#print axioms scratch
end Maxwell.Continuum.Parameters.SourceOuter
