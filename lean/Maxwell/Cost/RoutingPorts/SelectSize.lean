import Maxwell.Cost.RoutingPorts.Size
import Maxwell.Cost.RoutingPorts.Rename

namespace Maxwell.Cost.RoutingPorts.Size
open Structured RationalAccumulator

def banks : Finset ℕ := Finset.Icc 700 707 ∪ Finset.Icc 740 746
def work : Finset ℕ := {0,1,2,3} ∪ banks
def code : Code := .call (rawCode.compile.renameTapes relocation)

theorem frame_renamed {s t : Store}
    (hf : BinaryPrecision.Frame (SelectedParameters.Geometric.workspace ∪ {520,521,522,523})
      (s.renameTapes relocation.symm).val t.val) :
    BinaryPrecision.Frame work s.val (t.renameTapes relocation).val := by
  refine ⟨hf.address,hf.inputHead,hf.memory,hf.randomCursor,hf.output,?_⟩
  intro i hi
  have ho : shiftBank i ∉ SelectedParameters.Geometric.workspace ∪ {520,521,522,523} := by
    simp only [work,banks,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,
      Finset.mem_Icc,not_or] at hi
    simp only [SelectedParameters.Geometric.workspace,Finset.mem_union,Finset.mem_insert,
      Finset.mem_singleton]
    dsimp only [shiftBank]
    split_ifs <;> simp only [not_or]
    all_goals (repeat' constructor)
    all_goals (try omega)
    all_goals trace_state
  have h := hf.tapes (shiftBank i) ho
  change t.val.tapes (shiftBank i)=s.val.tapes i
  simpa only [renamed_tape,shiftBank_involutive i] using h

/-- The exponent and enclosing square are produced by an actual finite
search from the stored vertex count. Only private tapes are changed. -/
theorem executes (vertices : ℕ) (hv : 0 < vertices)
    (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (hvertices : Word s.val 141 vertices) (hs : NatAssign.Scratch s.val)
    (hfresh : ∀ i ∈ banks, Blank s.val i) :
    ∃ cost t, Executes input tape code cost s t ∧ cost ≤ rawPrice vertices+1 ∧
      Word t.val 705 (4^Nat.clog 4 vertices) ∧ Word t.val 706 (Nat.clog 4 vertices) ∧
      NatAssign.Scratch t.val ∧ BinaryPrecision.Frame work s.val t.val := by
  let v := s.renameTapes relocation.symm
  have vb : NatAssign.Bank ids (initial vertices) v.val := by
    intro i hi
    by_cases hi141 : i=141
    · subst i
      change Word s.val 141 vertices
      exact hvertices
    · have hzero : initial vertices i=0 := by simp [initial,hi141]
      rw [hzero]
      apply (zero_word_iff_blank _ _).mpr
      have hm : shiftBank i∈banks := by
        simp only [ids,SelectedParameters.Geometric.ids,SelectedParameters.Geometric.extra,
          Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hi
        simp only [banks,Finset.mem_union,Finset.mem_Icc]
        dsimp only [shiftBank]
        split_ifs <;> omega
      change Blank s.val (shiftBank i)
      exact hfresh (shiftBank i) hm
  have vs : NatAssign.Scratch v.val := by
    intro i hi
    exact blank_of_eq (show v.val.tapes i=s.val.tapes i by
      change s.val.tapes (shiftBank i)=s.val.tapes i
      rw [shiftBank_fixed i (by omega) (by omega) (by omega) (by omega)]) (hs i hi)
  obtain ⟨cost,u,eu,hcost,hu,fu⟩ := raw_executes vertices hv input tape v vb vs
  let t := u.renameTapes relocation
  have get (i : ℕ) (hi : i∈SelectedParameters.Geometric.ids) := hu.bank i hi
  have hw : Word t.val 705 (4^Nat.clog 4 vertices) := by
    have h := get 525 (by decide)
    change Word u.val 525 (4^Nat.clog 4 vertices)
    simpa [SelectedParameters.Geometric.values] using h
  have hn : Word t.val 706 (Nat.clog 4 vertices) := by
    have h := get 526 (by decide)
    change Word u.val 526 (Nat.clog 4 vertices)
    simpa [SelectedParameters.Geometric.values] using h
  have scratch : NatAssign.Scratch t.val := by
    intro i hi
    exact blank_of_eq (show t.val.tapes i=u.val.tapes i by
      change u.val.tapes (shiftBank i)=u.val.tapes i
      rw [shiftBank_fixed i (by omega) (by omega) (by omega) (by omega)]) (hu.scratch i hi)
  refine ⟨cost+1,t,?_,by omega,hw,hn,scratch,frame_renamed fu⟩
  simpa only [code,v,Store.renameTapes_symm] using eu.renamed_call relocation

end Maxwell.Cost.RoutingPorts.Size
