import Maxwell.Continuum.CalibrationSeedRootIndex
import Maxwell.Cost.SelectedParameters.AllComparisons
import Maxwell.Cost.Structured.NatAssign.Difference

/-! Fixed natural plans for one of the eight sparse root-cache terms. -/
namespace Maxwell.Continuum.Calibration.SeedRoot
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 3000000
set_option maxRecDepth 12000

def extra : Finset ℕ := Finset.Icc 750 799
def retained : Finset ℕ := extra\Finset.Icc 756 771
def ids : Finset ℕ := SelectedParameters.Compare.ids extra
def workspace : Finset ℕ := {0,1,2,3}∪ids
def coordinates (v : ℕ→ℕ) : Fin 3→ℕ := ![v 753,v 754,v 755]
def coordinatePlan (s : Corner.Parity) (j : Fin 3) : List NatAssign.Instruction :=
  [.copy 750 (756+j.val),
   .multiply (if ![s.1,s.2.1,s.2.2] j then 770 else 768) (756+j.val),
   .add 752 (756+j.val),.copy (756+j.val) (759+j.val),.add 771 (759+j.val),
   .literal (762+j.val) 0]
def prepare (s : Corner.Parity) (part : Fin 2) : List NatAssign.Instruction :=
  [.literal 768 2,.literal 769 1,.literal 770 3,.copy 751 771,.multiply 768 771,
   .copy 771 767,.add 769 767,.literal 766 part.val,.literal 35 0,.literal 36 0]++
    coordinatePlan s 0++coordinatePlan s 1++coordinatePlan s 2
def prepared (s : Corner.Parity) (part : Fin 2) (v : ℕ→ℕ) := NatAssign.values (prepare s part) v
def tests : List SelectedParameters.AllComparisons.Test :=
  [((756,769),(753,769)),((753,769),(759,769)),
   ((757,769),(754,769)),((754,769),(760,769)),
   ((758,769),(755,769)),((755,769),(761,769))]
def differences (v : ℕ→ℕ) : ℕ→ℕ :=
  Function.update (Function.update (Function.update v 762 (v 753-v 756))
    763 (v 754-v 757)) 764 (v 755-v 758)
def finish : List NatAssign.Instruction :=
  [.copy 764 765,.multiply 767 765,.add 763 765,.multiply 767 765,
   .add 762 765,.multiply 768 765,.add 766 765]
def finished (v : ℕ→ℕ) := NatAssign.values finish (differences v)

theorem ids_lower (i : ℕ) (hi : i∈ids) : 4 ≤ i := by
  simp only [ids,SelectedParameters.Compare.ids,extra,Finset.mem_union,
    Finset.mem_Icc,Finset.mem_insert,Finset.mem_singleton] at hi
  omega
theorem extra_lower (i : ℕ) (hi : i∈extra) : 40 ≤ i := by
  exact (by decide : 40≤750).trans (Finset.mem_Icc.mp hi).1
theorem retained_bounds (i : ℕ) (hi : i∈retained) :
    750 ≤ i ∧ i≤799 ∧ (i≤755 ∨ 772 ≤ i) := by
  simp only [retained,extra,Finset.mem_sdiff,Finset.mem_Icc] at hi
  omega
theorem coordinatePlan_valid (s : Corner.Parity) (j : Fin 3) :
    ∀a∈coordinatePlan s j,a.Valid ids := by
  obtain ⟨a,b,c⟩ := s
  cases a <;> cases b <;> cases c <;> fin_cases j <;>
    simp [coordinatePlan,NatAssign.Instruction.Valid,ids,SelectedParameters.Compare.ids,extra]
theorem prepare_valid (s : Corner.Parity) (part : Fin 2) :
    ∀a∈prepare s part,a.Valid ids := by
  simp only [prepare,List.mem_append]
  intro a ha
  rcases ha with ((h|h)|h)|h
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      simp [NatAssign.Instruction.Valid,ids,SelectedParameters.Compare.ids,extra]
  · exact coordinatePlan_valid s 0 a h
  · exact coordinatePlan_valid s 1 a h
  · exact coordinatePlan_valid s 2 a h
theorem finish_valid : ∀a∈finish,a.Valid ids := by
  simp [finish,NatAssign.Instruction.Valid,ids,SelectedParameters.Compare.ids,extra]
theorem tests_valid : ∀q∈tests,SelectedParameters.AllComparisons.Valid extra q := by
  simp [tests,SelectedParameters.AllComparisons.Valid,extra]

theorem prepared_fields (s : Corner.Parity) (part : Fin 2) (v : ℕ→ℕ)
    (half : v 752=v 750/2) :
    (∀j : Fin 3,prepared s part v (756+j.val)=base (v 750) s j ∧
      prepared s part v (759+j.val)=base (v 750) s j+2*v 751 ∧
      prepared s part v (762+j.val)=0) ∧
    coordinates (prepared s part v)=coordinates v ∧
    prepared s part v 767=2*v 751+1 ∧ prepared s part v 766=part.val ∧
    prepared s part v 768=2 ∧ prepared s part v 769=1 ∧
    prepared s part v 35=0 ∧ prepared s part v 36=0 := by
  obtain ⟨a,b,c⟩ := s
  cases a <;> cases b <;> cases c <;>
    simp [prepared,prepare,coordinatePlan,NatAssign.values,NatAssign.Instruction.update,
      NatAssign.Instruction.target,NatAssign.Instruction.value,coordinates,base,half,
      Fin.forall_fin_succ,Nat.add_comm]

theorem prepared_failed (s : Corner.Parity) (part : Fin 2) (v : ℕ→ℕ)
    (half : v 752=v 750/2) :
    tests.any (SelectedParameters.AllComparisons.failed (prepared s part v))=
      decide (¬inside (v 750) (v 751) s (coordinates v)) := by
  have fields := prepared_fields s part v half
  have coords := congrFun fields.2.1
  simp only [tests,List.any_cons,List.any_nil,Bool.or_false,
    SelectedParameters.AllComparisons.failed,fields.2.2.2.2.2.1,Nat.cast_one,div_one]
  have c0 := coords 0
  have c1 := coords 1
  have c2 := coords 2
  change prepared s part v 753=v 753 at c0
  change prepared s part v 754=v 754 at c1
  change prepared s part v 755=v 755 at c2
  have h0 := fields.1 0
  have h1 := fields.1 1
  have h2 := fields.1 2
  norm_num only [Fin.val_zero,Fin.val_one,Fin.val_two,Nat.reduceAdd] at h0 h1 h2
  rw [c0,c1,c2,h0.1,h0.2.1,h1.1,h1.2.1,h2.1,h2.2.1]
  simp only [Nat.cast_lt,←Bool.decide_or,decide_eq_decide]
  simp [inside,Fin.forall_fin_succ,coordinates]
  omega

theorem finished_index (s : Corner.Parity) (part : Fin 2) (v : ℕ→ℕ)
    (half : v 752=v 750/2) :
    finished (prepared s part v) 765=index (v 750) (v 751) s (coordinates v) part := by
  have fields := prepared_fields s part v half
  have coords := congrFun fields.2.1
  have c0 := coords 0
  have c1 := coords 1
  have c2 := coords 2
  change prepared s part v 753=v 753 at c0
  change prepared s part v 754=v 754 at c1
  change prepared s part v 755=v 755 at c2
  have h0 := fields.1 0
  have h1 := fields.1 1
  have h2 := fields.1 2
  norm_num only [Fin.val_zero,Fin.val_one,Fin.val_two,Nat.reduceAdd] at h0 h1 h2
  simp [finished,finish,differences,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.target,NatAssign.Instruction.value,c0,c1,c2,h0.1,h1.1,h2.1,
    fields.2.2.1,fields.2.2.2.1,fields.2.2.2.2.1,index,flat,digit,coordinates]
  ring

theorem prepared_keep (parity : Corner.Parity) (part : Fin 2) (v : ℕ→ℕ)
    (i : ℕ) (hi : i∈retained) : prepared parity part v i=v i := by
  apply NatAssign.values_preserves
  have bounds := retained_bounds i hi
  simp [prepare,coordinatePlan,NatAssign.Instruction.target]
  omega

theorem finished_keep (v : ℕ→ℕ) (i : ℕ) (hi : i∈retained) : finished v i=v i := by
  have bounds := retained_bounds i hi
  rw [finished,NatAssign.values_preserves finish _ i (by
    simp [finish,NatAssign.Instruction.target];omega)]
  simp [differences,show i≠762 by omega,show i≠763 by omega,show i≠764 by omega]

theorem finished_congr (v w : ℕ→ℕ) (keep : ∀i∈extra,v i=w i) : finished v 765=finished w 765 := by
  simp [finished,finish,differences,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.target,NatAssign.Instruction.value,
    keep 753 (by decide),keep 754 (by decide),keep 755 (by decide),
    keep 756 (by decide),keep 757 (by decide),keep 758 (by decide),
    keep 766 (by decide),keep 767 (by decide),keep 768 (by decide)]

#print axioms prepared_failed
#print axioms finished_index
end Maxwell.Continuum.Calibration.SeedRoot
