import Maxwell.Continuum.MachinData
import Maxwell.Continuum.RationalArctanExtension

/-! Concrete register data and arithmetic stages for the Machin evaluator. -/

namespace Maxwell.Continuum.Machin
open Maxwell.Cost Maxwell.Cost.Structured RationalTaylor
set_option maxHeartbeats 2500000
set_option maxRecDepth 4096

def allIds : Finset ℕ := RationalArctan.ids∪{620,621,622,623,624,625,626,627}
def allWorkspace : Finset ℕ := {0,1,2,3}∪allIds

def initialValues (b i : ℕ) : ℕ := if i=610 then 1 else if i=611 then b else 0
def firstValues (N : ℕ) : ℕ→ℕ := RationalArctan.extendedValues (initialValues 5) negativeSigns (N+6)
def preparedValues (N i : ℕ) : ℕ :=
  if i=620 then positive 5 N else if i=621 then negative 5 N else
  if i=622 then denominator 5 N else initialValues 239 i
def secondValues (N : ℕ) : ℕ→ℕ := RationalArctan.extendedValues (preparedValues N) negativeSigns (N+6)

def prologue : List NatAssign.Instruction :=
  [.literal 610 1,.literal 611 5,.literal 612 0,.literal 613 0,.literal 614 0,
   .literal 615 0,.literal 616 0,.literal 617 0,.literal 618 0,
   .literal 620 0,.literal 621 0,.literal 622 0,.literal 623 0,.literal 624 0,
   .literal 625 0,.literal 626 0,.literal 627 0]

def saveFirst : List NatAssign.Instruction :=
  [.copy 612 620,.copy 613 621,.copy 614 622,.literal 611 239,
   .literal 612 0,.literal 613 0,.literal 614 0,.literal 615 0,
   .literal 616 0,.literal 617 0,.literal 618 0]

def combine : List NatAssign.Instruction :=
  [.copy 620 623,.multiply 614 623,.literal 626 16,.multiply 626 623,
   .copy 613 626,.multiply 622 626,.literal 627 4,.multiply 627 626,.add 626 623,
   .copy 621 624,.multiply 614 624,.literal 626 16,.multiply 626 624,
   .copy 612 626,.multiply 622 626,.multiply 627 626,.add 626 624,
   .copy 622 625,.multiply 614 625,.literal 626 0,.literal 627 0]

theorem allIds_ge (i : ℕ) (hi : i∈allIds) : 4 ≤ i := by
  simp only [allIds,RationalArctan.ids,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hi
  omega

theorem ids_subset : RationalArctan.ids⊆allIds := Finset.subset_union_left

theorem outside_workspace (i : ℕ) (hi : i∈allIds) (hn : i∉RationalArctan.ids) :
    i∉RationalArctan.workspace := by
  simp only [allIds,RationalArctan.ids,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hi hn
  simp only [RationalArctan.workspace,Finset.mem_insert,Finset.mem_singleton]
  omega

theorem stages_valid : (∀ a∈prologue, a.Valid allIds) ∧
    (∀ a∈saveFirst, a.Valid allIds) ∧ (∀ a∈combine, a.Valid allIds) := by
  simp [prologue,saveFirst,combine,NatAssign.Instruction.Valid,allIds,RationalArctan.ids]

theorem prologue_values (v : ℕ→ℕ) (i : ℕ) (hi : i∈allIds) :
    NatAssign.values prologue v i=initialValues 5 i := by
  have hlo : 610 ≤ i := by
    simp only [allIds,RationalArctan.ids,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hi
    omega
  have hhi : i≤627 := by
    simp only [allIds,RationalArctan.ids,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hi
    omega
  interval_cases i <;> simp_all [allIds,RationalArctan.ids,prologue,initialValues,
    NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.value,NatAssign.Instruction.target]

theorem saveFirst_values (N i : ℕ) (hi : i∈allIds) :
    NatAssign.values saveFirst (firstValues N) i=preparedValues N i := by
  have hlo : 610 ≤ i := by
    simp only [allIds,RationalArctan.ids,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hi
    omega
  have hhi : i≤627 := by
    simp only [allIds,RationalArctan.ids,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hi
    omega
  interval_cases i <;> simp_all [allIds,RationalArctan.ids,saveFirst,initialValues,preparedValues,
    firstValues,RationalArctan.extendedValues,RationalArctan.values,positive,negative,denominator,
    NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.value,NatAssign.Instruction.target]

theorem combine_values (N : ℕ) :
    NatAssign.values combine (secondValues N) 623=numeratorPositive N ∧
    NatAssign.values combine (secondValues N) 624=numeratorNegative N ∧
    NatAssign.values combine (secondValues N) 625=commonDenominator N := by
  simp [combine,secondValues,preparedValues,initialValues,RationalArctan.extendedValues,
    RationalArctan.ids,RationalArctan.values,positive,negative,denominator,
    numeratorPositive,numeratorNegative,commonDenominator,NatAssign.values,
    NatAssign.Instruction.update,NatAssign.Instruction.value,NatAssign.Instruction.target]
  constructor
  · ring
  constructor <;> ring

theorem initial_width (b : ℕ) (hb : b.bits.length≤8) (i : ℕ) :
    (initialValues b i).bits.length≤8 := by
  unfold initialValues
  split_ifs <;> first | exact hb | decide

theorem prefix_width_ge_eight (N : ℕ) : 8≤RationalArctan.width (N+6) 8 := by
  unfold RationalArctan.width RationalArctan.termWidth
  nlinarith

theorem first_width (N i : ℕ) (hi : i∈allIds) :
    (firstValues N i).bits.length≤RationalArctan.width (N+6) 8 :=
  RationalArctan.extended_width allIds ids_subset (initialValues 5) negativeSigns (N+6) 8
    (fun j _ => initial_width 5 (by decide) j) i hi

theorem prepared_width (N i : ℕ) :
    (preparedValues N i).bits.length≤RationalArctan.width (N+6) 8 := by
  have h5 := prefix_width 5 N (by decide)
  unfold preparedValues
  split_ifs <;> first | exact h5.1 | exact h5.2.1 | exact h5.2.2 |
    exact (initial_width 239 (by decide) i).trans (prefix_width_ge_eight N)

theorem prepared_input_width (N i : ℕ) (hi : i∈RationalArctan.ids) :
    (preparedValues N i).bits.length≤8 := by
  have h620 : i≠620 := by simp only [RationalArctan.ids,Finset.mem_insert,Finset.mem_singleton] at hi; omega
  have h621 : i≠621 := by simp only [RationalArctan.ids,Finset.mem_insert,Finset.mem_singleton] at hi; omega
  have h622 : i≠622 := by simp only [RationalArctan.ids,Finset.mem_insert,Finset.mem_singleton] at hi; omega
  simpa only [preparedValues,ite_eq_right h620,ite_eq_right h621,ite_eq_right h622] using
    initial_width 239 (by decide) i

theorem second_width (N i : ℕ) :
    (secondValues N i).bits.length≤RationalArctan.width (N+6) 8 := by
  unfold secondValues RationalArctan.extendedValues
  split_ifs
  · have hv : preparedValues N 610=1 ∧ preparedValues N 611=239 := by simp [preparedValues,initialValues]
    rw [hv.1,hv.2]
    exact RationalArctan.values_width 1 239 negativeSigns (N+6) (N+6) 8 le_rfl (by decide) (by decide) i
  · exact prepared_width N i

#print axioms combine_values

end Maxwell.Continuum.Machin
