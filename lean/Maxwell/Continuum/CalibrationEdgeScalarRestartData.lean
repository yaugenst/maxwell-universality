import Maxwell.Continuum.CalibrationEdgeScalarBank
import Maxwell.Continuum.RationalDataflowResetExcept

/-! An edge iteration starts its matrix bank from the newly computed five
scalars and literal zeros. The previous matrix affects cleanup cost only. -/
namespace Maxwell.Continuum.Calibration.EdgeScalarRestart
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384
attribute [local irreducible] BasisForcing.bank SchurRow.nodeCount

def erased : Finset ℕ := SchurRow.bank\EdgeScalar.saved
def code : Code := .seq EdgeScalar.code (.seq (Initialize.code erased) BasisReentry.code)
def width (N B : ℕ) : ℕ := max 1 (max 1 (EdgeScalar.resultWidth N B))
def eraseWidth (N B P : ℕ) : ℕ := 1+P+EdgeScalar.resultWidth N B

theorem values (N : ℕ) (mid : Parts) (p : ℕ→Parts) :
    ResetExcept.values EdgeScalar.saved (EdgeScalar.patch N mid p)=EdgeScalar.result N mid := by
  funext i
  by_cases scalar : i∈EdgeScalar.saved
  · simp only [ResetExcept.values,EdgeScalar.patch,ite_eq_left scalar]
  · have ne : i≠232 ∧ i≠233 := by
      simp only [EdgeScalar.saved,Finset.mem_insert,Finset.mem_singleton,not_or] at scalar
      tauto
    simp only [ResetExcept.values,ite_eq_right scalar,Initialize.parts,EdgeScalar.result,
      ite_eq_right ne.1,ite_eq_right ne.2]

theorem erased_subset : erased⊆SchurRow.bank := Finset.sdiff_subset

theorem erased_workspace : workspace erased⊆workspace BasisScalarReload.bank := by
  intro k hk
  rcases Finset.mem_union.mp hk with low | ids
  · exact Finset.mem_union_left _ low
  · exact Finset.mem_union_right _ (ids_mono (erased_subset.trans Finset.subset_union_right) ids)

theorem source_separate : Disjoint BasisForcing.bank erased :=
  BasisScalarReload.separated.mono_right erased_subset

theorem reserved_workspace (k : ℕ) (h : k=311 ∨ k=376 ∨ (5≤k ∧ k≤9) ∨ (600≤k ∧ k<1000)) :
    k∉workspace BasisScalarReload.bank := by
  simp only [workspace,ids,Finset.mem_union,not_or]
  refine ⟨by simp only [Finset.mem_insert,Finset.mem_singleton];omega,?_,?_⟩
  · intro member
    obtain ⟨i,_,cell⟩:=Finset.mem_biUnion.mp member
    simp only [cellPorts,positivePort,negativePort,denominatorPort,
      Finset.mem_insert,Finset.mem_singleton] at cell
    omega
  · simp only [workPorts,temporaryPorts,RationalMagnitude.ids,Finset.mem_union,
      Finset.mem_insert,Finset.mem_singleton];omega

#print axioms values
end Maxwell.Continuum.Calibration.EdgeScalarRestart
