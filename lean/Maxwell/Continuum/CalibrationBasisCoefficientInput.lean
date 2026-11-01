import Maxwell.Continuum.CalibrationBasisForcingInput
import Maxwell.Continuum.CalibrationCoefficientAllocationCounter

/-! Assemble the coefficient allocator's input bank from the actual source
producer's returned words. Only untouched finite scratch words come from the
incoming state; no coefficients, metadata, or widths are postulated. -/
namespace Maxwell.Continuum.Calibration.BasisForcing.CoefficientInput
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow PartArray ArrayDecodeMachine
set_option maxHeartbeats 6000000
set_option maxRecDepth 16384
attribute [local irreducible] bank sourceTable

def extraIds : Finset ℕ := Finset.Icc 321 332∪Finset.Icc 580 584
def numbers (R heap : ℕ) (nf extra work : ℕ→ℕ) (k : ℕ) : ℕ :=
  if k=311 then R else if k∈naturalIds then nf k else
  if k=200 then 625 else if k=202 then heap else if k=203 then heap+aliasArraySize R*625 else
  if k=204 then heap+2*aliasArraySize R*625 else
  if k∈PowerMachine.BufferNorm.Allocation.inputs then work k else extra k

theorem radius (R heap : ℕ) (nf extra work : ℕ→ℕ) : numbers R heap nf extra work 311=R := rfl

theorem natural (R heap : ℕ) (nf extra work : ℕ→ℕ) (hr:nf 311=R) (k : ℕ) (hk:k∈naturalIds) :
    numbers R heap nf extra work k=nf k := by
  by_cases he:k=311
  · subst k;exact hr.symm
  · simp only [numbers,he,hk,↓reduceIte]

theorem emission_subset : emissionIds⊆naturalIds∪extraIds := by
  intro k hk
  rcases Finset.mem_union.mp hk with hk|hk
  · rcases Finset.mem_union.mp hk with hk|hk
    · apply Finset.mem_union_left
      apply naturalIds_parts
      rcases Finset.mem_union.mp hk with hp|hw
      · obtain ⟨r,hr,hp⟩:=Finset.mem_biUnion.mp hp
        apply Finset.mem_union_left
        apply Finset.mem_biUnion.mpr
        refine ⟨r,?_,hp⟩
        simp only [RawFree.neighborRegisters,Finset.mem_range] at hr
        simp only [bank,Finset.mem_range]
        omega
      · exact Finset.mem_union_right _ hw
    · have bounds:=Finset.mem_Icc.mp hk
      by_cases h:k≤320
      · exact Finset.mem_union_left _ (naturalIds_decode (Finset.mem_Icc.mpr ⟨bounds.1,h⟩))
      · exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_Icc.mpr ⟨by omega,bounds.2⟩))
  · exact Finset.mem_union_left _ (naturalIds_work hk)

theorem extra_inverse : extraIds⊆inversePorts := by
  intro k hk
  exact Finset.mem_union_right _ hk

theorem assembled (R heap : ℕ) (nf extra work : ℕ→ℕ) (hr:nf 311=R)
    (U E W M : ℕ) (nwidth:∀k∈naturalIds,(nf k).bits.length≤U)
    (ewidth:∀k∈extraIds,(extra k).bits.length≤E)
    (wwidth:∀k∈PowerMachine.BufferNorm.Allocation.inputs,(work k).bits.length≤W)
    (a : Table (aliasArraySize R)) (memory : ℕ→Bool) (metadata:sameMetadata (sourceTable R heap memory) a)
    (bounds:(sourceTable R heap memory).MetadataWidth M)
    (s : Store) (ready:a.Ready s) (nbank:NatAssign.Bank naturalIds nf s.val)
    (ebank:NatAssign.Bank extraIds extra s.val)
    (wbank:NatAssign.Bank PowerMachine.BufferNorm.Allocation.inputs work s.val) :
    NatAssign.Bank CoefficientAllocation.allIds (numbers R heap nf extra work) s.val ∧
      ∀k∈CoefficientAllocation.allIds,(numbers R heap nf extra work k).bits.length≤U+E+W+M := by
  have each (k : ℕ) (hk:k∈CoefficientAllocation.allIds) :
      RationalAccumulator.Word s.val k (numbers R heap nf extra work k) ∧
        (numbers R heap nf extra work k).bits.length≤U+E+W+M := by
    by_cases hn:k∈naturalIds
    · rw [natural R heap nf extra work hr k hn]
      exact ⟨nbank k hn,(nwidth k hn).trans (by omega)⟩
    have h311:k≠311:=fun he=>hn (he ▸ naturalIds_decode (by decide))
    by_cases h200:k=200
    · subst k
      simp only [numbers,h311,hn,ite_false,ite_true]
      exact ⟨by simpa only [metadata.1,sourceTable,Profile.Runtime.memoryTable,BankArray.Word,RationalAccumulator.Word] using ready.width,
        (show (625:ℕ).bits.length≤M by simpa only [sourceTable,Profile.Runtime.memoryTable] using bounds.width).trans (by omega)⟩
    by_cases h202:k=202
    · subst k
      simp only [numbers,h311,hn,h200,ite_false,ite_true]
      exact ⟨by simpa only [metadata.2.1,sourceTable,Profile.Runtime.memoryTable,BankArray.Word,RationalAccumulator.Word] using ready.basePositive,
        (show heap.bits.length≤M by simpa only [sourceTable,Profile.Runtime.memoryTable] using bounds.basePositive).trans (by omega)⟩
    by_cases h203:k=203
    · subst k
      simp only [numbers,h311,hn,h200,h202,ite_false,ite_true]
      exact ⟨by simpa only [metadata.2.2.1,sourceTable,Profile.Runtime.memoryTable,BankArray.Word,RationalAccumulator.Word] using ready.baseNegative,
        (show (heap+aliasArraySize R*625).bits.length≤M by simpa only [sourceTable,Profile.Runtime.memoryTable] using bounds.baseNegative).trans (by omega)⟩
    by_cases h204:k=204
    · subst k
      simp only [numbers,h311,hn,h200,h202,h203,ite_false,ite_true]
      exact ⟨by simpa only [metadata.2.2.2.1,sourceTable,Profile.Runtime.memoryTable,BankArray.Word,RationalAccumulator.Word] using ready.baseDenominator,
        (show (heap+2*aliasArraySize R*625).bits.length≤M by simpa only [sourceTable,Profile.Runtime.memoryTable] using bounds.baseDenominator).trans (by omega)⟩
    simp only [numbers,h311,hn,h200,h202,h203,h204,ite_false]
    by_cases hw:k∈PowerMachine.BufferNorm.Allocation.inputs
    · rw [ite_eq_left hw]
      exact ⟨wbank k hw,(wwidth k hw).trans (by omega)⟩
    rw [ite_eq_right hw]
    have he:k∈extraIds:=by
      rcases Finset.mem_union.mp hk with hs|hs
      · rcases Finset.mem_union.mp hs with he|hh
        · exact (Finset.mem_union.mp (emission_subset he)).resolve_left hn
        · simp only [Finset.mem_insert,Finset.mem_singleton] at hh
          omega
      · simp only [CoefficientAllocation.workIds,Finset.mem_insert,Finset.mem_singleton] at hs
        simp only [PowerMachine.BufferNorm.Allocation.inputs,Finset.mem_insert,Finset.mem_singleton,not_or] at hw
        simp only [extraIds,Finset.mem_union,Finset.mem_Icc]
        omega
    exact ⟨ebank k he,(ewidth k he).trans (by omega)⟩
  exact ⟨fun k hk=>(each k hk).1,fun k hk=>(each k hk).2⟩

#print axioms assembled
end Maxwell.Continuum.Calibration.BasisForcing.CoefficientInput
