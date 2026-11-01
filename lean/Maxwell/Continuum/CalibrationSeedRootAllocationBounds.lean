import Maxwell.Continuum.CalibrationSeedRootAllocationData

/-! Bounds for the actual measured storage request and its three-channel
layout. No destination width or address certificate is a machine input. -/
namespace Maxwell.Continuum.Calibration.SeedRoot.Allocation
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 2048

def measureWidth (B : ℕ) : ℕ := 1000+(sources.length+1)*B
def planWidth (B : ℕ) : ℕ := 2^plan.length*(measureWidth B+331)
def table (n : ℕ→ℕ) (memory : ℕ→Bool) : PartArray.Table (n 788) :=
  Profile.Runtime.memoryTable _ (producerWidth (budget n)) (heap n) (producerWidth_pos _) memory

theorem measured_width (n : ℕ→ℕ) (B : ℕ) (hw : ∀k∈allIds,(n k).bits.length≤B) :
    ∀k∈allIds,(measured n k).bits.length≤measureWidth B := by
  have totalBound:=NatAssign.LengthSum.total_le sources n B (fun k hk=>hw k (sources_valid k hk).1)
  have base:B≤measureWidth B:=by unfold measureWidth;nlinarith only [Nat.zero_le (sources.length*B)]
  intro k hk
  by_cases h802:k=802
  · subst k
    change (1000+NatAssign.LengthSum.total sources n).bits.length≤measureWidth B
    have bits : (1000+NatAssign.LengthSum.total sources n).bits.length≤1000+NatAssign.LengthSum.total sources n := by
      rw [Nat.size_eq_bits_len,Nat.size_le];exact Nat.lt_two_pow_self
    unfold measureWidth
    nlinarith only [bits,totalBound,Nat.zero_le B]
  · by_cases h803:k=803
    · subst k;simp [measured,NatAssign.LengthSum.initializedValues]
    · simpa only [measured,NatAssign.LengthSum.initializedValues,Function.update_of_ne h802,
        Function.update_of_ne h803] using (hw k hk).trans base

theorem plan_literals (B : ℕ) : ∀a∈plan,a.literalWidth≤measureWidth B+330 := by
  have offset : (producerWidth 0).bits.length≤330 := by decide
  have power : (2^321:ℕ).bits.length=322 := by decide
  norm_num only at power
  simp only [plan,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,
    NatAssign.Instruction.literalWidth]
  norm_num only [show (0:ℕ).bits.length=0 by rfl,show (1:ℕ).bits.length=1 by rfl,
    show (2:ℕ).bits.length=2 by rfl,power]
  omega

theorem planned_width (n : ℕ→ℕ) (B : ℕ) (hw : ∀k∈allIds,(n k).bits.length≤B) :
    ∀k∈allIds,(planned n k).bits.length≤planWidth B := by
  intro k hk
  have h:=NatAssign.values_width allIds plan plan_valid (measured n) (measureWidth B+330)
    (fun k hk=>(measured_width n B hw k hk).trans (Nat.le_add_right _ _)) (plan_literals B) k hk
  exact (Nat.le_add_right _ 1).trans h

theorem heap_bits (n : ℕ→ℕ) : (heap n).bits.length≤7*budget n+17 := by
  have d:=budget_bound n 751 (by decide)
  have w:=budget_bound n 200 (by decide)
  have h:=budget_bound n 204 (by decide)
  have hp:=budget_bound n 202 (by decide)
  have hq:=budget_bound n 203 (by decide)
  have pq:=RationalAccumulator.bits_add_le (n 202) (n 203)
  have pqd:=RationalAccumulator.bits_add_le (n 202+n 203) (n 204)
  have a:=RationalAccumulator.bits_mul_le 2 (n 751)
  have b:=RationalAccumulator.bits_add_le (2*n 751) 1
  have c:=RationalAccumulator.bits_mul_le (2*n 751+1) (2*n 751+1)
  have e:=RationalAccumulator.bits_mul_le ((2*n 751+1)*(2*n 751+1)) (2*n 751+1)
  have f:=RationalAccumulator.bits_mul_le 2 ((2*n 751+1)^3)
  have g:=RationalAccumulator.bits_mul_le (2*(2*n 751+1)^3) (n 200)
  have j:=RationalAccumulator.bits_add_le (n 202+n 203+n 204) (2*(2*n 751+1)^3*n 200)
  norm_num only [show (1:ℕ).bits.length=1 by rfl,show (2:ℕ).bits.length=2 by rfl] at a b f
  have cube : (2*n 751+1)*(2*n 751+1)*(2*n 751+1)=(2*n 751+1)^3 := by ring
  rw [cube] at e
  unfold heap
  omega

theorem table_metadata (n : ℕ→ℕ) (memory : ℕ→Bool) :
    (table n memory).MetadataWidth (producerWidth (budget n)) := by
  apply Profile.Runtime.memoryTable_metadata _ _ _ _ _ _ le_rfl
  have hb:=budget_ge n
  have heapWidth:=heap_bits n
  have countWidth:=budget_bound n 788 (by decide)
  have slot:=producerWidth_bits (budget n)
  have small : (budget n).bits.length≤budget n := by
    rw [Nat.size_eq_bits_len,Nat.size_le];exact Nat.lt_two_pow_self
  have large : 9*budget n+674≤producerWidth (budget n) := by
    rw [producerWidth_affine]
    omega
  omega

theorem table_disjoint {T : ℕ} (a : PartArray.Table T) (n : ℕ→ℕ)
    (hsize : T=2*(2*n 751+1)^3) (width : addressValue a.width=n 200)
    (p : addressValue a.basePositive=n 202) (q : addressValue a.baseNegative=n 203)
    (d : addressValue a.baseDenominator=n 204) (memory : ℕ→Bool) :
    a.SeparatedFrom (table n memory) := by
  intro x hx y hy
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  simp only [table,Profile.Runtime.memoryTable,List.mem_cons,List.not_mem_nil,or_false] at hy
  rcases hx with rfl|rfl|rfl <;> rcases hy with rfl|rfl|rfl <;>
    simp only [table,Profile.Runtime.memoryTable,IncidenceEncoding.Separated,addressValue_bits,
      width,hsize,heap,p,q,d] <;> left <;> omega

#print axioms table_metadata
#print axioms table_disjoint
end Maxwell.Continuum.Calibration.SeedRoot.Allocation
