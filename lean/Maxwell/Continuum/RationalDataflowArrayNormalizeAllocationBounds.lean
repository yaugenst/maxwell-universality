import Maxwell.Continuum.RationalDataflowArrayNormalizeAllocationData
import Maxwell.Continuum.RationalDataflowStoredWidths

/-! The measured normalization request bounds the actual words and allocates
three channels beyond every input channel. -/
namespace Maxwell.Continuum.RationalDataflow.PartArray.Normalize.Allocation
open Maxwell.Cost Maxwell.Cost.Structured Calibration
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384

def measureWidth (B : ℕ) : ℕ := 1000+(sources.length+1)*B
def planWidth (B : ℕ) : ℕ := 2^plan.length*(measureWidth B+7)
def table (n : ℕ→ℕ) (memory : ℕ→Bool) : Table (n 788) :=
  Profile.Runtime.memoryTable _ (capacity n) (heap n) (capacity_pos n) memory

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

theorem plan_literals (B : ℕ) : ∀a∈plan,a.literalWidth≤measureWidth B+6 := by
  simp [plan,NatAssign.Instruction.literalWidth,show (32:ℕ).bits.length=6 by decide,
    show (24:ℕ).bits.length=5 by decide,show (49:ℕ).bits.length=6 by decide,
    show (3:ℕ).bits.length=2 by decide]
theorem planned_width (n : ℕ→ℕ) (B : ℕ) (hw : ∀k∈allIds,(n k).bits.length≤B) :
    ∀k∈allIds,(planned n k).bits.length≤planWidth B := by
  intro k hk
  exact (Nat.le_add_right _ 1).trans
    (NatAssign.values_width allIds plan plan_valid (measured n) (measureWidth B+6)
      (fun k hk=>(measured_width n B hw k hk).trans (Nat.le_add_right _ _)) (plan_literals B) k hk)

theorem capacity_bits (n : ℕ→ℕ) : (capacity n).bits.length≤3*budget n+20 := by
  have hc:=budget_bound n 788 (by decide)
  have hp:=budget_bound n 700 (by decide)
  have hb:=budget_ge n
  have hw : (budget n).bits.length≤budget n := by
    rw [Nat.size_eq_bits_len,Nat.size_le];exact Nat.lt_two_pow_self
  have a:=RationalAccumulator.bits_add_le (n 788) 1
  have b:=RationalAccumulator.bits_add_le (budget n) 1
  have c:=RationalAccumulator.bits_mul_le 32 (n 788+1)
  have d:=RationalAccumulator.bits_mul_le (32*(n 788+1)) (budget n+1)
  have e:=RationalAccumulator.bits_mul_le 24 (n 700)
  have f:=RationalAccumulator.bits_add_le (32*(n 788+1)*(budget n+1)) (24*n 700)
  have g:=RationalAccumulator.bits_add_le (32*(n 788+1)*(budget n+1)+24*n 700) 49
  norm_num only [show (1:ℕ).bits.length=1 by rfl,show (32:ℕ).bits.length=6 by decide,
    show (24:ℕ).bits.length=5 by decide,show (49:ℕ).bits.length=6 by decide] at a b c e g
  rw [capacity_eq]
  omega
theorem heap_bits (n : ℕ→ℕ) : (heap n).bits.length≤2*budget n+4 := by
  have h200:=budget_bound n 200 (by decide)
  have h202:=budget_bound n 202 (by decide)
  have h203:=budget_bound n 203 (by decide)
  have h204:=budget_bound n 204 (by decide)
  have h788:=budget_bound n 788 (by decide)
  have a:=RationalAccumulator.bits_add_le (n 202) (n 203)
  have b:=RationalAccumulator.bits_add_le (n 202+n 203) (n 204)
  have c:=RationalAccumulator.bits_mul_le (n 788) (n 200)
  have d:=RationalAccumulator.bits_add_le (n 202+n 203+n 204) (n 788*n 200)
  unfold heap
  omega
theorem table_metadata (n : ℕ→ℕ) (memory : ℕ→Bool) :
    (table n memory).MetadataWidth (capacity n) := by
  apply Profile.Runtime.memoryTable_metadata _ _ _ _ _ _ le_rfl
  have hheap:=heap_bits n
  have hcap:=capacity_bits n
  have hcount:=budget_bound n 788 (by decide)
  have hb:=budget_ge n
  have large : 6*budget n+28≤capacity n := by
    rw [capacity_eq]
    nlinarith only [hb,Nat.zero_le (n 788*(budget n+1)),Nat.zero_le (n 700)]
  omega

theorem table_disjoint {T : ℕ} (a : Table T) (n : ℕ→ℕ) (s : Store)
    (bank : NatAssign.Bank sourceIds n s.val) (ready : a.Ready s)
    (count : T=n 788) (memory : ℕ→Bool) : a.SeparatedFrom (table n memory) := by
  obtain ⟨w,p,q,d⟩:=a.words_of_bank sourceIds n (by decide) s bank ready
  intro x hx y hy
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  simp only [table,Profile.Runtime.memoryTable,List.mem_cons,List.not_mem_nil,or_false] at hy
  rcases hx with rfl|rfl|rfl <;> rcases hy with rfl|rfl|rfl <;>
    simp only [table,Profile.Runtime.memoryTable,IncidenceEncoding.Separated,addressValue_bits,
      count,heap,w,p,q,d] <;> left <;> omega

#print axioms table_metadata
#print axioms table_disjoint
end Maxwell.Continuum.RationalDataflow.PartArray.Normalize.Allocation
