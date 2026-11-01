import Maxwell.Continuum.CalibrationCoefficientAllocationData

/-! The measured allocation width is linear in input word lengths. Arithmetic
and metadata bounds refer to that actual measured value, not supplied width
words. -/
namespace Maxwell.Continuum.Calibration.CoefficientAllocation
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow PartArray ArrayDecodeMachine NeumannMachine
set_option maxHeartbeats 5000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 2048

def measureWidth (B : ℕ) : ℕ := 626+(sources.length+1)*B
def planWidth (B : ℕ) : ℕ := 2^22*(measureWidth B+1001)
def metadataWidth (B : ℕ) : ℕ := slotWidth (measureWidth B)+3*planWidth B+4

theorem measured_width (n : ℕ→ℕ) (B : ℕ) (hw : ∀k∈allIds,(n k).bits.length≤B) :
    ∀k∈allIds,(measured n k).bits.length≤measureWidth B := by
  have totalBound:=NatAssign.LengthSum.total_le sources n B (fun k hk=>hw k (sources_valid k hk).1)
  have base:B≤measureWidth B:=by unfold measureWidth;nlinarith only [Nat.zero_le (sources.length*B)]
  intro k hk
  by_cases h580:k=580
  · subst k
    rw [measured_budget]
    have bits:(budget n).bits.length≤budget n:=by
      rw [Nat.size_eq_bits_len,Nat.size_le];exact Nat.lt_two_pow_self
    unfold budget measureWidth at *
    nlinarith only [bits,totalBound]
  · by_cases h581:k=581
    · subst k
      simp [measured,NatAssign.LengthSum.initializedValues]
    · simpa only [measured,NatAssign.LengthSum.initializedValues,Function.update_of_ne h580,
        Function.update_of_ne h581] using (hw k hk).trans base

theorem budget_le_measureWidth (n : ℕ→ℕ) (B : ℕ) (hw : ∀k∈allIds,(n k).bits.length≤B) :
    budget n≤measureWidth B := by
  have totalBound:=NatAssign.LengthSum.total_le sources n B (fun k hk=>hw k (sources_valid k hk).1)
  unfold budget measureWidth
  nlinarith only [totalBound,Nat.zero_le B]

theorem plan_literals (B : ℕ) : ∀a∈plan,a.literalWidth≤measureWidth B+1000 := by
  have offset : slotOffset.bits.length≤1000 := by decide
  have power : (2^717:ℕ).bits.length≤1000 := by decide
  have low : 1000≤measureWidth B+1000 := Nat.le_add_left _ _
  simp only [plan,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,NatAssign.Instruction.literalWidth]
  norm_num only at power
  norm_num only [show (0:ℕ).bits.length=0 by rfl,show (1:ℕ).bits.length=1 by rfl,
    show (2:ℕ).bits.length=2 by rfl,show (3:ℕ).bits.length=2 by rfl]
  omega

theorem planned_width (n : ℕ→ℕ) (B : ℕ) (hw : ∀k∈allIds,(n k).bits.length≤B) :
    ∀k∈allIds,(planned n k).bits.length≤planWidth B := by
  have h:=NatAssign.values_width allIds plan plan_valid (measured n) (measureWidth B+1000)
    (fun k hk=>(measured_width n B hw k hk).trans (Nat.le_add_right _ _)) (plan_literals B)
  intro k hk
  have hh:=h k hk
  change (planned n k).bits.length+1≤2^22*(measureWidth B+1000+1) at hh
  unfold planWidth
  omega

theorem slotWidth_mono {B C : ℕ} (h:B≤C) : slotWidth B≤slotWidth C := by
  unfold slotWidth
  exact Nat.add_le_add_right (Nat.mul_le_mul_left _ h) _

theorem table_metadata (n : ℕ→ℕ) (B : ℕ) (hw : ∀k∈allIds,(n k).bits.length≤B) (memory : ℕ→Bool) :
    (Profile.Runtime.memoryTable (tableSize (aliasArraySize (n 311))) (slotWidth (budget n))
      (heap n) (slotWidth_pos _) memory).MetadataWidth (metadataWidth B) := by
  have width:=planned_width n B hw
  have count:=width 570 (by decide)
  have slot:=width 571 (by decide)
  have base:=width 572 (by decide)
  rw [(plan_outputs n).1] at count
  rw [(plan_outputs n).2.1] at slot
  rw [(plan_outputs n).2.2.1] at base
  apply Profile.Runtime.memoryTable_metadata
  · have h:=slotWidth_mono (budget_le_measureWidth n B hw)
    unfold metadataWidth
    omega
  · unfold metadataWidth
    omega

#print axioms planned_width
#print axioms table_metadata
end Maxwell.Continuum.Calibration.CoefficientAllocation
