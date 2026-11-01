import Maxwell.Continuum.CalibrationInverseDescriptorData
import Maxwell.Continuum.NatAssignOutputWidth

/-! Bounds for the descriptor arithmetic refer to its measured input words.
The shared-conversion allowance includes the actual coefficient-table count. -/
namespace Maxwell.Continuum.Calibration.InverseDescriptor
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow PartArray ArrayDecodeMachine NeumannMachine
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384
attribute [local irreducible] sources budget rawWidth dimension slotWidth

theorem measured_width (v : ℕ→ℕ) : ∀k∈ids,(measured v k).bits.length≤budget v := by
  intro k hk
  by_cases ht:k=530
  · subst k
    rw [measured_budget,Nat.size_eq_bits_len,Nat.size_le]
    exact Nat.lt_two_pow_self
  by_cases ht':k=531
  · subst k
    simp only [measured,NatAssign.LengthSum.initializedValues,Function.update_of_ne (by decide : (531:ℕ)≠530),
      Function.update_self]
    change 0≤budget v
    exact Nat.zero_le _
  have hs:k∈sourceIds:=by
    rcases Finset.mem_union.mp hk with h|h
    · exact h
    · simp only [Finset.mem_insert,Finset.mem_singleton] at h
      omega
  rw [measured_source v k hs]
  exact budget_bound v k hs

theorem literals_fit (v : ℕ→ℕ) : ∀a∈plan,a.literalWidth≤budget v := by
  have h:=budget_ge v
  have power:(2^140:ℕ).bits.length=141:=by rw [Nat.size_eq_bits_len,Nat.size_pow]
  simp only [plan,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,NatAssign.Instruction.literalWidth]
  norm_num only at power
  norm_num only [show (0:ℕ).bits.length=0 by rfl,show (1:ℕ).bits.length=1 by rfl,
    show (2:ℕ).bits.length=2 by rfl,show (3:ℕ).bits.length=2 by rfl]
  omega

theorem bankWidth_lower (v : ℕ→ℕ) : 2^80*(budget v+1)≤bankWidth v := by
  unfold bankWidth
  exact (Nat.le_mul_of_pos_right _ (by omega : 0<v 570+2)).trans
    (Nat.le_mul_of_pos_right _ (by omega : 0<rawWidth v+2))

theorem values_width (v : ℕ→ℕ) : ∀k∈ids,(values v k).bits.length≤bankWidth v := by
  have h:=NatAssign.values_width_bound ids plan plan_valid (measured v) (budget v)
    (measured_width v) (literals_fit v)
  have hp:2^plan.length≤(2:ℕ)^80:=Nat.pow_le_pow_right (by decide) (by decide : plan.length≤80)
  intro k hk
  have hb:=h k hk
  change (values v k).bits.length+1≤2^plan.length*(budget v+1) at hb
  have hk':(values v k).bits.length≤2^plan.length*(budget v+1):=by omega
  exact (hk'.trans (Nat.mul_le_mul_right _ hp)).trans (bankWidth_lower v)

theorem rawWidth_bound (v : ℕ→ℕ) : rawWidth v+2≤bankWidth v := by
  unfold bankWidth
  have h:1≤2^80*(budget v+1)*(v 570+2):=by
    have h:0<2^80*(budget v+1)*(v 570+2):=by positivity
    omega
  simpa only [one_mul] using Nat.mul_le_mul_right (rawWidth v+2) h

theorem sharedWidth_bound (v : ℕ→ℕ) : PartArray.sharedWidth (v 570) (rawWidth v)≤bankWidth v := by
  have h:1≤2^80*(budget v+1):=by
    have h:0<2^80*(budget v+1):=by positivity
    omega
  unfold PartArray.sharedWidth bankWidth
  have hm:(v 570+2)*(rawWidth v+2)≤2^80*(budget v+1)*(v 570+2)*(rawWidth v+2):=by
    calc
      _ = 1*((v 570+2)*(rawWidth v+2)) := by ring
      _ ≤ (2^80*(budget v+1))*((v 570+2)*(rawWidth v+2)) := Nat.mul_le_mul_right _ h
      _ = _ := by ring
  nlinarith only [hm,Nat.zero_le (v 570)]

#print axioms values_width
#print axioms sharedWidth_bound
end Maxwell.Continuum.Calibration.InverseDescriptor
