import Maxwell.Continuum.ProfileRawProducer

/-! Endpoint moments from a descending Horner traversal. The fixed recurrence
does not need a multiplication by a runtime coefficient index. -/
namespace Maxwell.Continuum.Profile.Runtime
set_option maxHeartbeats 1500000

def suffixMoment (f : ℕ→ℚ) (n r m : ℕ) : ℚ :=
  ∑ j∈Finset.Ico r n,((j:ℚ)-r)^m*f j

theorem suffixMoment_step (f : ℕ→ℚ) (n r : ℕ) (hr : r<n) :
    suffixMoment f n r 0=suffixMoment f n (r+1) 0+f r ∧
    suffixMoment f n r 1=suffixMoment f n (r+1) 1+suffixMoment f n (r+1) 0 ∧
    suffixMoment f n r 2=suffixMoment f n (r+1) 2+
      2*suffixMoment f n (r+1) 1+suffixMoment f n (r+1) 0 := by
  have split (m : ℕ) := Finset.sum_eq_sum_Ico_succ_bot hr
    (fun j => ((j:ℚ)-r)^m*f j)
  constructor
  · unfold suffixMoment
    rw [split 0]
    simp only [pow_zero,one_mul]
    exact add_comm _ _
  constructor
  · unfold suffixMoment
    rw [split 1]
    simp only [sub_self,pow_one,zero_mul,zero_add]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    push_cast
    ring
  · unfold suffixMoment
    rw [split 2]
    simp only [sub_self,zero_pow (by decide : 2≠0),zero_mul,zero_add]
    rw [Finset.mul_sum,← Finset.sum_add_distrib,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    push_cast
    ring

theorem suffixMoment_empty (f : ℕ→ℚ) (n m : ℕ) : suffixMoment f n n m=0 := by
  simp [suffixMoment]

theorem suffixMoment_final (f : ℕ→ℚ) (n m : ℕ) :
    suffixMoment f n 0 m=∑j∈Finset.range n,(j:ℚ)^m*f j := by
  simp only [suffixMoment,Nat.cast_zero,sub_zero,Nat.Ico_zero_eq_range]

#print axioms suffixMoment_step
end Maxwell.Continuum.Profile.Runtime
