import Maxwell.Continuum.ProfileBufferExecution

/-! The computed working width also covers every actual address word and
clock of the two coefficient buffers. -/
namespace Maxwell.Continuum.Profile.Runtime
open RationalDataflow Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 4500000
set_option maxRecDepth 16384
set_option exponentiation.threshold 2048

theorem producerSize_input_bounds (N : ℕ) : 501≤producerSize N ∧
    N.bits.length≤producerSize N ∧ (profileDegree N).bits.length≤producerSize N := by
  have hb (n : ℕ) : n.bits.length≤n := by
    rw [Nat.size_eq_bits_len,Nat.size_le];exact Nat.lt_two_pow_self
  have hn : N+1≤(N+1)^2 := Nat.le_self_pow (by decide) _
  have hp : 1≤(N+1)^2 := one_le_pow₀ (by omega)
  have hd := (producerSize_bounds N).2.2.1
  refine ⟨?_,(hb N).trans ?_,(hb _).trans hd⟩ <;> unfold producerSize <;> omega

theorem allocationBound_runtime (N : ℕ) : allocationBound (producerSize N)≤runtimeBudget N := by
  have hp : producerSize N+1≤(producerSize N+1)^18 := Nat.le_self_pow (by decide) _
  unfold allocationBound runtimeBudget workingBudget
  exact Nat.mul_le_mul (Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (by decide : 64≤500)) hp

theorem runtimeBudget_le_bufferWidth (N D : ℕ) : runtimeBudget N≤bufferWidth N D := by
  unfold bufferWidth encodedTableWidth correctionWorkingWidth endpointWorkingWidth
  omega

theorem allocated_metadata (N heap : ℕ) (hh : heap.bits.length≤producerSize N)
    (memory : ℕ→Bool) :
    (memoryTable (profileDegree N) (runtimeBudget N) heap
      (runtimeBudget_parameters N).1 memory).MetadataWidth (runtimeBudget N) ∧
    (memoryTable (profileDegree N) (bufferWidth N (profileDegree N))
      (secondBufferBase N (profileDegree N) heap)
      (Nat.lt_of_lt_of_le (runtimeBudget_parameters N).1 (runtimeBudget_le_bufferWidth N _)) memory).MetadataWidth
        (bufferWidth N (profileDegree N)) := by
  obtain ⟨hB,hN,hD⟩ := producerSize_input_bounds N
  have all (i : ℕ) (hi : i∈allocationIds) :
      (bufferAddressValues N (profileDegree N) heap i).bits.length≤runtimeBudget N :=
    (bufferAddressValues_width N (profileDegree N) heap (producerSize N) hN hD hh hB i hi).trans
      (allocationBound_runtime N)
  have hWM := runtimeBudget_le_bufferWidth N (profileDegree N)
  constructor
  · refine ⟨?_,?_,?_,?_,by simp only [memoryTable,List.length_replicate];exact le_rfl⟩
    · simpa only [memoryTable,bufferAddressValues_eq,ite_true] using all 210 (by decide)
    · simpa [memoryTable,bufferAddressValues_eq] using all 212 (by decide)
    · simpa [memoryTable,bufferAddressValues_eq] using all 213 (by decide)
    · simpa [memoryTable,bufferAddressValues_eq] using all 214 (by decide)
  · refine ⟨?_,?_,?_,?_,by simp only [memoryTable,List.length_replicate];exact le_rfl⟩
    · apply le_trans _ hWM;simpa [memoryTable,bufferAddressValues_eq] using all 200 (by decide)
    · apply le_trans _ hWM;simpa [memoryTable,bufferAddressValues_eq] using all 202 (by decide)
    · apply le_trans _ hWM;simpa [memoryTable,bufferAddressValues_eq] using all 203 (by decide)
    · apply le_trans _ hWM;simpa [memoryTable,bufferAddressValues_eq] using all 204 (by decide)

theorem clockCost_bound (W B : ℕ) (hW : W≤B) (hb : W.bits.length≤B) :
    clockCost W≤2^8*(B+1)^2 := by
  unfold clockCost
  have h := Nat.mul_le_mul (Nat.add_le_add_right hW 1)
    (Nat.add_le_add_right (Nat.mul_le_mul_left 13 hb) 21)
  nlinarith only [h,hW,hb,Nat.zero_le B]

theorem allocationCost_bound (N D B : ℕ)
    (hW : runtimeBudget N≤B) (hM : bufferWidth N D≤B) :
    allocationCost N D B≤2^181*(B+2)^2 := by
  have hb (n : ℕ) : n.bits.length≤n := by
    rw [Nat.size_eq_bits_len,Nat.size_le];exact Nat.lt_two_pow_self
  have ha := allocationArithmeticCost_polynomial B
  have hw := clockCost_bound (runtimeBudget N) B hW ((hb _).trans hW)
  have hm := clockCost_bound (bufferWidth N D) B hM ((hb _).trans hM)
  unfold allocationCost
  nlinarith only [ha,hw,hm,Nat.zero_le B]

#print axioms allocated_metadata
#print axioms allocationCost_bound
end Maxwell.Continuum.Profile.Runtime
