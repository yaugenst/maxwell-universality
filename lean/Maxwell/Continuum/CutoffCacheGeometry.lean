import Maxwell.Continuum.CutoffCacheDimensions

/-! The computed cache width accommodates every address and clock word.
Both buffers are disjoint without any premise about their old contents. -/
namespace Maxwell.Continuum.Calibration.RawCutoff
open RationalDataflow RationalDataflow.PartArray Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

theorem cache_nat_bits_le (n : ℕ) : n.bits.length≤n := by
  rw [Nat.size_eq_bits_len,Nat.size_le]
  exact Nat.lt_two_pow_self

theorem cache_working_pos (D W : ℕ) : 0<monomialWorkingWidth D W := by
  unfold monomialWorkingWidth
  omega

theorem cache_width_bits (D W : ℕ) :
    (monomialWorkingWidth D W).bits.length≤monomialStorageWidth D W+6 := by
  have h := RationalAccumulator.bits_mul_le 16 (monomialStorageWidth D W+1)
  have hsmall := cache_nat_bits_le (monomialStorageWidth D W+1)
  rw [show (16:ℕ).bits.length=5 from rfl] at h
  change (16*(monomialStorageWidth D W+1)).bits.length≤_
  omega

theorem cache_next_base_bits (D W heap : ℕ) :
    (cacheNextBase D W heap).bits.length≤heap.bits.length+(4*(D+1)).bits.length+
      (monomialWorkingWidth D W).bits.length+3 := by
  have h3 := RationalAccumulator.bits_mul_le 3 (4*(D+1))
  have hp := RationalAccumulator.bits_mul_le (3*(4*(D+1))) (monomialWorkingWidth D W)
  have ha := RationalAccumulator.bits_add_le heap (3*(4*(D+1))*monomialWorkingWidth D W)
  rw [show (3:ℕ).bits.length=2 from rfl] at h3
  unfold cacheNextBase
  omega

theorem cache_header_bound (D W heap : ℕ) (hh : heap.bits.length≤W) :
    heap.bits.length+(4*(D+1)).bits.length+(monomialWorkingWidth D W).bits.length+4≤
      monomialWorkingWidth D W ∧
    (cacheNextBase D W heap).bits.length+(4*(D+1)).bits.length+
      (monomialWorkingWidth D W).bits.length+4≤monomialWorkingWidth D W := by
  have hn := cache_nat_bits_le (4*(D+1))
  have hb := cache_width_bits D W
  have hnext := cache_next_base_bits D W heap
  unfold monomialWorkingWidth monomialStorageWidth at hb hnext ⊢
  omega

theorem cache_table_metadata (D W heap : ℕ) (hh : heap.bits.length≤W) (memory : ℕ→Bool) :
    (Profile.Runtime.memoryTable (4*(D+1)) (monomialWorkingWidth D W) heap
      (cache_working_pos D W) memory).MetadataWidth (monomialWorkingWidth D W) ∧
    (Profile.Runtime.memoryTable (4*(D+1)) (monomialWorkingWidth D W) (cacheNextBase D W heap)
      (cache_working_pos D W) memory).MetadataWidth (monomialWorkingWidth D W) := by
  have h := cache_header_bound D W heap hh
  exact ⟨Profile.Runtime.memoryTable_metadata _ _ _ _ _ _ le_rfl h.1,
    Profile.Runtime.memoryTable_metadata _ _ _ _ _ _ le_rfl h.2⟩

theorem cache_buffers_separated (D W heap : ℕ) (memory memory' : ℕ→Bool) :
    (Profile.Runtime.memoryTable (4*(D+1)) (monomialWorkingWidth D W) heap
      (cache_working_pos D W) memory).SeparatedFrom
    (Profile.Runtime.memoryTable (4*(D+1)) (monomialWorkingWidth D W) (cacheNextBase D W heap)
      (cache_working_pos D W) memory') := by
  have h := Profile.Runtime.memoryTable_separatedFrom (4*(D+1)) (4*(D+1))
    (monomialWorkingWidth D W) (monomialWorkingWidth D W) heap (cacheNextBase D W heap)
    (cache_working_pos D W) (cache_working_pos D W) memory le_rfl
  simpa only [Table.SeparatedFrom,Profile.Runtime.memoryTable] using h

#print axioms cache_header_bound
#print axioms cache_table_metadata
#print axioms cache_buffers_separated
end Maxwell.Continuum.Calibration.RawCutoff
