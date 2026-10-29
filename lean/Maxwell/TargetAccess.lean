import Maxwell.Target

/-!
# Existence of bounded fixed-width physical readout

Every real coordinate in the declared half-open signed range admits a word
of exactly the emitted width with error at most one fractional unit. The
proof uses the floor of the scaled coordinate and offset-binary storage.
It proves existence of valid access messages, not a computational real oracle.
-/

namespace Maxwell.Target.FixedPointFormat

theorem exists_accurate_word (F : FixedPointFormat) (x : ℝ) (hx : F.InRange x) :
    ∃ w : F.Word, |(F.value w : ℝ) - x| ≤ 1 / (2 : ℝ) ^ F.fractionalBits := by
  let z : ℤ := ⌊x * (2 : ℝ) ^ F.fractionalBits⌋
  let bound : ℤ := 2 ^ (F.integerBits + F.fractionalBits)
  have hs : (0 : ℝ) < 2 ^ F.fractionalBits := by positivity
  have hbound : (bound : ℝ) =
      (2 : ℝ) ^ F.integerBits * (2 : ℝ) ^ F.fractionalBits := by
    simp [bound, pow_add]
  have hzlo : -bound ≤ z := by
    apply Int.le_floor.mpr
    push_cast
    rw [hbound]
    simpa only [neg_mul] using mul_le_mul_of_nonneg_right hx.1 hs.le
  have hzhi : z < bound := by
    apply Int.floor_lt.mpr
    rw [hbound]
    exact mul_lt_mul_of_pos_right hx.2 hs
  have hoff : 0 ≤ z + bound := by omega
  have hwidth : ((2 ^ F.width : ℕ) : ℤ) = 2 * bound := by
    simp [width, bound, Nat.add_assoc, pow_add]
  have hw : (z + bound).toNat < 2 ^ F.width := by
    have hh : ((z + bound).toNat : ℤ) < ((2 ^ F.width : ℕ) : ℤ) := by
      rw [Int.toNat_of_nonneg hoff, hwidth]
      omega
    exact_mod_cast hh
  let w : F.Word := ⟨(z + bound).toNat, hw⟩
  have hnum : F.numerator w = z := by
    simp [numerator, w, Int.toNat_of_nonneg hoff, bound]
  have hvalue : (F.value w : ℝ) = (z : ℝ) / (2 : ℝ) ^ F.fractionalBits := by
    simp [value, hnum]
  have hfloor : (z : ℝ) ≤ x * (2 : ℝ) ^ F.fractionalBits := Int.floor_le _
  have hnext : x * (2 : ℝ) ^ F.fractionalBits < (z : ℝ) + 1 :=
    Int.lt_floor_add_one _
  have hupper : (z : ℝ) / (2 : ℝ) ^ F.fractionalBits ≤ x :=
    (div_le_iff₀ hs).mpr hfloor
  have hlower : x - 1 / (2 : ℝ) ^ F.fractionalBits <
      (z : ℝ) / (2 : ℝ) ^ F.fractionalBits := by
    apply (lt_div_iff₀ hs).mpr
    have hi : (1 / (2 : ℝ) ^ F.fractionalBits) * (2 : ℝ) ^ F.fractionalBits = 1 :=
      one_div_mul_cancel hs.ne'
    nlinarith
  refine ⟨w, ?_⟩
  rw [hvalue, abs_le]
  have hinv : (0 : ℝ) ≤ 1 / (2 : ℝ) ^ F.fractionalBits := by positivity
  constructor <;> linarith

end Maxwell.Target.FixedPointFormat

namespace Maxwell.Target.WeightedDecoder

/-- A declared range bound for every sampled coordinate supplies an accurate
message in the finite fixed-width message type for every such physical vector. -/
theorem exists_accurate_messages {ι : Type*} {n : ℕ} (D : WeightedDecoder ι n)
    (y : ι → ℝ) (hy : D.Fits y) : ∃ w : D.Messages, D.Accurate w y := by
  have h : ∀ j, ∃ w : D.format.Word,
      |(D.format.value w : ℝ) - y (D.coordinate j)| ≤
        1 / (2 : ℝ) ^ D.format.fractionalBits := by
    intro j
    exact D.format.exists_accurate_word (y (D.coordinate j)) (hy j)
  choose w hw using h
  exact ⟨w, hw⟩

end Maxwell.Target.WeightedDecoder
