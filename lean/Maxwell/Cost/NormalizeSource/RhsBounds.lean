import Maxwell.Cost.NormalizeSource.SourceData
import Maxwell.Logical.SourceRounding

namespace Maxwell.Cost.NormalizeSource
open Logical Logical.Normalization

theorem nearest_numerator_le (precision : ℕ) (q : ℚ) (hq : |q| ≤ 1) :
    (Rounding.nearest precision q).numerator.natAbs ≤ 2^precision := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp hq
  have hp : (0:ℚ) < 2^precision := by positivity
  have hupper : (Rounding.nearest precision q).numerator ≤ (2^precision:ℤ) := by
    apply Int.floor_le_iff.mpr
    norm_cast
    push_cast
    nlinarith
  have hlower : -(2^precision:ℤ) ≤ (Rounding.nearest precision q).numerator := by
    apply Int.le_floor.mpr
    push_cast
    nlinarith
  have ha := abs_le.mpr ⟨hlower, hupper⟩
  rw [← Int.natCast_natAbs] at ha
  exact_mod_cast ha

theorem nearest_numerator_bits (precision : ℕ) (q : ℚ) (hq : |q| ≤ 1) :
    (Rounding.nearest precision q).numerator.natAbs.bits.length ≤ precision+1 := by
  have h := Nat.size_le_size (nearest_numerator_le precision q hq)
  rw [Nat.size_pow] at h
  simpa only [Nat.size_eq_bits_len] using h

theorem source_rounded_bits (S : Source.SparseSystem) (hb : S.source ≠ 0)
    (precision : ℕ) (q : ℚ) (hq : q ∈ List.ofFn S.source) :
    (roundedNumerator (NormalizeRatio.sourceScalePair S).1
      (NormalizeRatio.sourceScalePair S).2 precision q).natAbs.bits.length ≤ precision+1 := by
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hq
  unfold roundedNumerator
  rw [NormalizeRatio.sourceScalePair_value]
  exact nearest_numerator_bits precision _ (normalizedSource_bound S hb i)

/-- The shared denominator and the archived integer denote exactly the
rounded source used in the analytic and logical recovery proof. -/
theorem source_rounded_value (S : Source.SparseSystem) (precision : ℕ) (i : Fin S.n) :
    (roundedNumerator (NormalizeRatio.sourceScalePair S).1
      (NormalizeRatio.sourceScalePair S).2 precision (S.source i) : ℚ) / 2^precision =
        roundedSource S precision i := by
  unfold roundedNumerator
  rw [NormalizeRatio.sourceScalePair_value]
  rfl

theorem source_rhs_width (p : Source.Parameters) (S : Source.SparseSystem)
    (hp : Source.Promises p S) (precision : ℕ) :
    ∀ q ∈ List.ofFn S.source, ∀ i, 30 ≤ i → i ≤ 34 →
      (NormalizeCoefficient.values (Codec.RationalPair.canonical q)
        (NormalizeRatio.sourceScalePair S).1 (NormalizeRatio.sourceScalePair S).2 precision i).bits.length ≤
          sourceWidth p S precision := by
  have hw := MagnitudeMax.promised_rhs_width p S hp
  have hm := MagnitudeMax.maximum_width (List.ofFn S.source) (MagnitudeMax.inputWidth p S)
    (MagnitudeMax.inputWidth p S) (MagnitudeMax.inputWidth_pos p S)
    (fun q hq => (hw q hq).1) (fun q hq => (hw q hq).2)
  intro q hq i hi hj
  obtain ⟨hn, hd⟩ := hw q hq
  interval_cases i
  all_goals simp only [NormalizeCoefficient.values, Function.update_apply, Codec.RationalPair.canonical]
  all_goals norm_num
  all_goals first
    | (dsimp [sourceWidth, NormalizeRatio.sourceScalePair] at *; omega)
    | (rw [PowerOfTwo.power_bits]; simp; dsimp [sourceWidth]; omega)

end Maxwell.Cost.NormalizeSource
