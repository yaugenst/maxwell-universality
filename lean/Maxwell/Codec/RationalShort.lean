import Maxwell.Codec.RationalArithmetic
import Maxwell.Cost.RationalCanonical.Value

/-! Canonical reduction cannot enlarge a literal rational-pair budget. The
result applies to every bounded access message, without an accuracy premise. -/
namespace Maxwell.Codec.RationalPair

theorem value_short {B : ℕ} {q : RationalPair} (h : q.Short B) :
    Source.ShortRational (B:ℝ) q.value := by
  have he : q.value = Cost.RationalCanonical.value (decide (q.numerator < 0))
      q.numerator.natAbs q.denominator := by
    unfold value Cost.RationalCanonical.value
    congr 1
    by_cases hn : q.numerator < 0
    · simp only [hn,decide_true,↓reduceIte]
      have hz : -(q.numerator.natAbs:ℤ) = q.numerator := by
        rw [Int.ofNat_natAbs_of_nonpos hn.le,neg_neg]
      exact_mod_cast hz.symm
    · simp only [hn,decide_false,Bool.false_eq_true,↓reduceIte]
      exact congrArg (fun z : ℤ => (z:ℚ))
        (Int.natAbs_of_nonneg (le_of_not_gt hn)).symm
  rw [he]
  constructor
  · unfold signedBitLength
    rw [Cost.RationalCanonical.value_num_natAbs _ _ _ q.denominator_pos]
    have hh := unsignedBitLength_mono (Nat.div_le_self q.numerator.natAbs
      (Nat.gcd q.numerator.natAbs q.denominator))
    exact_mod_cast (show unsignedBitLength
      (q.numerator.natAbs/Nat.gcd q.numerator.natAbs q.denominator)+1 ≤ B by
      have hh' := h.1
      unfold signedBitLength at hh'
      omega)
  · rw [Cost.RationalCanonical.value_den _ _ _ q.denominator_pos]
    exact_mod_cast (unsignedBitLength_mono (Nat.div_le_self q.denominator
      (Nat.gcd q.numerator.natAbs q.denominator))).trans h.2

end Maxwell.Codec.RationalPair

namespace Maxwell.Source.ShortRational

theorem mono {a b : ℝ} {q : ℚ} (h : ShortRational a q) (hab : a ≤ b) :
    ShortRational b q := ⟨h.1.trans hab,h.2.trans hab⟩

theorem zero : ShortRational (1:ℝ) (0:ℚ) := by
  norm_num [ShortRational,signedBitLength,unsignedBitLength]

theorem mul {A B : ℕ} {a b : ℚ} (ha : ShortRational A a) (hb : ShortRational B b) :
    ShortRational ((A+B:ℕ):ℝ) (a*b) := by
  simpa only [Codec.RationalPair.mul_value,Codec.RationalPair.canonical_value] using
    Codec.RationalPair.value_short
      (Codec.RationalPair.mul_short (Codec.RationalPair.canonical_short ha)
        (Codec.RationalPair.canonical_short hb))

theorem add {A B : ℕ} {a b : ℚ} (ha : ShortRational A a) (hb : ShortRational B b) :
    ShortRational ((A+B+1:ℕ):ℝ) (a+b) := by
  simpa only [Codec.RationalPair.add_value,Codec.RationalPair.canonical_value] using
    Codec.RationalPair.value_short
      (Codec.RationalPair.add_short (Codec.RationalPair.canonical_short ha)
        (Codec.RationalPair.canonical_short hb))

end Maxwell.Source.ShortRational

namespace Maxwell.Codec

theorem decoder_value_short {ι : Type*} {n B : ℕ} (D : Target.WeightedDecoder ι n)
    (messages : D.Messages) (i : Fin n)
    (hoffset : Source.ShortRational B (D.offset i))
    (hweights : ∀ j ∈ D.support i, Source.ShortRational B (D.weight i j)) :
    Source.ShortRational ((B+(D.support i).card*(B+D.format.width+2):ℕ):ℝ)
      (D.decode messages i) := by
  simpa only [decoderPairs_value] using
    RationalPair.value_short (decoderPairs_short D messages i hoffset hweights)

end Maxwell.Codec
