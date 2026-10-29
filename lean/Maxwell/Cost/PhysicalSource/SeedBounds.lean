import Maxwell.Cost.PhysicalSource.SeedArithmetic

namespace Maxwell.Cost.PhysicalSource.SeedArithmetic
open RationalAccumulator

def inputIds : Finset ℕ := {361,362,363,364,365,366,367,506,507}

private theorem four_scaled_pair_bound (a b c d beta B : ℕ)
    (ha : a.bits.length≤B) (hb : b.bits.length≤B) (hc : c.bits.length≤B)
    (hd : d.bits.length≤B) (he : beta.bits.length≤B) :
    (4*beta*(a*b+c*d)).bits.length≤3*B+4 := by
  have hp := bits_mul_le a b
  have hq := bits_mul_le c d
  have hs := bits_add_le (a*b) (c*d)
  have ht := bits_mul_le 4 beta
  have hu := bits_mul_le (4*beta) (a*b+c*d)
  have hf : (4:ℕ).bits.length=3 := rfl
  omega

theorem positive_bits (v : ℕ→ℕ) (B : ℕ)
    (h : ∀ i ∈ inputIds, (v i).bits.length≤B) : (positive v).bits.length≤3*B+4 :=
  four_scaled_pair_bound _ _ _ _ _ B (h _ (by decide)) (h _ (by decide))
    (h _ (by decide)) (h _ (by decide)) (h _ (by decide))

theorem negative_bits (v : ℕ→ℕ) (B : ℕ)
    (h : ∀ i ∈ inputIds, (v i).bits.length≤B) : (negative v).bits.length≤3*B+4 :=
  four_scaled_pair_bound _ _ _ _ _ B (h _ (by decide)) (h _ (by decide))
    (h _ (by decide)) (h _ (by decide)) (h _ (by decide))

theorem denominator_bits (v : ℕ→ℕ) (B : ℕ)
    (h : ∀ i ∈ inputIds, (v i).bits.length≤B) : (denominator v).bits.length≤4*B := by
  have h1 := h 361 (by decide)
  have h2 := h 364 (by decide)
  have h3 := h 365 (by decide)
  have h4 := h 506 (by decide)
  have hp := bits_mul_le (v 361) (v 364)
  have hq := bits_mul_le (v 361*v 364) (v 365)
  have hr := bits_mul_le (v 361*v 364*v 365) (v 506)
  exact hr.trans (by omega)

end Maxwell.Cost.PhysicalSource.SeedArithmetic
