import Maxwell.Cost.DecoderParser.Result

namespace Maxwell.Cost.DecoderParser

def formatTermWidth (F : Target.FixedPointFormat) (q : ℚ) : ℕ :=
  3*F.width+q.num.natAbs.bits.length+q.den.bits.length+4

theorem termWidth_le (F : Target.FixedPointFormat) (q : ℚ) (w : F.Word) :
    termWidth F q (Codec.word F w) ≤ formatTermWidth F q := by
  simp only [termWidth,formatTermWidth,Codec.word_length,Nat.size_eq_bits_len,Nat.size_pow,
    Target.FixedPointFormat.width]
  omega

def rowWidth {N : ℕ} (F : Target.FixedPointFormat) (row : Row N) : ℕ :=
  offsetWidth row.1+(row.2.map (fun x => formatTermWidth F x.2+1)).sum

theorem rowWidth_le {ι : Type*} {n : ℕ} (D : Target.WeightedDecoder ι n) (w : D.Messages)
    (row : Row D.sampleCount) : offsetWidth row.1+termsWidth D w row.2 ≤ rowWidth D.format row := by
  apply Nat.add_le_add_left
  unfold termsWidth
  induction row.2 with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons,List.sum_cons]
    exact Nat.add_le_add (Nat.add_le_add_right (termWidth_le D.format x.2 (w x.1)) 1) ih

def decoderWidth {ι : Type*} {n : ℕ} (D : Target.WeightedDecoder ι n) : ℕ :=
  (rows D).foldr (fun row bound => max (rowWidth D.format row) bound) 0

private theorem le_foldr_max {α : Type*} (f : α → ℕ) (xs : List α) (x : α) (h : x ∈ xs) :
    f x ≤ xs.foldr (fun y b => max (f y) b) 0 := by
  induction xs with
  | nil => simp at h
  | cons y ys ih =>
    simp only [List.mem_cons] at h
    rcases h with rfl|h
    · exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

theorem decoderWidth_spec {ι : Type*} {n : ℕ} (D : Target.WeightedDecoder ι n) (w : D.Messages)
    (row : Row D.sampleCount) (h : row ∈ rows D) :
    offsetWidth row.1+termsWidth D w row.2 ≤ decoderWidth D :=
  (rowWidth_le D w row).trans (le_foldr_max (rowWidth D.format) (rows D) row h)

theorem offsetWidth_le (q : ℚ) (B : ℕ) (h : Source.ShortRational B q) : offsetWidth q ≤ 2*B := by
  have hh := Codec.RationalPair.canonical_short h
  simp only [Codec.RationalPair.Short,Codec.RationalPair.canonical,signedBitLength,
    Codec.unsignedBitLength_eq_size,← Nat.size_eq_bits_len] at hh
  unfold offsetWidth
  omega

theorem formatTermWidth_le (F : Target.FixedPointFormat) (q : ℚ) (B : ℕ)
    (h : Source.ShortRational B q) : formatTermWidth F q ≤ 3*F.width+2*B+4 := by
  have hh := Codec.RationalPair.canonical_short h
  simp only [Codec.RationalPair.Short,Codec.RationalPair.canonical,signedBitLength,
    Codec.unsignedBitLength_eq_size,← Nat.size_eq_bits_len] at hh
  unfold formatTermWidth
  omega

theorem decoderWidth_bound {ι : Type*} {n : ℕ} (D : Target.WeightedDecoder ι n) (B K : ℕ)
    (hoffset : ∀ i, Source.ShortRational B (D.offset i))
    (hweight : ∀ i j, j ∈ D.support i → Source.ShortRational B (D.weight i j))
    (hsupport : ∀ i, (D.support i).card ≤ K) :
    decoderWidth D ≤ 2*B+K*(3*D.format.width+2*B+5) := by
  have hrow (row : Row D.sampleCount) (hr : row ∈ rows D) :
      rowWidth D.format row ≤ 2*B+K*(3*D.format.width+2*B+5) := by
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hr
    have hoff := offsetWidth_le (D.offset i) B (hoffset i)
    have hsum : (((rowTerms D i).map fun x => formatTermWidth D.format x.2+1)).sum ≤
        (rowTerms D i).length*(3*D.format.width+2*B+5) := by
      have hh := List.sum_le_length_nsmul
        ((rowTerms D i).map fun x => formatTermWidth D.format x.2+1)
        (3*D.format.width+2*B+5) (by
          intro a ha
          obtain ⟨x,hx,rfl⟩ := List.mem_map.mp ha
          obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hx
          have ht := formatTermWidth_le D.format (D.weight i j) B (hweight i j (by simpa using hj))
          change formatTermWidth D.format (D.weight i j)+1 ≤ _
          omega)
      simpa using hh
    have hlen : (rowTerms D i).length ≤ K := by simpa [rowTerms] using hsupport i
    have hmul := Nat.mul_le_mul_right (3*D.format.width+2*B+5) hlen
    dsimp [rowWidth]
    omega
  unfold decoderWidth
  generalize rows D=rs at *
  induction rs with
  | nil => simp
  | cons row rs ih =>
    apply max_le (hrow row (by simp))
    exact ih (by intro x hx;exact hrow x (by simp [hx]))

end Maxwell.Cost.DecoderParser
