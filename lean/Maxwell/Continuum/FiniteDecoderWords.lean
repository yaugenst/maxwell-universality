import Maxwell.Continuum.FiniteDecoderCost

/-! Bounds on the actual standalone decoder wire from its stored scalar
fields and rational stencils. -/

namespace Maxwell.Continuum.FiniteDecoder
open Maxwell.Cost Maxwell.Cost.DecoderParser
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

theorem maxWidth_le_of_bound (shape : Shape) (x : Payload shape) (B : ℕ)
    (h : WidthBound shape x B) : maxWidth shape x≤B := by
  induction shape with
  | bit => exact Nat.zero_le _
  | nat => exact h
  | pair left right ihl ihr => exact max_le (ihl x.1 h.1) (ihr x.2 h.2)
  | list element ih =>
    apply max_le h.1
    have hall := h.2
    clear h
    induction x with
    | nil => exact Nat.zero_le _
    | cons a xs ihxs =>
      exact max_le (ih a (hall a (by simp))) (ihxs (fun q hq => hall q (by simp [hq])))

theorem rational_width {q : ℚ} {B : ℕ} (h : Source.ShortRational B q) :
    WidthBound rationalShape (rationalPayload q) B := by
  have hn : signedBitLength q.num≤B := by exact_mod_cast h.1
  have hd : unsignedBitLength q.den≤B := by exact_mod_cast h.2
  simp only [signedBitLength,Codec.unsignedBitLength_eq_size,← Nat.size_eq_bits_len] at hn hd
  refine ⟨trivial,?_,hd⟩
  change q.num.natAbs.bits.length≤B
  omega

theorem description_width {ι : Type*} {n : ℕ} (D : Target.WeightedDecoder ι n) (B K : ℕ)
    (hn : n.bits.length≤B) (hI : D.format.integerBits.bits.length≤B)
    (hP : D.format.fractionalBits.bits.length≤B) (hJ : D.sampleCount.bits.length≤B)
    (hK : K.bits.length≤B) (hoffset : ∀i,Source.ShortRational B (D.offset i))
    (hweight : ∀i j,j∈D.support i → Source.ShortRational B (D.weight i j))
    (hsupport : ∀i,(D.support i).card≤K) :
    maxWidth descriptionShape (descriptionData D)≤B := by
  apply maxWidth_le_of_bound
  refine ⟨⟨hn,hI,hP,hJ⟩,?_,?_⟩
  · rw [rowData_length D]
    exact hn
  · intro row hrow
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hrow
    refine ⟨rational_width (hoffset i),?_,?_⟩
    · have h := Nat.size_le_size (hsupport i)
      simp only [← Nat.size_eq_bits_len] at h
      simpa using h.trans hK
    · intro term hterm
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hterm
      have h := Nat.size_le_size j.isLt.le
      simp only [← Nat.size_eq_bits_len] at h
      exact ⟨h.trans hJ,rational_width (hweight i j (by simpa using hj))⟩

private theorem natural_wire_length (n B : ℕ) (h : n.bits.length≤B) :
    (Codec.nat n).length≤2*B+1 := by
  simpa only [Codec.nat_length,Codec.unsignedBitLength_eq_size,← Nat.size_eq_bits_len] using
    (show 2*n.bits.length+1≤2*B+1 by omega)

theorem description_length {ι : Type*} {n : ℕ} (D : Target.WeightedDecoder ι n) (B K : ℕ)
    (hn : n.bits.length≤B) (hI : D.format.integerBits.bits.length≤B)
    (hP : D.format.fractionalBits.bits.length≤B) (hJ : D.sampleCount.bits.length≤B)
    (hK : K.bits.length≤B) (hoffset : ∀i,Source.ShortRational B (D.offset i))
    (hweight : ∀i j,j∈D.support i → Source.ShortRational B (D.weight i j))
    (hsupport : ∀i,(D.support i).card≤K) :
    (description D).length≤16*(n+1)*(K+1)*(B+1) := by
  have hheader : (beforeRows D).length≤8*B+4 := by
    have h1 := natural_wire_length n B hn
    have h2 := natural_wire_length D.format.integerBits B hI
    have h3 := natural_wire_length D.format.fractionalBits B hP
    have h4 := natural_wire_length D.sampleCount B hJ
    simp only [beforeRows,headerData,wire,List.length_append]
    omega
  have hrows : ∀row∈rows D,(rowWire row).length≤8*(K+1)*(B+1) := by
    intro row hrow
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hrow
    have ho := Codec.rat_length_le (hoffset i)
    have hc : (rowTerms D i).length≤K := by simpa [rowTerms] using hsupport i
    have hcb : unsignedBitLength (rowTerms D i).length≤B := by
      have hh := Nat.size_le_size hc
      simpa only [Codec.unsignedBitLength_eq_size,← Nat.size_eq_bits_len] using
        (show (rowTerms D i).length.bits.length≤B by
          simp only [← Nat.size_eq_bits_len] at hh
          omega)
    have ht := Codec.list_length_le termWire (rowTerms D i) (6*B+2) (by
      intro term hterm
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hterm
      have hh := Nat.size_le_size j.isLt.le
      simp only [← Nat.size_eq_bits_len] at hh
      have hi := natural_wire_length j.val B (hh.trans hJ)
      have hw := Codec.rat_length_le (hweight i j (by simpa using hj))
      simp only [termWire,List.length_append]
      omega)
    have hm := Nat.mul_le_mul_right (6*B+2) hc
    change (Codec.rat (D.offset i)++Codec.list termWire (rowTerms D i)).length≤_
    simp only [List.length_append]
    nlinarith only [ho,hcb,ht,hm,Nat.zero_le B,Nat.zero_le K]
  have hr := Codec.flatMap_length_le rowWire (rows D) (8*(K+1)*(B+1)) hrows
  rw [rows_length] at hr
  have hnwire := natural_wire_length n B hn
  rw [description_rows]
  simp only [List.length_append]
  have hbase : 10*B+5≤16*(K+1)*(B+1) := by nlinarith only [Nat.zero_le B,Nat.zero_le K]
  have hprod := Nat.mul_le_mul_left (n*(K+1)*(B+1)) (show 8≤16 by decide)
  nlinarith only [hheader,hnwire,hr,hbase,hprod]

#print axioms description_width
#print axioms description_length

end Maxwell.Continuum.FiniteDecoder
