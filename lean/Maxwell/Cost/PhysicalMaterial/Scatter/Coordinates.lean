import Maxwell.Cost.PhysicalMaterial.Scatter.Offset

namespace Maxwell.Cost.PhysicalMaterial.Scatter
open Structured RationalAccumulator

abbrev Point := Fin 3 → ℤ

def coordinate (anchor : Fin 3 → ℕ) (d : Point) (j : Fin 3) : ℕ :=
  ((anchor j:ℤ)+d j).toNat


theorem coordinate_cast (anchor : Fin 3 → ℕ) (d : Point) (j : Fin 3)
    (h : 0≤(anchor j:ℤ)+d j) :
    (coordinate anchor d j:ℤ) = (anchor j:ℤ)+d j :=
  Int.toNat_of_nonneg h

def coordinateCode (d : Point) : Code :=
  .seq (offsetCode 294 324 (d 0))
    (.seq (offsetCode 295 325 (d 1)) (offsetCode 296 326 (d 2)))

def coordinateWork : Finset ℕ := {0,1,2,3,292,324,325,326}
def coordinateFactor (d : Point) : ℕ := offsetFactor (d 0)+offsetFactor (d 1)+offsetFactor (d 2)
def offsetWidth (d : Point) : ℕ := (d 0).natAbs.bits.length+(d 1).natAbs.bits.length+(d 2).natAbs.bits.length

theorem coordinate_length (anchor : Fin 3 → ℕ) (d : Point) (B : ℕ)
    (hb : ∀ j,(anchor j).bits.length≤B) (j : Fin 3) :
    (coordinate anchor d j).bits.length≤B+offsetWidth d+1 := by
  have hle : coordinate anchor d j ≤ anchor j+(d j).natAbs := by
    unfold coordinate
    cases h : d j with
    | ofNat k =>
      change ((anchor j:ℤ)+(k:ℤ)).toNat ≤ anchor j+k
      omega
    | negSucc k =>
      change ((anchor j:ℤ)+Int.negSucc k).toNat ≤ anchor j+(k+1)
      omega
  have hn := Nat.size_le_size hle
  have hs := IndexedAddress.sum_length_le (anchor j).bits (d j).natAbs.bits
  have hn' : (coordinate anchor d j).bits.length ≤ (anchor j+(d j).natAbs).bits.length := by
    simpa only [Nat.size_eq_bits_len] using hn
  simp only [addressValue_bits] at hs
  have hd : (d j).natAbs.bits.length≤offsetWidth d := by
    fin_cases j
    · change (d 0).natAbs.bits.length≤offsetWidth d
      unfold offsetWidth
      omega
    · change (d 1).natAbs.bits.length≤offsetWidth d
      unfold offsetWidth
      omega
    · change (d 2).natAbs.bits.length≤offsetWidth d
      unfold offsetWidth
      omega
  have ha := hb j
  omega

private theorem offset_mono (target : ℕ) (ht : target=324∨target=325∨target=326) :
    offsetWork target ⊆ coordinateWork := by
  rcases ht with rfl|rfl|rfl <;> decide

set_option maxRecDepth 8192 in
theorem coordinates_executes (d : Point) (anchor : Fin 3 → ℕ) (B : ℕ)
    (hb : ∀ j,(anchor j).bits.length≤B) (hroom : ∀ j,0≤(anchor j:ℤ)+d j)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hw : ∀ j,Word s.val (294+j.val) (anchor j))
    (hz : ∀ j:Fin 3,Blank s.val (324+j.val)) (h292 : Blank s.val 292) (hr : Ready s.val) :
    ∃ cost t, cost≤coordinateFactor d*(B+1) ∧ Executes input tape (coordinateCode d) cost s t ∧
      (∀ j,Word t.val (324+j.val) (coordinate anchor d j)) ∧ Blank t.val 292 ∧ Ready t.val ∧
      BinaryPrecision.Frame coordinateWork s.val t.val := by
  obtain ⟨ac,a,hac,ea,aw,a292,ar,af⟩ := offset_executes 294 324 (by decide) (by decide) (by decide) (by decide)
    (d 0) (anchor 0) B (hb 0) (hroom 0) input tape s (hw 0) (hz 0) h292 hr
  obtain ⟨bc,b,hbc,eb,bw,b292,br,bf⟩ := offset_executes 295 325 (by decide) (by decide) (by decide) (by decide)
    (d 1) (anchor 1) B (hb 1) (hroom 1) input tape a
    (word_of_eq (af.tapes 295 (by decide)) (hw 1)) (blank_of_eq (af.tapes 325 (by decide)) (hz 1)) a292 ar
  obtain ⟨cc,t,hcc,ec,tw,t292,tr,tf⟩ := offset_executes 296 326 (by decide) (by decide) (by decide) (by decide)
    (d 2) (anchor 2) B (hb 2) (hroom 2) input tape b
    (word_of_eq ((bf.tapes 296 (by decide)).trans (af.tapes 296 (by decide))) (hw 2))
    (blank_of_eq ((bf.tapes 326 (by decide)).trans (af.tapes 326 (by decide))) (hz 2)) b292 br
  refine ⟨ac+(bc+cc),t,?_,ea.seq (eb.seq ec),?_,t292,tr,
    (af.mono (offset_mono 324 (Or.inl rfl))).trans
      ((bf.mono (offset_mono 325 (Or.inr (Or.inl rfl)))).trans
        (tf.mono (offset_mono 326 (Or.inr (Or.inr rfl)))))⟩
  · unfold coordinateFactor
    nlinarith
  · intro j
    fin_cases j
    · exact word_of_eq ((tf.tapes 324 (by decide)).trans (bf.tapes 324 (by decide))) aw
    · exact word_of_eq (tf.tapes 325 (by decide)) bw
    · exact tw

end Maxwell.Cost.PhysicalMaterial.Scatter
