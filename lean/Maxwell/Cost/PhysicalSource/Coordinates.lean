import Maxwell.Cost.PhysicalDecoder.Samples

namespace Maxwell.Cost.PhysicalSource.Coordinates
open Structured RationalAccumulator
open PhysicalMaterial.Scatter

def coordinateCode (d : Point) : Code :=
  .seq (offsetCode 294 373 (d 0))
    (.seq (offsetCode 295 374 (d 1)) (offsetCode 296 375 (d 2)))

def coordinateWork : Finset ℕ := {0,1,2,3,292,373,374,375}
private theorem offset_mono (target : ℕ) (ht : target=373∨target=374∨target=375) :
    offsetWork target ⊆ coordinateWork := by
  rcases ht with rfl|rfl|rfl <;> decide

set_option maxRecDepth 8192 in
theorem coordinates_executes (d : Point) (anchor : Fin 3 → ℕ) (B : ℕ)
    (hb : ∀ j,(anchor j).bits.length≤B) (hroom : ∀ j,0≤(anchor j:ℤ)+d j)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hw : ∀ j,Word s.val (294+j.val) (anchor j))
    (hz : ∀ j:Fin 3,Blank s.val (373+j.val)) (h292 : Blank s.val 292) (hr : Ready s.val) :
    ∃ cost t, cost≤coordinateFactor d*(B+1) ∧ Executes input tape (coordinateCode d) cost s t ∧
      (∀ j,Word t.val (373+j.val) (coordinate anchor d j)) ∧ Blank t.val 292 ∧ Ready t.val ∧
      BinaryPrecision.Frame coordinateWork s.val t.val := by
  obtain ⟨ac,a,hac,ea,aw,a292,ar,af⟩ := offset_executes 294 373 (by decide) (by decide) (by decide) (by decide)
    (d 0) (anchor 0) B (hb 0) (hroom 0) input tape s (hw 0) (hz 0) h292 hr
  obtain ⟨bc,b,hbc,eb,bw,b292,br,bf⟩ := offset_executes 295 374 (by decide) (by decide) (by decide) (by decide)
    (d 1) (anchor 1) B (hb 1) (hroom 1) input tape a
    (word_of_eq (af.tapes 295 (by decide)) (hw 1)) (blank_of_eq (af.tapes 374 (by decide)) (hz 1)) a292 ar
  obtain ⟨cc,t,hcc,ec,tw,t292,tr,tf⟩ := offset_executes 296 375 (by decide) (by decide) (by decide) (by decide)
    (d 2) (anchor 2) B (hb 2) (hroom 2) input tape b
    (word_of_eq ((bf.tapes 296 (by decide)).trans (af.tapes 296 (by decide))) (hw 2))
    (blank_of_eq ((bf.tapes 375 (by decide)).trans (af.tapes 375 (by decide))) (hz 2)) b292 br
  refine ⟨ac+(bc+cc),t,?_,ea.seq (eb.seq ec),?_,t292,tr,
    (af.mono (offset_mono 373 (Or.inl rfl))).trans
      ((bf.mono (offset_mono 374 (Or.inr (Or.inl rfl)))).trans
        (tf.mono (offset_mono 375 (Or.inr (Or.inr rfl)))))⟩
  · unfold coordinateFactor
    nlinarith
  · intro j
    fin_cases j
    · exact word_of_eq ((tf.tapes 373 (by decide)).trans (bf.tapes 373 (by decide))) aw
    · exact word_of_eq (tf.tapes 374 (by decide)) bw
    · exact tw

end Maxwell.Cost.PhysicalSource.Coordinates
