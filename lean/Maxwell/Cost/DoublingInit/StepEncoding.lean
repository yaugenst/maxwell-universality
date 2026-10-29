import Maxwell.Cost.DoublingInit.Encoding

namespace Maxwell.Cost.DoublingInit

theorem represents_step {n : ℕ} {layout : Layout} {memory : ℕ → Bool}
    {a b : Equiv.Perm (Fin n)} {limit : ℕ} (hlt : limit < n)
    (h : Represents layout memory a b limit) (hs : layout.Separated n) :
    Represents layout (stepMemory layout a b ⟨limit,hlt⟩ memory) a b (limit+1) := by
  let i : Fin n := ⟨limit,hlt⟩
  let w := IncidenceEncoding.word layout.route.width i.val
  let p := IncidenceEncoding.word layout.route.width (a (b i)).val
  have hw : w.length=layout.route.width := by simp [w]
  have hp : p.length=layout.route.width := by simp [p]
  have preserve {base : ℕ} {values : Vector (List Bool) n}
      (r : BitArray.Represents memory base layout.route.width values)
      (h2 : IncidenceEncoding.Separated base (n*layout.route.width) (layout.base 2) (n*layout.route.width))
      (h3 : IncidenceEncoding.Separated base (n*layout.route.width) (layout.base 3) (n*layout.route.width))
      (h4 : IncidenceEncoding.Separated base (n*layout.route.width) (layout.base 4) (n*layout.route.width))
      (h5 : IncidenceEncoding.Separated base (n*layout.route.width) (layout.base 5) (n*layout.route.width)) :
      BitArray.Represents (stepMemory layout a b i memory) base layout.route.width values := by
    exact IncidenceEncoding.represents_write_disjoint
      (IncidenceEncoding.represents_write_disjoint
        (IncidenceEncoding.represents_write_disjoint
          (IncidenceEncoding.represents_write_disjoint r _ _ i p hp h2) _ _ i w hw h3) _ _ i w hw h4)
        _ _ i w hw h5
  refine ⟨preserve h.inputA (hs 0 2 (by decide)) (hs 0 3 (by decide)) (hs 0 4 (by decide)) (hs 0 5 (by decide)),
    preserve h.inputB (hs 1 2 (by decide)) (hs 1 3 (by decide)) (hs 1 4 (by decide)) (hs 1 5 (by decide)),?_,?_,?_,?_⟩
  · have hj := h.jump.write_same hlt
    have he : (permutation (a*b)).get i = a (b i) := by simp [Equiv.Perm.mul_apply]
    change Prefix (MemoryWord.writeBits memory (layout.route.oldJump+i.val*layout.route.width)
      (IncidenceEncoding.word layout.route.width ((permutation (a*b)).get i).val)) _ _ _ _ at hj
    rw [he] at hj
    exact ((hj.write_other (hs 2 3 (by decide)) i w hw).write_other
      (hs 2 4 (by decide)) i w hw).write_other (hs 2 5 (by decide)) i w hw
  · have hm := (h.minimum.write_other (hs 3 2 (by decide)) i p hp).write_same hlt
    simp only [identity_get] at hm
    exact (hm.write_other (hs 3 4 (by decide)) i w hw).write_other (hs 3 5 (by decide)) i w hw
  · have hj := ((h.newJump.write_other (hs 4 2 (by decide)) i p hp).write_other
      (hs 4 3 (by decide)) i w hw).write_same hlt
    simp only [identity_get] at hj
    exact hj.write_other (hs 4 5 (by decide)) i w hw
  · have hm := (((h.newMinimum.write_other (hs 5 2 (by decide)) i p hp).write_other
      (hs 5 3 (by decide)) i w hw).write_other (hs 5 4 (by decide)) i w hw).write_same hlt
    simpa [identity_get,stepMemory,Layout.base,p,w,i] using hm

end Maxwell.Cost.DoublingInit
