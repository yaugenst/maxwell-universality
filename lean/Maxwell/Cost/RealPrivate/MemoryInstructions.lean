import Maxwell.Cost.RealPrivate.StoreSemantics

namespace Maxwell.Cost.RealPrivate
open RealSimulation.Control

theorem load_instruction (externalInput : RAMInput) (tape : ℕ → Bool)
    {L : Layout} {origin : ℕ} {source : RAMState} {written : List ℕ}
    (s : Store) (h : Represents origin source written s.val) (dst address : ℕ) :
    ∃ t, Executes externalInput tape (instruction L (.load dst address)) 48 s t ∧
      Represents origin (source.setWord dst (source.words (source.indices address)))
        (dst :: written) t.val ∧ CallerFrame origin s.val t.val := by
  have hg := getIndex_correct externalInput tape s h address coordinateRegister (by decide)
  let s1 := indexed s address coordinateRegister
  let a := slot origin 0 (source.indices address)
  let s2 := s1.put pointerRegister a
  have horigin : s1.val.indices originRegister = origin := hg.2.1.origin_word
  have hcoordinate : s1.val.indices coordinateRegister = source.indices address := hg.2.2.1
  have hptr : Executes externalInput tape (bankPointer 0 coordinateRegister) 13 s1 s2 := by
    simpa only [horigin, hcoordinate] using
      bankPointer_executes externalInput tape s1 0 coordinateRegister (by decide)
  have h2 := hg.2.1.put_scratch pointerRegister a
    (by simp [ProtectedIndex, pointerRegister, zeroRegister, oneRegister])
  have hpval : s2.val.indices pointerRegister = a := by simp [s2]
  have hv : s2.val.words (s2.val.indices pointerRegister) = source.words (source.indices address) := by
    rw [hpval]; exact h2.words _
  let s3 := putWord s2 0 (source.words (source.indices address))
  have he : Executes externalInput tape (realLoad 0 pointerRegister) 2 s2 s3 := by
    simpa only [hv] using realLoad_executes externalInput tape s2 0 pointerRegister
  have h3 := h2.word_scratch 0 (source.words (source.indices address)) (by have := h.high; omega)
  have hs := setWord_correct externalInput tape s3 h3 dst 0
  have hv0 : s3.val.words 0 = source.words (source.indices address) := by simp [s3]
  rw [hv0] at hs
  have hp := incrementPC_correct externalInput tape _ hs.2.1
  refine ⟨_, hg.1.seq (hptr.seq (he.seq (hs.1.seq hp.1))), hp.2.1, ?_⟩
  exact hg.2.2.2.trans ((callerFrame_put s1 origin pointerRegister a (Or.inl (by decide))).trans
    ((callerFrame_word s2 origin 0 _ (Or.inl (by decide))).trans (hs.2.2.trans hp.2.2)))

theorem loadIndex_instruction (externalInput : RAMInput) (tape : ℕ → Bool)
    {L : Layout} {origin : ℕ} {source : RAMState} {written : List ℕ}
    (s : Store) (h : Represents origin source written s.val) (dst address : ℕ) :
    ∃ t, Executes externalInput tape (instruction L (.loadIndex dst address)) 48 s t ∧
      Represents origin (source.setIndex dst (source.indices (source.indices address)))
        (dst :: written) t.val ∧ CallerFrame origin s.val t.val := by
  have hg := getIndex_correct externalInput tape s h address coordinateRegister (by decide)
  let s1 := indexed s address coordinateRegister
  let a := slot origin 0 (source.indices address)
  let s2 := s1.put pointerRegister a
  have horigin : s1.val.indices originRegister = origin := hg.2.1.origin_word
  have hcoordinate : s1.val.indices coordinateRegister = source.indices address := hg.2.2.1
  have hptr : Executes externalInput tape (bankPointer 0 coordinateRegister) 13 s1 s2 := by
    simpa only [horigin, hcoordinate] using
      bankPointer_executes externalInput tape s1 0 coordinateRegister (by decide)
  have h2 := hg.2.1.put_scratch pointerRegister a
    (by simp [ProtectedIndex, pointerRegister, zeroRegister, oneRegister])
  have hpval : s2.val.indices pointerRegister = a := by simp [s2]
  have hv : s2.val.indices (s2.val.indices pointerRegister) = source.indices (source.indices address) := by
    rw [hpval]; exact h2.indices _
  let s3 := s2.put valueRegister (source.indices (source.indices address))
  have he : Executes externalInput tape (load valueRegister pointerRegister) 2 s2 s3 := by
    simpa only [hv] using load_executes externalInput tape s2 valueRegister pointerRegister
  have h3 := h2.put_scratch valueRegister (source.indices (source.indices address))
    (by simp [ProtectedIndex, valueRegister, zeroRegister, oneRegister])
  have hs := setIndex_correct externalInput tape s3 h3 dst valueRegister (by decide)
  have hv0 : s3.val.indices valueRegister = source.indices (source.indices address) := by simp [s3]
  rw [hv0] at hs
  have hp := incrementPC_correct externalInput tape _ hs.2.1
  refine ⟨_, hg.1.seq (hptr.seq (he.seq (hs.1.seq hp.1))), hp.2.1, ?_⟩
  exact hg.2.2.2.trans ((callerFrame_put s1 origin pointerRegister a (Or.inl (by decide))).trans
    ((callerFrame_put s2 origin valueRegister _ (Or.inl (by decide))).trans (hs.2.2.trans hp.2.2)))

theorem store_instruction (externalInput : RAMInput) (tape : ℕ → Bool)
    {L : Layout} {origin : ℕ} {source : RAMState} {written : List ℕ}
    (s : Store) (h : Represents origin source written s.val) (address src : ℕ) :
    ∃ t, Executes externalInput tape (instruction L (.store address src)) 46 s t ∧
      Represents origin (source.setWord (source.indices address) (source.words src))
        (source.indices address :: written) t.val ∧ CallerFrame origin s.val t.val := by
  have hg := getIndex_correct externalInput tape s h address coordinateRegister (by decide)
  have hw := getWord_correct externalInput tape _ hg.2.1 src 0 (by decide)
  let s2 := worded (indexed s address coordinateRegister) src 0
  have hc : s2.val.indices coordinateRegister = source.indices address := by
    simpa [s2, worded, putWord, coordinateRegister, pointerRegister] using hg.2.2.1
  let a := slot origin 0 (source.indices address)
  let s3 := s2.put pointerRegister a
  have horigin : s2.val.indices originRegister = origin := hw.2.1.origin_word
  have hptr : Executes externalInput tape (bankPointer 0 coordinateRegister) 13 s2 s3 := by
    simpa only [horigin, hc] using
      bankPointer_executes externalInput tape s2 0 coordinateRegister (by decide)
  have h3 := hw.2.1.put_scratch pointerRegister a
    (by simp [ProtectedIndex, pointerRegister, zeroRegister, oneRegister])
  have hpval : s3.val.indices pointerRegister = a := by simp [s3]
  have hv : s3.val.words 0 = source.words src := hw.2.2.1
  let s4 := putWord s3 a (source.words src)
  have he : Executes externalInput tape (realStore pointerRegister 0) 2 s3 s4 := by
    simpa only [hpval, hv] using realStore_executes externalInput tape s3 pointerRegister 0
  have h4 := h3.private_word (source.indices address) (source.words src)
  have hl := appendLog_executes externalInput tape s4
    (by rw [h4.origin_word]; exact h.high) h4.one
  have hcoord : s4.val.indices coordinateRegister = source.indices address := by
    simpa [s4, s3, putWord, coordinateRegister, pointerRegister] using hc
  have h5 := h4.logged
  change Represents origin _ (s4.val.indices coordinateRegister :: written) (logged s4).val at h5
  rw [hcoord] at h5
  have hp := incrementPC_correct externalInput tape _ h5
  refine ⟨_, hg.1.seq (hw.1.seq (hptr.seq (he.seq (hl.seq hp.1)))), hp.2.1, ?_⟩
  exact hg.2.2.2.trans (hw.2.2.2.trans
    ((callerFrame_put s2 origin pointerRegister a (Or.inl (by decide))).trans
      ((callerFrame_word s3 origin a _ (Or.inr (slot_ge_origin _ _ _))).trans
        ((callerFrame_logged s4 origin h4.origin_word).trans hp.2.2))))

theorem storeIndex_instruction (externalInput : RAMInput) (tape : ℕ → Bool)
    {L : Layout} {origin : ℕ} {source : RAMState} {written : List ℕ}
    (s : Store) (h : Represents origin source written s.val) (address src : ℕ) :
    ∃ t, Executes externalInput tape (instruction L (.storeIndex address src)) 46 s t ∧
      Represents origin (source.setIndex (source.indices address) (source.indices src))
        (source.indices address :: written) t.val ∧ CallerFrame origin s.val t.val := by
  have hg := getIndex_correct externalInput tape s h address coordinateRegister (by decide)
  have hw := getIndex_correct externalInput tape _ hg.2.1 src valueRegister (by decide)
  let s2 := indexed (indexed s address coordinateRegister) src valueRegister
  have hc : s2.val.indices coordinateRegister = source.indices address := by
    simpa [s2, indexed, coordinateRegister, valueRegister, pointerRegister] using hg.2.2.1
  let a := slot origin 0 (source.indices address)
  let s3 := s2.put pointerRegister a
  have horigin : s2.val.indices originRegister = origin := hw.2.1.origin_word
  have hptr : Executes externalInput tape (bankPointer 0 coordinateRegister) 13 s2 s3 := by
    simpa only [horigin, hc] using
      bankPointer_executes externalInput tape s2 0 coordinateRegister (by decide)
  have h3 := hw.2.1.put_scratch pointerRegister a
    (by simp [ProtectedIndex, pointerRegister, zeroRegister, oneRegister])
  have hpval : s3.val.indices pointerRegister = a := by simp [s3]
  have hv : s3.val.indices valueRegister = source.indices src := by
    change (s2.put pointerRegister a).val.indices valueRegister = _
    rw [Store.put_indices, ite_eq_right (by decide : valueRegister ≠ pointerRegister)]
    exact hw.2.2.1
  let s4 := s3.put a (source.indices src)
  have he : Executes externalInput tape (save pointerRegister valueRegister) 2 s3 s4 := by
    simpa only [hpval, hv] using save_executes externalInput tape s3 pointerRegister valueRegister
  have h4 := h3.private_index (source.indices address) (source.indices src)
  have hl := appendLog_executes externalInput tape s4
    (by rw [h4.origin_word]; exact h.high) h4.one
  have hn : coordinateRegister ≠ a := (slot_ne_small h.high 0 _ coordinateRegister (by decide)).symm
  have hcoord : s4.val.indices coordinateRegister = source.indices address := by
    simp only [s4, Store.put_indices, ite_eq_right hn]
    simpa [s3, coordinateRegister, pointerRegister] using hc
  have h5 := h4.logged
  change Represents origin _ (s4.val.indices coordinateRegister :: written) (logged s4).val at h5
  rw [hcoord] at h5
  have hp := incrementPC_correct externalInput tape _ h5
  refine ⟨_, hg.1.seq (hw.1.seq (hptr.seq (he.seq (hl.seq hp.1)))), hp.2.1, ?_⟩
  exact hg.2.2.2.trans (hw.2.2.2.trans
    ((callerFrame_put s2 origin pointerRegister a (Or.inl (by decide))).trans
      ((callerFrame_put s3 origin a _ (Or.inr (Or.inr (slot_ge_origin _ _ _)))).trans
        ((callerFrame_logged s4 origin h4.origin_word).trans hp.2.2))))

end Maxwell.Cost.RealPrivate
