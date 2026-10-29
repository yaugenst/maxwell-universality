import Maxwell.Cost.RealPrivate.StoreSemantics

namespace Maxwell.Cost.RealPrivate
open RealSimulation.Control

theorem literal_instruction (externalInput : RAMInput) (tape : ℕ → Bool)
    {L : Layout} {origin : ℕ} {source : RAMState} {written : List ℕ}
    (s : Store) (h : Represents origin source written s.val) (dst : ℕ) (q : ℚ) :
    ∃ t, Executes externalInput tape (instruction L (.literal dst q)) 29 s t ∧
      Represents origin (source.setWord dst q) (dst :: written) t.val ∧
      CallerFrame origin s.val t.val := by
  let s0 := putWord s 0 q
  have h0 := h.word_scratch 0 (q : ℝ) (by have := h.high; omega)
  have hs := setWord_correct externalInput tape s0 h0 dst 0
  have hv : s0.val.words 0 = q := by simp [s0]
  rw [hv] at hs
  have hp := incrementPC_correct externalInput tape _ hs.2.1
  refine ⟨_, (realLiteral_executes externalInput tape s 0 q).seq (hs.1.seq hp.1), hp.2.1, ?_⟩
  exact (callerFrame_word s origin 0 _ (Or.inl (by decide))).trans (hs.2.2.trans hp.2.2)

theorem copy_instruction (externalInput : RAMInput) (tape : ℕ → Bool)
    {L : Layout} {origin : ℕ} {source : RAMState} {written : List ℕ}
    (s : Store) (h : Represents origin source written s.val) (dst src : ℕ) :
    ∃ t, Executes externalInput tape (instruction L (.copy dst src)) 33 s t ∧
      Represents origin (source.setWord dst (source.words src)) (dst :: written) t.val ∧
      CallerFrame origin s.val t.val := by
  have hg := getWord_correct externalInput tape s h src 0 (by decide)
  have hs := setWord_correct externalInput tape _ hg.2.1 dst 0
  rw [hg.2.2.1] at hs
  have hp := incrementPC_correct externalInput tape _ hs.2.1
  exact ⟨_, hg.1.seq (hs.1.seq hp.1), hp.2.1, hg.2.2.2.trans (hs.2.2.trans hp.2.2)⟩

/-- A binary arithmetic block uses an independently proved execution of
its literal two-instruction primitive. The source operands are fetched
before any destination write, including aliased destinations. -/
theorem binary_word_instruction (externalInput : RAMInput) (tape : ℕ → Bool)
    {origin : ℕ} {source : RAMState} {written : List ℕ}
    (s : Store) (h : Represents origin source written s.val)
    (dst left right : ℕ) (compute : Code) (f : ℝ → ℝ → ℝ)
    (execute : ∀ v : Store, Executes externalInput tape compute 2 v
      (putWord v 2 (f (v.val.words 0) (v.val.words 1)))) :
    ∃ t, Executes externalInput tape
        (block [getWord left 0, getWord right 1, compute, setWord dst 2, incrementPC]) 41 s t ∧
      Represents origin (source.setWord dst (f (source.words left) (source.words right)))
        (dst :: written) t.val ∧ CallerFrame origin s.val t.val := by
  have hl := getWord_correct externalInput tape s h left 0 (by decide)
  have hr := getWord_correct externalInput tape _ hl.2.1 right 1 (by decide)
  let s2 := worded (worded s left 0) right 1
  have hleft : s2.val.words 0 = source.words left := by
    simpa [s2, worded, Store.put, putWord] using hl.2.2.1
  have hright : s2.val.words 1 = source.words right := hr.2.2.1
  let value := f (source.words left) (source.words right)
  let s3 := putWord s2 2 value
  have hc : Executes externalInput tape compute 2 s2 s3 := by
    simpa only [hleft, hright] using execute s2
  have h3 := hr.2.1.word_scratch 2 value (by have := h.high; omega)
  have hs := setWord_correct externalInput tape s3 h3 dst 2
  have hv : s3.val.words 2 = value := by simp [s3]
  rw [hv] at hs
  have hp := incrementPC_correct externalInput tape _ hs.2.1
  refine ⟨_, hl.1.seq (hr.1.seq (hc.seq (hs.1.seq hp.1))), hp.2.1, ?_⟩
  exact hl.2.2.2.trans (hr.2.2.2.trans
    ((callerFrame_word s2 origin 2 value (Or.inl (by decide))).trans (hs.2.2.trans hp.2.2)))

theorem indexLiteral_instruction (externalInput : RAMInput) (tape : ℕ → Bool)
    {L : Layout} {origin : ℕ} {source : RAMState} {written : List ℕ}
    (s : Store) (h : Represents origin source written s.val) (dst value : ℕ) :
    ∃ t, Executes externalInput tape (instruction L (.indexLiteral dst value)) 29 s t ∧
      Represents origin (source.setIndex dst value) (dst :: written) t.val ∧
      CallerFrame origin s.val t.val := by
  let s0 := s.put valueRegister value
  have h0 := h.put_scratch valueRegister value
    (by simp [ProtectedIndex, valueRegister, zeroRegister, oneRegister])
  have hs := setIndex_correct externalInput tape s0 h0 dst valueRegister (by decide)
  have hv : s0.val.indices valueRegister = value := by simp [s0]
  rw [hv] at hs
  have hp := incrementPC_correct externalInput tape _ hs.2.1
  refine ⟨_, (literal_executes externalInput tape s valueRegister value).seq (hs.1.seq hp.1), hp.2.1, ?_⟩
  exact (callerFrame_put s origin valueRegister value (Or.inl (by decide))).trans (hs.2.2.trans hp.2.2)

theorem indexCopy_instruction (externalInput : RAMInput) (tape : ℕ → Bool)
    {L : Layout} {origin : ℕ} {source : RAMState} {written : List ℕ}
    (s : Store) (h : Represents origin source written s.val) (dst src : ℕ) :
    ∃ t, Executes externalInput tape (instruction L (.indexCopy dst src)) 33 s t ∧
      Represents origin (source.setIndex dst (source.indices src)) (dst :: written) t.val ∧
      CallerFrame origin s.val t.val := by
  have hg := getIndex_correct externalInput tape s h src valueRegister (by decide)
  have hs := setIndex_correct externalInput tape _ hg.2.1 dst valueRegister (by decide)
  rw [hg.2.2.1] at hs
  have hp := incrementPC_correct externalInput tape _ hs.2.1
  exact ⟨_, hg.1.seq (hs.1.seq hp.1), hp.2.1, hg.2.2.2.trans (hs.2.2.trans hp.2.2)⟩

theorem binary_index_instruction (externalInput : RAMInput) (tape : ℕ → Bool)
    {origin : ℕ} {source : RAMState} {written : List ℕ}
    (s : Store) (h : Represents origin source written s.val)
    (dst left right : ℕ) (compute : Code) (f : ℕ → ℕ → ℕ)
    (execute : ∀ v : Store, Executes externalInput tape compute 2 v
      (v.put valueRegister (f (v.val.indices leftRegister) (v.val.indices rightRegister)))) :
    ∃ t, Executes externalInput tape
        (block [getIndex left leftRegister, getIndex right rightRegister, compute,
          setIndex dst valueRegister, incrementPC]) 41 s t ∧
      Represents origin (source.setIndex dst (f (source.indices left) (source.indices right)))
        (dst :: written) t.val ∧ CallerFrame origin s.val t.val := by
  have hl := getIndex_correct externalInput tape s h left leftRegister (by decide)
  have hr := getIndex_correct externalInput tape _ hl.2.1 right rightRegister (by decide)
  let s2 := indexed (indexed s left leftRegister) right rightRegister
  have hleft : s2.val.indices leftRegister = source.indices left := by
    simpa [s2, indexed, leftRegister, rightRegister, pointerRegister] using hl.2.2.1
  have hright : s2.val.indices rightRegister = source.indices right := hr.2.2.1
  let value := f (source.indices left) (source.indices right)
  let s3 := s2.put valueRegister value
  have hc : Executes externalInput tape compute 2 s2 s3 := by
    simpa only [hleft, hright] using execute s2
  have h3 := hr.2.1.put_scratch valueRegister value
    (by simp [ProtectedIndex, valueRegister, zeroRegister, oneRegister])
  have hs := setIndex_correct externalInput tape s3 h3 dst valueRegister (by decide)
  have hv : s3.val.indices valueRegister = value := by simp [s3]
  rw [hv] at hs
  have hp := incrementPC_correct externalInput tape _ hs.2.1
  refine ⟨_, hl.1.seq (hr.1.seq (hc.seq (hs.1.seq hp.1))), hp.2.1, ?_⟩
  exact hl.2.2.2.trans (hr.2.2.2.trans
    ((callerFrame_put s2 origin valueRegister value (Or.inl (by decide))).trans (hs.2.2.trans hp.2.2)))

end Maxwell.Cost.RealPrivate
