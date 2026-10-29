import Maxwell.Cost.RealPrivate.AccessSemantics
import Maxwell.Cost.RealPrivate.LogFrame

namespace Maxwell.Cost.RealPrivate
open RealSimulation.Control

theorem setWord_correct (externalInput : RAMInput) (tape : ℕ → Bool)
    {origin : ℕ} {source : RAMState} {written : List ℕ} (s : Store)
    (h : Represents origin source written s.val) (address src : ℕ) :
    Executes externalInput tape (setWord address src) 25 s (wordSet s address src) ∧
    Represents origin {source with words := Function.update source.words address (s.val.words src)}
      (address :: written) (wordSet s address src).val ∧
    CallerFrame origin s.val (wordSet s address src).val := by
  let s0 := s.put pointerRegister (slot (s.val.indices originRegister) 0 address)
  let s1 := putWord s0 (slot (s.val.indices originRegister) 0 address) (s.val.words src)
  let s2 := s1.put coordinateRegister address
  have h0 : Represents origin source written s0.val :=
    h.put_scratch pointerRegister _ (by simp [ProtectedIndex, pointerRegister, zeroRegister, oneRegister])
  have h1 : Represents origin
      {source with words := Function.update source.words address (s.val.words src)} written s1.val := by
    simpa only [s1, h.origin_word] using h0.private_word address (s.val.words src)
  have h2 := h1.put_scratch coordinateRegister address
    (by simp [ProtectedIndex, coordinateRegister, zeroRegister, oneRegister])
  refine ⟨setWord_executes externalInput tape s address src
      (by rw [h.origin_word]; exact h.high) h.one, ?_,
    callerFrame_wordSet s origin address src h.origin_word⟩
  simpa [wordSet, s1, s0] using h2.logged

theorem setIndex_correct (externalInput : RAMInput) (tape : ℕ → Bool)
    {origin : ℕ} {source : RAMState} {written : List ℕ} (s : Store)
    (h : Represents origin source written s.val) (address src : ℕ) (hs : src ≠ pointerRegister) :
    Executes externalInput tape (setIndex address src) 25 s (indexSet s address src) ∧
    Represents origin {source with indices := Function.update source.indices address (s.val.indices src)}
      (address :: written) (indexSet s address src).val ∧
    CallerFrame origin s.val (indexSet s address src).val := by
  let s0 := s.put pointerRegister (slot (s.val.indices originRegister) 0 address)
  let s1 := s0.put (slot (s.val.indices originRegister) 0 address) (s.val.indices src)
  have h0 : Represents origin source written s0.val :=
    h.put_scratch pointerRegister _ (by simp [ProtectedIndex, pointerRegister, zeroRegister, oneRegister])
  have h1 : Represents origin
      {source with indices := Function.update source.indices address (s.val.indices src)} written s1.val := by
    simpa only [s1, h.origin_word] using h0.private_index address (s.val.indices src)
  have h2 := h1.put_scratch coordinateRegister address
    (by simp [ProtectedIndex, coordinateRegister, zeroRegister, oneRegister])
  refine ⟨setIndex_executes externalInput tape s address src hs
      (by rw [h.origin_word]; exact h.high) h.one, ?_,
    callerFrame_indexSet s origin address src h.origin_word h.high⟩
  simpa [indexSet, s1, s0] using h2.logged

end Maxwell.Cost.RealPrivate
