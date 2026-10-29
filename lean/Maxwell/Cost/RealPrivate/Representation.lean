import Maxwell.Cost.RealPrivate.Layout

namespace Maxwell.Cost.RealPrivate
open RealSimulation.Control

/-- Already-produced finite typed input buffers. Their locations are
disjoint from the low scratch frame and below the allocated private origin. -/
structure InputBuffer where
  realBase : ℕ
  realLength : ℕ
  indexBase : ℕ
  indexLength : ℕ

structure Inputs (L : Layout) (origin : ℕ) (B : InputBuffer)
    (input : RAMInput) (target : RAMState) : Prop where
  real_base : target.indices realInputBase = B.realBase
  real_length : target.indices realInputLength = B.realLength
  index_base : target.indices indexInputBase = B.indexBase
  index_length : target.indices indexInputLength = B.indexLength
  real_low : 32 ≤ B.realBase
  index_low : 256 ≤ B.indexBase
  real_high : ∀ j < B.realLength, B.realBase + L.realInputStride * j < origin
  index_high : ∀ j < B.indexLength, B.indexBase + L.indexInputStride * j < origin
  real_cells : ∀ j < B.realLength,
    target.words (B.realBase + L.realInputStride * j) = input.words j
  index_cells : ∀ j < B.indexLength,
    target.indices (B.indexBase + L.indexInputStride * j) = input.indices j
  real_outside : ∀ j, B.realLength ≤ j → input.words j = 0
  index_outside : ∀ j, B.indexLength ≤ j → input.indices j = 0

/-- The source's entire typed memory is represented, including every
indirectly addressed cell. The finite write log covers every nonzero cell,
which permits an actual bounded cleanup before the next solver attempt. -/
structure Represents (origin : ℕ) (source : RAMState) (written : List ℕ)
    (target : RAMState) : Prop where
  high : 256 ≤ origin
  origin_word : target.indices originRegister = origin
  zero : target.indices zeroRegister = 0
  one : target.indices oneRegister = 1
  pc : target.indices sourcePC = source.pc
  words : ∀ a, target.words (slot origin 0 a) = source.words a
  indices : ∀ a, target.indices (slot origin 0 a) = source.indices a
  real_output_length : target.indices realOutputLength = source.output.length
  index_output_length : target.indices indexOutputLength = source.indexOutput.length
  real_output : ∀ j < source.output.length,
    target.words (slot origin 1 j) = source.output.reverse[j]?.getD 0
  index_output : ∀ j < source.indexOutput.length,
    target.indices (slot origin 1 j) = source.indexOutput.reverse[j]?.getD 0
  log_length : target.indices logLength = written.length
  log_cells : ∀ j < written.length,
    target.indices (slot origin 2 j) = written.reverse[j]?.getD 0
  random_cursor : target.randomCursor = source.randomCursor

def Covered (source : RAMState) (written : List ℕ) : Prop :=
  ∀ a, a ∉ written → source.words a = 0 ∧ source.indices a = 0

def ProtectedIndex (j : ℕ) : Prop := j = zeroRegister ∨ j = oneRegister ∨ 160 ≤ j

theorem Inputs.congr {L : Layout} {origin : ℕ} {B : InputBuffer} {input : RAMInput}
    {s t : RAMState} (h : Inputs L origin B input s)
    (hw : ∀ j, 32 ≤ j → j < origin → t.words j = s.words j)
    (hi : ∀ j, 160 ≤ j → j < origin → t.indices j = s.indices j)
    (high : 256 ≤ origin) : Inputs L origin B input t := by
  refine ⟨?_, ?_, ?_, ?_, h.real_low, h.index_low, h.real_high, h.index_high,
    ?_, ?_, h.real_outside, h.index_outside⟩
  · rw [hi realInputBase (by decide) (by unfold realInputBase; omega)]; exact h.real_base
  · rw [hi realInputLength (by decide) (by unfold realInputLength; omega)]; exact h.real_length
  · rw [hi indexInputBase (by decide) (by unfold indexInputBase; omega)]; exact h.index_base
  · rw [hi indexInputLength (by decide) (by unfold indexInputLength; omega)]; exact h.index_length
  · intro j hj
    rw [hw _ (by have := h.real_low; omega) (h.real_high j hj)]
    exact h.real_cells j hj
  · intro j hj
    rw [hi _ (by have := h.index_low; omega) (h.index_high j hj)]
    exact h.index_cells j hj

theorem Represents.congr {origin : ℕ} {source : RAMState} {written : List ℕ}
    {s t : RAMState} (h : Represents origin source written s)
    (hw : ∀ j, origin ≤ j → t.words j = s.words j)
    (hi : ∀ j, ProtectedIndex j → t.indices j = s.indices j)
    (hr : t.randomCursor = s.randomCursor) : Represents origin source written t := by
  have hp (bank a : ℕ) : ProtectedIndex (slot origin bank a) := by
    apply Or.inr; apply Or.inr
    have := h.high
    have := slot_ge_origin origin bank a
    omega
  refine ⟨h.high, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hr.trans h.random_cursor⟩
  · rw [hi originRegister (by right; right; decide)]; exact h.origin_word
  · rw [hi zeroRegister (Or.inl rfl)]; exact h.zero
  · rw [hi oneRegister (Or.inr (Or.inl rfl))]; exact h.one
  · rw [hi sourcePC (by right; right; decide)]; exact h.pc
  · intro a; rw [hw _ (slot_ge_origin origin 0 a)]; exact h.words a
  · intro a; rw [hi _ (hp 0 a)]; exact h.indices a
  · rw [hi realOutputLength (by right; right; decide)]; exact h.real_output_length
  · rw [hi indexOutputLength (by right; right; decide)]; exact h.index_output_length
  · intro j hj; rw [hw _ (slot_ge_origin origin 1 j)]; exact h.real_output j hj
  · intro j hj; rw [hi _ (hp 1 j)]; exact h.index_output j hj
  · rw [hi logLength (by right; right; decide)]; exact h.log_length
  · intro j hj; rw [hi _ (hp 2 j)]; exact h.log_cells j hj

theorem Represents.put_scratch {origin : ℕ} {source : RAMState} {written : List ℕ}
    {s : Store} (h : Represents origin source written s.val)
    (r v : ℕ) (hr : ¬ ProtectedIndex r) :
    Represents origin source written (s.put r v).val := by
  apply h.congr
  · intro j _; rfl
  · intro j hj
    have hn : j ≠ r := by rintro rfl; exact hr hj
    simp [hn]
  · rfl

theorem Represents.word_scratch {origin : ℕ} {source : RAMState} {written : List ℕ}
    {s : Store} (h : Represents origin source written s.val)
    (r : ℕ) (v : ℝ) (hr : r < origin) :
    Represents origin source written (putWord s r v).val := by
  apply h.congr
  · intro j hj; simp [show j ≠ r by omega]
  · intro j _; rfl
  · rfl

end Maxwell.Cost.RealPrivate
