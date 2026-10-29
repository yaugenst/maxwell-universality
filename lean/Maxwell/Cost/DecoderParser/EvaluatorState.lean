import Maxwell.Cost.DecoderParser.Accumulate
import Maxwell.Cost.DecoderParser.RowHeader
import Maxwell.Cost.DecoderParser.MessageMemory
import Maxwell.Cost.DecoderFetch

namespace Maxwell.Cost.DecoderParser
open Structured
open RationalAccumulator (Bank Scratch Word Blank)

/-- Memory, sequential output and all tapes outside the actual work set. -/
structure EvalFrame (work : Finset ℕ) (s t : BitRAMState) : Prop where
  memory : t.memory=s.memory
  randomCursor : t.randomCursor=s.randomCursor
  output : t.output=s.output
  tapes : ∀ i, i ∉ work → t.tapes i=s.tapes i

theorem EvalFrame.refl (work : Finset ℕ) (s : BitRAMState) : EvalFrame work s s :=
  ⟨rfl,rfl,rfl,fun _ _ => rfl⟩

theorem EvalFrame.trans {work : Finset ℕ} {s t u : BitRAMState}
    (h : EvalFrame work s t) (k : EvalFrame work t u) : EvalFrame work s u :=
  ⟨k.memory.trans h.memory,k.randomCursor.trans h.randomCursor,k.output.trans h.output,
    fun i hi => (k.tapes i hi).trans (h.tapes i hi)⟩

theorem EvalFrame.mono {work work' : Finset ℕ} {s t : BitRAMState}
    (h : EvalFrame work s t) (hw : work ⊆ work') : EvalFrame work' s t :=
  ⟨h.memory,h.randomCursor,h.output,fun i hi => h.tapes i (fun hm => hi (hw hm))⟩

theorem Frame.eval {work : Finset ℕ} {s t : BitRAMState} (h : Frame work s t) : EvalFrame work s t :=
  ⟨h.memory,h.randomCursor,h.output,h.tapes⟩

def termWork : Finset ℕ := {0,1,2,3,5,6,7,8,9,12,13,30,31,32,33,34,35,36,45,65}

theorem ArithmeticFrame.eval {s t : BitRAMState} (h : ArithmeticFrame s t) :
    EvalFrame termWork s t := by
  refine ⟨h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,?_⟩
  intro i hi
  simp only [termWork,Finset.mem_insert,Finset.mem_singleton,not_or] at hi
  exact h.2.2.2.2.2 i (by omega) (by tauto) (by tauto) (by tauto) (by omega) (by tauto)

theorem fetch_eval {s t : BitRAMState} (h : DecoderFetch.Frame s t) :
    EvalFrame termWork s t := by
  refine ⟨h.1.2.2.2.1,h.1.2.1,h.1.2.2.1,?_⟩
  intro i hi
  simp only [termWork,Finset.mem_insert,Finset.mem_singleton,not_or] at hi
  exact h.2 i (by omega) (by tauto)

/-- Stable work-tape invariant between every two weighted terms. Metadata
constants are constructed once; parser tapes are reset to their literal origin. -/
structure EvalReady (F : Target.FixedPointFormat) (s : BitRAMState) : Prop where
  arithmetic : Scratch s 0
  blank : ∀ i ∈ ({5,6,7,8,9,65} : Finset ℕ), Blank s i
  parser : ∀ i ∈ ({10,12,13,45} : Finset ℕ), s.tapes i=BitTape.blank
  width : Word s 64 F.width
  center : Word s 66 (2^(F.integerBits+F.fractionalBits))
  scale : Word s 67 (2^F.fractionalBits)

theorem EvalReady.counter {F : Target.FixedPointFormat} {s t : Store} (counter : ℕ)
    (hc : 70 ≤ counter) (hf : Counted.Frame counter s t) (h : EvalReady F s.val) : EvalReady F t.val := by
  have ht (i : ℕ) (hi : i < 70) := hf.2.2.2.2.2.1 i (by omega)
  refine ⟨?_,?_,?_,RationalAccumulator.word_of_eq (ht 64 (by decide)) h.width,
    RationalAccumulator.word_of_eq (ht 66 (by decide)) h.center,
    RationalAccumulator.word_of_eq (ht 67 (by decide)) h.scale⟩
  · exact ⟨RationalAccumulator.blank_of_eq (ht 0 (by decide)) h.arithmetic.1,
      RationalAccumulator.word_of_eq (ht 1 (by decide)) h.arithmetic.2.1,
      RationalAccumulator.blank_of_eq (ht 2 (by decide)) h.arithmetic.2.2.1,
      RationalAccumulator.blank_of_eq (ht 3 (by decide)) h.arithmetic.2.2.2⟩
  · intro i hi
    have hb : i < 70 := by simp only [Finset.mem_insert,Finset.mem_singleton] at hi;omega
    exact RationalAccumulator.blank_of_eq (ht i hb) (h.blank i hi)
  · intro i hi
    have hb : i < 70 := by simp only [Finset.mem_insert,Finset.mem_singleton] at hi;omega
    exact (ht i hb).trans (h.parser i hi)

end Maxwell.Cost.DecoderParser
