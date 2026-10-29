import Maxwell.Cost.SourceCircuit.HornerStep
import Maxwell.Cost.Structured.CountedShifted

namespace Maxwell.Cost.SourceCircuit.RowSum
open Structured
open RationalAccumulator (Blank)

structure Data where
  next : List Bool
  accumulator : List Bool
  gates : List Bool
  terms : List (List Bool)

def step (d : Data) : Data where
  next := Increment.bits d.next
  accumulator := d.next
  gates := d.gates ++ additionTag ++ d.terms.getLastD [] ++ d.accumulator
  terms := d.terms.dropLast

def complete (d : Data) : Data := (step^[d.terms.length]) d

theorem complete_step (d : Data) (hne : d.terms ≠ []) : complete (step d) = complete d := by
  have hn : 0 < d.terms.length := List.length_pos_iff.mpr hne
  unfold complete
  have hl : (step d).terms.length + 1 = d.terms.length := by
    simp only [step, List.length_dropLast]
    omega
  rw [← hl, Function.iterate_succ_apply]

theorem complete_empty {d : Data} (h : d.terms = []) : complete d = d := by
  simp [complete, h]

structure Ready (clock : List Bool) (d : Data) (s : Store) : Prop where
  scratch : BankArray.Scratch s.val
  blank96 : Blank s.val 96
  blank99 : Blank s.val 99
  next : BankArray.Word s.val 95 d.next
  accumulator : BankArray.Word s.val 94 d.accumulator
  gates : s.val.tapes 97 = BitTape.atEnd d.gates
  terms : s.val.tapes 104 = BitTape.atEnd d.terms.flatten
  clock : BankArray.Word s.val 93 clock

structure Valid (width count : ℕ) (d : Data) : Prop where
  nextLength : d.next.length = width
  accumulatorLength : d.accumulator.length = width
  termsCount : d.terms.length = count
  termLength : ∀ word ∈ d.terms, word.length = width
  room : addressValue d.next + count < 2 ^ width

theorem last_word {d : Data} {width count : ℕ} (h : Valid width (count+1) d) :
    d.terms ≠ [] ∧ (d.terms.getLastD []).length = width ∧
      d.terms.dropLast ++ [d.terms.getLastD []] = d.terms := by
  have hne : d.terms ≠ [] := by intro he; have := h.termsCount; simp [he] at this
  have hd : d.terms.getLastD [] = d.terms.getLast hne := by
    rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hne]
    rfl
  exact ⟨hne, h.termLength _ (hd ▸ List.getLast_mem hne),
    hd ▸ List.dropLast_append_getLast hne⟩

theorem valid_step {d : Data} {width count : ℕ} (h : Valid width (count+1) d) :
    Valid width count (step d) := by
  refine ⟨?_, h.nextLength, ?_, ?_, ?_⟩
  · change (Increment.bits d.next).length = width
    rw [increment_length d.next (by rw [h.nextLength]; have := h.room; omega), h.nextLength]
  · simp [step, List.length_dropLast, h.termsCount]
  · intro word hw
    exact h.termLength word (List.mem_of_mem_dropLast hw)
  · change addressValue (Increment.bits d.next) + count < _
    rw [Increment.bits_value]
    have := h.room
    omega

def bodyWork : Finset ℕ := {94,95,96,97,99,104}
def work : Finset ℕ := {94,95,96,97,99,104,106}

theorem count_frame {s t : Store} (h : Counted.Frame 106 s t) :
    Frame work s.val t.val := by
  refine ⟨h.2.1, h.2.2.2.1, h.2.2.2.2.1, ?_, ?_, ?_⟩
  · intro j _ hj
    exact h.2.2.2.2.2.1 j (by intro he; exact hj (by simp [work, he]))
  · exact h.2.2.2.2.2.2 23 (by omega) (by omega) (by omega) (by omega)
  · intro j hj
    exact h.2.2.2.2.2.2 j (by omega) (by omega) (by omega) (by omega)

theorem Ready.count {clock : List Bool} {d : Data} {s t : Store}
    (h : Ready clock d s) (f : Counted.Frame 106 s t) : Ready clock d t := by
  refine ⟨scratch_of_tapes h.scratch (fun j hj => f.2.2.2.2.2.1 j (by omega)),
    RationalAccumulator.blank_of_eq (f.2.2.2.2.2.1 96 (by omega)) h.blank96,
    RationalAccumulator.blank_of_eq (f.2.2.2.2.2.1 99 (by omega)) h.blank99,
    BankArray.word_of_eq (f.2.2.2.2.2.1 95 (by omega)) h.next,
    BankArray.word_of_eq (f.2.2.2.2.2.1 94 (by omega)) h.accumulator,
    (f.2.2.2.2.2.1 97 (by omega)).trans h.gates,
    (f.2.2.2.2.2.1 104 (by omega)).trans h.terms,
    BankArray.word_of_eq (f.2.2.2.2.2.1 93 (by omega)) h.clock⟩

end Maxwell.Cost.SourceCircuit.RowSum
