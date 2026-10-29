import Maxwell.Cost.SourceCircuit.HornerStep

namespace Maxwell.Cost.SourceCircuit.HornerLoop
open Structured
open RationalAccumulator (Blank)

structure Data where
  next : List Bool
  accumulator : List Bool
  gates : List Bool
  leaves : List (List Bool)

def step (bit : Bool) (d : Data) : Data :=
  if bit then {
    next := Increment.bits (Increment.bits d.next)
    accumulator := Increment.bits d.next
    gates := d.gates ++ additionTag ++ d.leaves.getLastD [] ++ d.accumulator ++ halfTag ++ d.next
    leaves := d.leaves.dropLast }
  else {
    next := Increment.bits d.next
    accumulator := d.next
    gates := d.gates ++ halfTag ++ d.accumulator
    leaves := d.leaves }

structure Ready (clock : List Bool) (d : Data) (s : Store) : Prop where
  scratch : BankArray.Scratch s.val
  blank96 : Blank s.val 96
  blank99 : Blank s.val 99
  next : BankArray.Word s.val 95 d.next
  accumulator : BankArray.Word s.val 94 d.accumulator
  gates : s.val.tapes 97 = BitTape.atEnd d.gates
  leaves : s.val.tapes 103 = BitTape.atEnd (d.leaves.flatten)
  clock : BankArray.Word s.val 93 clock

structure Valid (width : ℕ) (remaining : List Bool) (d : Data) : Prop where
  nextLength : d.next.length = width
  accumulatorLength : d.accumulator.length = width
  leavesCount : d.leaves.length = remaining.count true
  leafLength : ∀ word ∈ d.leaves, word.length = width
  room : addressValue d.next + remaining.length + remaining.count true < 2^width

theorem last_word {d : Data} {width : ℕ} {remaining : List Bool}
    (h : Valid width (remaining ++ [true]) d) :
    d.leaves ≠ [] ∧ (d.leaves.getLastD []).length = width ∧
      d.leaves.dropLast ++ [d.leaves.getLastD []] = d.leaves := by
  have hne : d.leaves ≠ [] := by
    intro he
    have hc := h.leavesCount
    simp [he] at hc
  refine ⟨hne,?_,?_⟩
  · apply h.leafLength
    simpa only [List.getLastD_eq_getLast?, List.getLast?_eq_getLast_of_ne_nil hne,
      Option.getD_some] using List.getLast_mem hne
  · simpa only [List.getLastD_eq_getLast?, List.getLast?_eq_getLast_of_ne_nil hne,
      Option.getD_some] using List.dropLast_append_getLast hne

theorem valid_step (width : ℕ) (remaining : List Bool) (bit : Bool) (d : Data)
    (h : Valid width (remaining ++ [bit]) d) : Valid width remaining (step bit d) := by
  have hlen : (Increment.bits d.next).length = width := by
    rw [increment_length d.next (by rw [h.nextLength]; have := h.room; simp only [List.length_append,List.length_singleton] at this; omega),h.nextLength]
  cases bit with
  | false =>
    refine ⟨hlen,h.nextLength,?_,h.leafLength,?_⟩
    · simpa [step] using h.leavesCount
    · change addressValue (Increment.bits d.next) + _ + _ < _
      rw [Increment.bits_value]
      have hh := h.room
      simp at hh
      omega
  | true =>
    have hlen2 : (Increment.bits (Increment.bits d.next)).length = width := by
      rw [increment_length (Increment.bits d.next) (by
        rw [hlen,Increment.bits_value]
        have hh := h.room
        simp only [List.length_append,List.length_singleton,List.count_append,List.count_cons_self,List.count_nil] at hh
        omega),hlen]
    refine ⟨hlen2,hlen,?_,?_,?_⟩
    · change d.leaves.dropLast.length = remaining.count true
      rw [List.length_dropLast]
      have hh := h.leavesCount
      simp at hh
      omega
    · intro word hw
      exact h.leafLength word (List.mem_of_mem_dropLast hw)
    · change addressValue (Increment.bits (Increment.bits d.next)) + _ + _ < _
      rw [Increment.bits_value,Increment.bits_value]
      have hh := h.room
      simp at hh
      omega

end Maxwell.Cost.SourceCircuit.HornerLoop
