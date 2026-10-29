import Maxwell.Cost.MemoryWord.Write
import Mathlib.Data.Vector.Basic

namespace Maxwell.Cost.BitArray

private theorem get_set {α : Type*} {n : ℕ} (saved : Vector α n) (i j : Fin n) (value : α) :
    (saved.set i.val value i.isLt).get j = if i = j then value else saved.get j := by
  simp [Vector.get, Fin.cast, Array.getElem_set, Fin.ext_iff]

/-- A flat, fixed-width array in actual bit memory. The width is part of
its layout; indices are represented by binary words at the machine boundary. -/
structure Represents {n : ℕ} (memory : ℕ → Bool) (base width : ℕ)
    (words : Vector (List Bool) n) : Prop where
  length : ∀ i, (words.get i).length = width
  bits : ∀ (i : Fin n) (j : ℕ) (hj : j < width),
    memory (base + i.val * width + j) = (words.get i)[j]'(by rw [length]; exact hj)

theorem Represents.read {n : ℕ} {memory : ℕ → Bool} {base width : ℕ}
    {words : Vector (List Bool) n} (h : Represents memory base width words) (i : Fin n) :
    MemoryWord.readBits memory (base + i.val * width) width = words.get i := by
  apply List.ext_getElem
  · simpa using (h.length i).symm
  · intro j hj hk
    rw [MemoryWord.readBits_getElem memory _ width j (by simpa using hj)]
    exact h.bits i j (by simpa using hj)

/-- Writing one word preserves every other array word, including adjacent
ones. The proof uses the executed bit writer's exact interval semantics. -/
theorem Represents.write {n : ℕ} {memory : ℕ → Bool} {base width : ℕ}
    {words : Vector (List Bool) n} (h : Represents memory base width words)
    (i : Fin n) (word : List Bool) (hlen : word.length = width) :
    Represents (MemoryWord.writeBits memory (base + i.val * width) word)
      base width (words.set i word) := by
  have hlength : ∀ k, ((words.set i word).get k).length = width := by
    intro k
    rw [get_set]
    split_ifs with hk
    · exact hlen
    · exact h.length k
  refine ⟨hlength, ?_⟩
  intro k j hj
  by_cases hk : k = i
  · subst k
    simpa [get_set] using MemoryWord.writeBits_inside memory (base + i.val * width) word j (by omega)
  · have hindex : k.val ≠ i.val := fun he => hk (Fin.ext he)
    have hout : base + k.val * width + j < base + i.val * width ∨
        base + i.val * width + word.length ≤ base + k.val * width + j := by
      rcases Nat.lt_or_gt_of_ne hindex with hki | hik
      · left
        have hm := Nat.mul_le_mul_right width (show k.val + 1 ≤ i.val by omega)
        nlinarith
      · right
        have hm := Nat.mul_le_mul_right width (show i.val + 1 ≤ k.val by omega)
        nlinarith
    rw [MemoryWord.writeBits_outside memory _ word _ hout]
    simpa [get_set, hk, Ne.symm hk] using h.bits k j hj
/-- Existing random-memory reader, specialized to a proved array entry.
The address equality is supplied by an actual indexed-address routine. -/
theorem read_steps {n : ℕ} (input : List Bool) (randomTape : ℕ → Bool)
    (base width : ℕ) (words : Vector (List Bool) n) (i : Fin n)
    (address clock : List Bool) (ao co oo : ℤ) (s : BitRAMState)
    (hpc : s.pc = 0) (harray : Represents s.memory base width words)
    (hvalue : addressValue address = base + i.val * width) (hclockLength : clock.length = width)
    (haddress : s.tapes 5 = BitTape.shiftedEnd address ao)
    (hclock : s.tapes 6 = BitTape.shifted clock co)
    (houtput : s.tapes 7 = {BitTape.blank with head := oo}) :
    ∃ cost t finalAddress,
      cost ≤ width * (15 * (address.length + width) + 24) + 3 ∧
      PricedSteps (MemoryWord.readProgram.next input randomTape) cost s t ∧ t.pc = 28 ∧
      t.tapes 5 = BitTape.shiftedEnd finalAddress ao ∧
      addressValue finalAddress = base + (i.val + 1) * width ∧
      finalAddress.length ≤ address.length + width ∧
      t.tapes 6 = BitTape.shiftedEnd clock co ∧
      t.tapes 7 = BitTape.shiftedEnd (words.get i) oo ∧
      Represents t.memory base width words ∧ MemoryWord.Frame s t := by
  obtain ⟨cost, t, finalAddress, hc, hs, hp, ha, hv, hl, ht6, ht7, hf⟩ :=
    MemoryWord.simulation input randomTape address clock ao co oo s hpc haddress hclock houtput
  refine ⟨cost, t, finalAddress, ?_, hs, hp, ha, ?_, ?_, ht6, ?_, ?_, hf⟩
  · simpa [hclockLength] using hc
  · simpa [hvalue, hclockLength, Nat.add_mul, Nat.add_assoc] using hv
  · simpa [hclockLength] using hl
  · simpa [hvalue, hclockLength, harray.read i] using ht7
  · simpa [hf.2.1] using harray

/-- The finite writer realizes a vector update, with the complete resulting
memory function and its actual charged execution both in the conclusion. -/
theorem write_steps {n : ℕ} (input : List Bool) (randomTape : ℕ → Bool)
    (base width : ℕ) (words : Vector (List Bool) n) (i : Fin n)
    (address word : List Bool) (ao wo : ℤ) (s : BitRAMState)
    (hpc : s.pc = 0) (harray : Represents s.memory base width words)
    (hvalue : addressValue address = base + i.val * width) (hlen : word.length = width)
    (haddress : s.tapes 5 = BitTape.shiftedEnd address ao)
    (hword : s.tapes 6 = BitTape.shifted word wo) :
    ∃ cost t finalAddress,
      cost ≤ width * (15 * (address.length + width) + 22) + 3 ∧
      PricedSteps (MemoryWord.writeProgram.next input randomTape) cost s t ∧ t.pc = 26 ∧
      t.tapes 5 = BitTape.shiftedEnd finalAddress ao ∧
      addressValue finalAddress = base + (i.val + 1) * width ∧
      finalAddress.length ≤ address.length + width ∧
      t.tapes 6 = BitTape.shiftedEnd word wo ∧
      t.memory = MemoryWord.writeBits s.memory (base + i.val * width) word ∧
      Represents t.memory base width (words.set i word) ∧ MemoryWord.WriteFrame s t := by
  obtain ⟨cost, t, finalAddress, hc, hs, hp, ha, hv, hl, ht6, hm, hf⟩ :=
    MemoryWord.write_simulation input randomTape address word ao wo s hpc haddress hword
  refine ⟨cost, t, finalAddress, ?_, hs, hp, ha, ?_, ?_, ht6, ?_, ?_, hf⟩
  · simpa [hlen] using hc
  · simpa [hvalue, hlen, Nat.add_mul, Nat.add_assoc] using hv
  · simpa [hlen] using hl
  · simpa [hvalue] using hm
  · simpa [hm, hvalue] using harray.write i word hlen

end Maxwell.Cost.BitArray
