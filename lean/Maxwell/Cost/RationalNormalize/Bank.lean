import Maxwell.Cost.DyadicSqrt

namespace Maxwell.Cost.RationalNormalize

open Structured RationalAccumulator

def Frame (s t : BitRAMState) : Prop :=
  t.address = s.address ∧ t.inputHead = s.inputHead ∧ t.memory = s.memory ∧
  t.randomCursor = s.randomCursor ∧ t.output = s.output ∧
  (∀ i, (4 ≤ i ∧ i < 30 ∨ 37 ≤ i) → t.tapes i = s.tapes i) ∧
  (∀ i, 36 ≤ i → t.registers i = s.registers i)

theorem Frame.refl (s : BitRAMState) : Frame s s := by simp [Frame]

theorem Frame.trans {s t u : BitRAMState} (h : Frame s t) (k : Frame t u) :
    Frame s u := by
  rcases h with ⟨ha, hi, hm, hr, ho, ht, hg⟩
  rcases k with ⟨ka, ki, km, kr, ko, kt, kg⟩
  exact ⟨ka.trans ha, ki.trans hi, km.trans hm, kr.trans hr, ko.trans ho,
    fun i hi => (kt i hi).trans (ht i hi), fun i hi => (kg i hi).trans (hg i hi)⟩

theorem Frame.toLoop {s t : BitRAMState} (h : Frame s t) : DyadicSqrt.LoopFrame s t :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
    fun i hi => h.2.2.2.2.2.1 i (by omega), h.2.2.2.2.2.2⟩

theorem frame_of_bank {s t : BitRAMState} (h : RationalAccumulator.Frame s t) : Frame s t :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
    fun i hi => h.2.2.2.2.2.1 i (by omega) (by omega),
    fun i hi => h.2.2.2.2.2.2 i (by omega) (by omega) (by omega) (by omega) (by omega)⟩

def loadCode (source target : ℕ) : Code :=
  .seq (.call (TapeOps.clear target)) (.call (WordTransfer.clone source target))

/-- Copy a persistent input integer into the arithmetic bank. The input
word is preserved and every clearing/copying operation is charged. -/
theorem load (source target : ℕ) (hs : 41 ≤ source) (ht : 30 ≤ target) (ht' : target ≤ 36)
    (input : List Bool) (tape : ℕ → Bool) (v : ℕ → ℕ) (value : ℕ) (s : Store)
    (hbank : Bank s.val v) (hready : Scratch s.val 0) (hword : Word s.val source value) :
    ∃ t : Store, Executes input tape (loadCode source target)
      (6 * (v target).bits.length + 15 * value.bits.length + 21) s t ∧
      Bank t.val (Function.update v target value) ∧ Scratch t.val 0 ∧ Frame s.val t.val := by
  obtain ⟨origin, hw⟩ := hbank target ht ht'
  obtain ⟨a, ea, ha, fa⟩ := WordCall.clear target input tape (v target).bits origin s hw
  obtain ⟨sourceOrigin, hsource⟩ := hword
  have has : a.val.tapes source = BitTape.shifted value.bits sourceOrigin := by
    simpa [ha, show source ≠ target by omega] using hsource
  obtain ⟨t, et, htapes, ft⟩ := WordCall.clone source target (by omega) input tape value.bits
    sourceOrigin (origin + (v target).bits.length) a has (by simp [ha])
  have keep (i : ℕ) (hi : i ≠ target) : t.val.tapes i = s.val.tapes i := by
    simp [htapes, ha, hi]
  refine ⟨t, ?_, ?_, ?_, ?_⟩
  · convert ea.seq et using 1 <;> first | rfl | omega
  · intro i hi hi'
    by_cases hit : i = target
    · subst i
      exact ⟨origin + (v target).bits.length, by simp [htapes]⟩
    · simp only [Function.update_of_ne hit]
      exact word_of_eq (keep i hit) (hbank i hi hi')
  · exact ⟨blank_of_eq (keep 0 (by omega)) hready.1,
      word_of_eq (keep 1 (by omega)) hready.2.1,
      blank_of_eq (keep 2 (by omega)) hready.2.2.1,
      blank_of_eq (keep 3 (by omega)) hready.2.2.2⟩
  · exact ⟨ft.1.trans fa.1, ft.2.1.trans fa.2.1, ft.2.2.1.trans fa.2.2.1,
      ft.2.2.2.1.trans fa.2.2.2.1, ft.2.2.2.2.1.trans fa.2.2.2.2.1,
      fun i hi => keep i (by omega), fun i hi =>
        (ft.2.2.2.2.2.2 i (by omega) (by omega) (by omega) (by omega)).trans
          (fa.2.2.2.2.2.2 i (by omega) (by omega))⟩

def oneCode (target : ℕ) : Code := .seq (.call (TapeOps.clear target))
  (.seq (Code.atom (.literal 28 true)) (Code.atom (.writeTape target 28)))

theorem write_one (origin : ℤ) :
    ({BitTape.blank with head := origin} : BitTape).write (some true) =
      BitTape.shifted (1 : ℕ).bits origin := by
  apply BitTape.ext
  · rfl
  · have h := congrArg BitTape.cells (BitTape.shiftedEnd_append_write [] origin true)
    simpa [BitTape.shiftedEnd, BitTape.shifted, BitTape.blank] using h

/-- Write the fixed integer one using a literal Boolean and one tape write. -/
theorem one (target : ℕ) (ht : 30 ≤ target) (ht' : target ≤ 36)
    (input : List Bool) (tape : ℕ → Bool) (v : ℕ → ℕ) (s : Store)
    (hbank : Bank s.val v) (hready : Scratch s.val 0) :
    ∃ t : Store, Executes input tape (oneCode target) (6 * (v target).bits.length + 8) s t ∧
      Bank t.val (Function.update v target 1) ∧ Scratch t.val 0 ∧ Frame s.val t.val := by
  obtain ⟨origin, hw⟩ := hbank target ht ht'
  obtain ⟨a, ea, ha, fa⟩ := WordCall.clear target input tape (v target).bits origin s hw
  let b : Store := Store.ofState (a.val.setRegister 28 true)
  let t : Store := Store.ofState (b.val.setTape target ((b.val.tapes target).write (some true)))
  have eb : Executes input tape (Code.atom (.literal 28 true)) 2 a b :=
    Executes.literal input tape a 28 true
  have et : Executes input tape (Code.atom (.writeTape target 28)) 2 b t := by
    simpa [t, b, BitRAMState.setRegister, Store.ofState] using Executes.writeTape input tape b target 28
  have htapes : t.val.tapes = Function.update s.val.tapes target
      (BitTape.shifted (1 : ℕ).bits (origin + (v target).bits.length)) := by
    simp [t, b, Store.ofState, ha, BitRAMState.setTape, BitRAMState.setRegister, write_one]
  have keep (i : ℕ) (hi : i ≠ target) : t.val.tapes i = s.val.tapes i := by simp [htapes, hi]
  refine ⟨t, ?_, ?_, ?_, ?_⟩
  · simpa only [oneCode] using ea.seq (eb.seq et)
  · intro i hi hi'
    by_cases hit : i = target
    · subst i
      exact ⟨origin + (v target).bits.length, by simp [htapes]⟩
    · simp only [Function.update_of_ne hit]
      exact word_of_eq (keep i hit) (hbank i hi hi')
  · exact ⟨blank_of_eq (keep 0 (by omega)) hready.1,
      word_of_eq (keep 1 (by omega)) hready.2.1,
      blank_of_eq (keep 2 (by omega)) hready.2.2.1,
      blank_of_eq (keep 3 (by omega)) hready.2.2.2⟩
  · refine ⟨fa.1, fa.2.1, fa.2.2.1, fa.2.2.2.1, fa.2.2.2.2.1,
      fun i hi => keep i (by omega), ?_⟩
    intro i hi
    have hg := fa.2.2.2.2.2.2 i (by omega) (by omega)
    simpa [t, b, Store.ofState, BitRAMState.setTape, BitRAMState.setRegister,
      show i ≠ 28 by omega] using hg

end Maxwell.Cost.RationalNormalize
