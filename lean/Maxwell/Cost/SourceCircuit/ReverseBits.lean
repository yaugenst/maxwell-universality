import Maxwell.Cost.SourceCircuit.ScanBits

/-! A fixed body processes every bit from right to left. Only the body
correctness theorem depends on its meaning; all loop tests and head moves
are instructions of one finite program. -/

namespace Maxwell.Cost.SourceCircuit.ReverseBits
open Structured

def boundary (remaining following : List Bool) (origin : ℤ) : BitTape :=
  Increment.cursor remaining following origin

def retreated (source : ℕ) (s : Store) : Store := Store.ofState
  (s.val.setTape source {s.val.tapes source with head := (s.val.tapes source).head - 1})

theorem retreated_passive (source : ℕ) (s : Store) :
    ScanBits.Passive source s (retreated source s) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, fun _ _ _ => rfl⟩
  intro j hj
  simp [retreated, Store.ofState, BitRAMState.setTape, hj]

def scanCode (source : ℕ) (body : Code) : Code :=
  .seq (.atom (.tapeLeft source))
    (.seq (ScanBits.readCode source)
      (.loop 31 (.seq body
        (.seq (.atom (.tapeLeft source)) (ScanBits.readCode source)))))

def code (source : ℕ) (body : Code) : Code :=
  .seq (scanCode source body) (.atom (.tapeRight source))

theorem retreat_last (source : ℕ) (word following : List Bool) (bit : Bool) (origin : ℤ)
    (s : Store) (hs : s.val.tapes source = boundary (word ++ [bit]) following origin) :
    (retreated source s).val.tapes source = boundary word (bit :: following) origin := by
  simp [retreated, Store.ofState, BitRAMState.setTape, hs, boundary, Increment.cursor,
    List.append_assoc, Nat.cast_add]
  omega

set_option maxRecDepth 8192 in
theorem scan_executes {α : Type*} (source : ℕ) (body : Code) (step : Bool → α → α)
    (input : List Bool) (tape : ℕ → Bool) (invariant : List Bool → α → Store → Prop)
    (bound : ℕ)
    (stable : ∀ bits data s t, ScanBits.Passive source s t →
      invariant bits data s → invariant bits data t)
    (bodyCorrect : ∀ bits bit data s,
      invariant (bits ++ [bit]) data s → s.val.registers 30 = bit → s.val.registers 31 = true →
      ∃ cost t, cost ≤ bound ∧ Executes input tape body cost s t ∧
        invariant bits (step bit data) t ∧ t.val.tapes source = s.val.tapes source)
    (word following : List Bool) (origin : ℤ) (data : α) (s : Store)
    (hs : s.val.tapes source = boundary word following origin)
    (hinv : invariant word data s) :
    ∃ cost, ∃ t : Store, cost ≤ word.length * (bound + 6) + 6 ∧
      Executes input tape (scanCode source body) cost s t ∧
      invariant [] (word.foldr step data) t ∧
      t.val.tapes source = {BitTape.shifted (word ++ following) origin with head := origin - 1} := by
  induction word using List.reverseRecOn generalizing following data s with
  | nil =>
    let a := retreated source s
    let c := ScanBits.checked source a
    have read : (a.val.tapes source).read = none := by
      simp [a, retreated, Store.ofState, BitRAMState.setTape, hs, boundary,
        Increment.cursor, BitTape.read, BitTape.shifted, show ¬origin ≤ origin - 1 by omega]
    have present : c.val.registers 31 = false := by
      simp [c, ScanBits.checked, Store.ofState, read]
    have ai := stable [] data s a (retreated_passive source s) hinv
    have ci := stable [] data a c (ScanBits.checked_passive source a) ai
    refine ⟨6, c, by simp,
      (Executes.tapeLeft input tape s source).seq
        ((ScanBits.read_executes source input tape a).seq (.done present)), ci, ?_⟩
    simp [c, a, ScanBits.checked, retreated, Store.ofState, BitRAMState.setTape,
      hs, boundary, Increment.cursor]
  | append_singleton word bit ih =>
    let a := retreated source s
    let c := ScanBits.checked source a
    have atape : a.val.tapes source = boundary word (bit :: following) origin :=
      retreat_last source word following bit origin s hs
    have read : (a.val.tapes source).read = some bit := by
      rw [atape]
      exact Increment.cursor_read word (bit :: following) origin
    have present : c.val.registers 31 = true := by
      simp [c, ScanBits.checked, Store.ofState, read]
    have symbol : c.val.registers 30 = bit := by
      simp [c, ScanBits.checked, Store.ofState, read]
    have ai := stable (word ++ [bit]) data s a (retreated_passive source s) hinv
    have ci := stable (word ++ [bit]) data a c (ScanBits.checked_passive source a) ai
    obtain ⟨bc, u, hbc, eb, ui, us⟩ := bodyCorrect word bit data c ci symbol present
    have utape : u.val.tapes source = boundary word (bit :: following) origin :=
      us.trans atape
    obtain ⟨rc, t, hrc, er, ti, ts⟩ := ih (bit :: following) (step bit data) u utape ui
    change Executes input tape (.seq (.atom (.tapeLeft source))
      (.seq (ScanBits.readCode source) _)) rc u t at er
    cases er with
    | seq move rest =>
      cases rest with
      | seq check loop =>
        refine ⟨_, t, ?_, (Executes.tapeLeft input tape s source).seq
          ((ScanBits.read_executes source input tape a).seq
            (.more present (eb.seq (move.seq check)) loop)), ?_, ?_⟩
        · simp only [List.length_append, List.length_singleton]
          nlinarith
        · simpa only [List.foldr_append, List.foldr_cons, List.foldr_nil] using ti
        · simpa only [List.append_assoc, List.singleton_append] using ts

/-- The complete scanner restores the source head to its original start,
including for an empty word, and charges the final move off the sentinel. -/
theorem executes {α : Type*} (source : ℕ) (body : Code) (step : Bool → α → α)
    (input : List Bool) (tape : ℕ → Bool) (invariant : List Bool → α → Store → Prop)
    (bound : ℕ)
    (stable : ∀ bits data s t, ScanBits.Passive source s t →
      invariant bits data s → invariant bits data t)
    (bodyCorrect : ∀ bits bit data s,
      invariant (bits ++ [bit]) data s → s.val.registers 30 = bit → s.val.registers 31 = true →
      ∃ cost t, cost ≤ bound ∧ Executes input tape body cost s t ∧
        invariant bits (step bit data) t ∧ t.val.tapes source = s.val.tapes source)
    (word following : List Bool) (origin : ℤ) (data : α) (s : Store)
    (hs : s.val.tapes source = boundary word following origin)
    (hinv : invariant word data s) :
    ∃ cost, ∃ t : Store, cost ≤ word.length * (bound + 6) + 8 ∧
      Executes input tape (code source body) cost s t ∧
      invariant [] (word.foldr step data) t ∧
      t.val.tapes source = BitTape.shifted (word ++ following) origin := by
  obtain ⟨cost, a, hcost, ea, ai, atape⟩ := scan_executes source body step input tape
    invariant bound stable bodyCorrect word following origin data s hs hinv
  let t := ScanBits.advanced source a
  refine ⟨cost+2, t, by omega, ea.seq (Executes.tapeRight input tape a source),
    stable [] _ a t (ScanBits.advanced_passive source a) ai, ?_⟩
  simp [t, ScanBits.advanced, Store.ofState, BitRAMState.setTape, atape, BitTape.shifted]

theorem executes_word {α : Type*} (source : ℕ) (body : Code) (step : Bool → α → α)
    (input : List Bool) (tape : ℕ → Bool) (invariant : List Bool → α → Store → Prop)
    (bound : ℕ)
    (stable : ∀ bits data s t, ScanBits.Passive source s t →
      invariant bits data s → invariant bits data t)
    (bodyCorrect : ∀ bits bit data s,
      invariant (bits ++ [bit]) data s → s.val.registers 30 = bit → s.val.registers 31 = true →
      ∃ cost t, cost ≤ bound ∧ Executes input tape body cost s t ∧
        invariant bits (step bit data) t ∧ t.val.tapes source = s.val.tapes source)
    (word : List Bool) (origin : ℤ) (data : α) (s : Store)
    (hs : s.val.tapes source = BitTape.shiftedEnd word origin)
    (hinv : invariant word data s) :
    ∃ cost, ∃ t : Store, cost ≤ word.length * (bound + 6) + 8 ∧
      Executes input tape (code source body) cost s t ∧
      invariant [] (word.foldr step data) t ∧
      t.val.tapes source = BitTape.shifted word origin := by
  simpa using executes source body step input tape invariant bound stable bodyCorrect
    word [] origin data s (by simpa [boundary, Increment.cursor, BitTape.shiftedEnd] using hs) hinv

end Maxwell.Cost.SourceCircuit.ReverseBits
