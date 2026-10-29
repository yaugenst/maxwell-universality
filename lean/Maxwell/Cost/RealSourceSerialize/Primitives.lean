import Maxwell.Cost.RealSparseCode.Correctness
import Maxwell.Cost.RealArrayCode.Correctness
import Maxwell.Cost.RealSimulation.ControlCorrectness

namespace Maxwell.Cost.RealSourceSerialize
open RealNatCode (Layout StoredWord)
open RealSimulation.Control
open RealSparse (execute execute_sound)
set_option maxRecDepth 20000

def copyProgram (dst src : ℕ) : Machine := ⟨[.indexCopy dst src, .halt]⟩

theorem copy_executes (input : RAMInput) (tape : ℕ → Bool) (dst src : ℕ) (s : Store) :
    Executes input tape (.call (copyProgram dst src)) 2 s
      (Store.ofState (s.val.setIndex dst (s.val.indices src))) := by
  apply Executes.call _ _ _ 1
  · apply execute_sound
    simp [execute, copyProgram, Machine.next, s.property]
  · simp [copyProgram, RAMState.setIndex, s.property]

def natCode (register : ℕ) : Code :=
  .seq (.call (copyProgram 2 register)) (.call RealNatAppend.program)

theorem nat_executes (input : RAMInput) (tape : ℕ → Bool) (L : Layout)
    (register n : ℕ) (s : Store) (hn : s.val.indices register = n)
    (hc : s.val.indices 20 = L.cache) (hb : s.val.indices 21 = L.buffer)
    (hs : s.val.indices 22 = L.stride) :
    ∃ t : Store, Executes input tape (natCode register) (23 * n.size + 20) s t ∧
      StoredWord t.val L (Codec.nat n) ∧ t.val.indices 21 = L.bufferAt (Codec.nat n).length ∧
      t.val.words = s.val.words ∧
      (∀ i, RealNatAppend.Outside L i → t.val.indices i = s.val.indices i) ∧
      t.val.output = s.val.output ∧ t.val.indexOutput = s.val.indexOutput ∧
      t.val.randomCursor = s.val.randomCursor := by
  let a := Store.ofState (s.val.setIndex 2 (s.val.indices register))
  obtain ⟨t, ht, hpc, hstored, hcursor, hw, hi, ho, hio, hr⟩ :=
    RealNatAppend.terminates input tape L n a.val a.property
      (by simp [a, Store.ofState, RAMState.setIndex, hn])
      (by simpa [a, Store.ofState, RAMState.setIndex] using hc)
      (by simpa [a, Store.ofState, RAMState.setIndex] using hb)
      (by simpa [a, Store.ofState, RAMState.setIndex] using hs)
  have he := Executes.call RealNatAppend.program a t (23 * n.size + 17) ht.toSteps
    (by simp [RealNatAppend.program, RealNatCode.program, hpc])
  refine ⟨Store.ofState t, ?_, hstored, hcursor, hw, ?_, ho, hio, hr⟩
  · convert (copy_executes input tape 2 register s).seq he using 1 <;> try rfl
    omega
  · intro i hout
    simpa [a, Store.ofState, RAMState.setIndex, show i ≠ 2 by have := hout.1; omega] using hi i hout

def recordSetup : Machine := ⟨[.indexCopy 26 53, .halt]⟩
def vectorSetup : Machine := ⟨[.indexCopy 26 52, .indexCopy 24 54, .halt]⟩

def recordState (s : Store) : Store := Store.ofState (s.val.setIndex 26 (s.val.indices 53))
def vectorState (s : Store) : Store :=
  Store.ofState ((s.val.setIndex 26 (s.val.indices 52)).setIndex 24 (s.val.indices 54))

theorem recordSetup_executes (input : RAMInput) (tape : ℕ → Bool) (s : Store) :
    Executes input tape (.call recordSetup) 2 s (recordState s) :=
  copy_executes input tape 26 53 s

theorem vectorSetup_executes (input : RAMInput) (tape : ℕ → Bool) (s : Store) :
    Executes input tape (.call vectorSetup) 3 s (vectorState s) := by
  apply Executes.call _ _ _ 2
  · apply execute_sound
    simp [execute, vectorSetup, Machine.next, s.property, RAMState.setIndex]
  · simp [vectorSetup, RAMState.setIndex, s.property]

end Maxwell.Cost.RealSourceSerialize
