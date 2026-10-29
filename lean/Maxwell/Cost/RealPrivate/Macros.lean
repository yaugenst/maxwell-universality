import Maxwell.Cost.RealPrivate.Primitives

namespace Maxwell.Cost.RealPrivate
open RealSimulation.Control

def indexed (s : Store) (address dst : ℕ) : Store :=
  (s.put pointerRegister (slot (s.val.indices originRegister) 0 address)).put dst
    (s.val.indices (slot (s.val.indices originRegister) 0 address))

noncomputable def worded (s : Store) (address dst : ℕ) : Store :=
  putWord (s.put pointerRegister (slot (s.val.indices originRegister) 0 address)) dst
    (s.val.words (slot (s.val.indices originRegister) 0 address))

theorem getIndex_executes (input : RAMInput) (tape : ℕ → Bool) (s : Store)
    (address dst : ℕ) (high : 256 ≤ s.val.indices originRegister) :
    Executes input tape (getIndex address dst) 6 s (indexed s address dst) := by
  have hn : slot (s.val.indices originRegister) 0 address ≠ pointerRegister := by
    have := slot_ge_origin (s.val.indices originRegister) 0 address
    unfold pointerRegister
    omega
  have h := (staticPointer_executes input tape s 0 address).seq
    (load_executes input tape
      (s.put pointerRegister (slot (s.val.indices originRegister) 0 address)) dst pointerRegister)
  simpa [getIndex, indexed, hn] using h

theorem getWord_executes (input : RAMInput) (tape : ℕ → Bool) (s : Store)
    (address dst : ℕ) :
    Executes input tape (getWord address dst) 6 s (worded s address dst) := by
  have h := (staticPointer_executes input tape s 0 address).seq
    (realLoad_executes input tape
      (s.put pointerRegister (slot (s.val.indices originRegister) 0 address)) dst pointerRegister)
  simpa [getWord, worded, Store.put] using h

/-- The log update is an ordinary store at bank2, followed by the explicit
length increment. Its value is the logical source address in register2. -/
def logged (s : Store) : Store :=
  ((s.put pointerRegister (slot (s.val.indices originRegister) 2 (s.val.indices logLength))).put
    (slot (s.val.indices originRegister) 2 (s.val.indices logLength))
    (s.val.indices coordinateRegister)).put logLength (s.val.indices logLength + 1)

theorem appendLog_executes (input : RAMInput) (tape : ℕ → Bool) (s : Store)
    (high : 256 ≤ s.val.indices originRegister) (one : s.val.indices oneRegister = 1) :
    Executes input tape appendLog 17 s (logged s) := by
  let address := slot (s.val.indices originRegister) 2 (s.val.indices logLength)
  have hn (j : ℕ) (hj : j < 256) : j ≠ address := by
    have := slot_ge_origin (s.val.indices originRegister) 2 (s.val.indices logLength)
    dsimp [address]
    omega
  let s0 := s.put pointerRegister address
  let s1 := s0.put address (s.val.indices coordinateRegister)
  have h169 : 169 ≠ slot (s.val.indices originRegister) 2 (s.val.indices 169) := hn 169 (by decide)
  have h7 : 7 ≠ slot (s.val.indices originRegister) 2 (s.val.indices 169) := hn 7 (by decide)
  have h := (bankPointer_executes input tape s 2 logLength (by decide)).seq
    ((save_executes input tape s0 pointerRegister coordinateRegister).seq
      (add_executes input tape s1 logLength logLength oneRegister))
  simpa [appendLog, block, RealSimulation.sequence, logged, s0, s1, address,
    coordinateRegister, pointerRegister, oneRegister, logLength,
    h169, h7, show s.val.indices 7 = 1 from one] using h

def indexSet (s : Store) (address src : ℕ) : Store :=
  logged (((s.put pointerRegister (slot (s.val.indices originRegister) 0 address)).put
    (slot (s.val.indices originRegister) 0 address) (s.val.indices src)).put
    coordinateRegister address)

noncomputable def wordSet (s : Store) (address src : ℕ) : Store :=
  logged ((putWord (s.put pointerRegister (slot (s.val.indices originRegister) 0 address))
    (slot (s.val.indices originRegister) 0 address) (s.val.words src)).put
    coordinateRegister address)

theorem setIndex_executes (input : RAMInput) (tape : ℕ → Bool) (s : Store)
    (address src : ℕ) (hsrc : src ≠ pointerRegister)
    (high : 256 ≤ s.val.indices originRegister) (one : s.val.indices oneRegister = 1) :
    Executes input tape (setIndex address src) 25 s (indexSet s address src) := by
  let a := slot (s.val.indices originRegister) 0 address
  have hn (j : ℕ) (hj : j < 256) : j ≠ a := by
    have := slot_ge_origin (s.val.indices originRegister) 0 address
    dsimp [a]
    omega
  let s0 := s.put pointerRegister a
  let s1 := s0.put a (s.val.indices src)
  let s2 := s1.put coordinateRegister address
  have hs : (s0.val.indices src) = s.val.indices src := by simp [s0, hsrc]
  have hh : 256 ≤ s2.val.indices originRegister := by
    simpa [s2, s1, s0, originRegister, coordinateRegister, pointerRegister, hn 160 (by decide)] using high
  have ho : s2.val.indices oneRegister = 1 := by
    simpa [s2, s1, s0, oneRegister, coordinateRegister, pointerRegister, hn 7 (by decide)] using one
  have hsave : Executes input tape (save pointerRegister src) 2 s0 s1 := by
    simpa [s1, s0, hsrc] using save_executes input tape s0 pointerRegister src
  have h := (staticPointer_executes input tape s 0 address).seq
    (hsave.seq ((literal_executes input tape s1 coordinateRegister address).seq
      (appendLog_executes input tape s2 hh ho)))
  simpa [setIndex, block, RealSimulation.sequence, indexSet, s0, s1, s2, a] using h

theorem setWord_executes (input : RAMInput) (tape : ℕ → Bool) (s : Store)
    (address src : ℕ) (high : 256 ≤ s.val.indices originRegister)
    (one : s.val.indices oneRegister = 1) :
    Executes input tape (setWord address src) 25 s (wordSet s address src) := by
  let a := slot (s.val.indices originRegister) 0 address
  let s0 := s.put pointerRegister a
  let s1 := putWord s0 a (s.val.words src)
  let s2 := s1.put coordinateRegister address
  have hh : 256 ≤ s2.val.indices originRegister := by
    simpa [s2, s1, s0, putWord, originRegister, coordinateRegister, pointerRegister] using high
  have ho : s2.val.indices oneRegister = 1 := by
    simpa [s2, s1, s0, putWord, oneRegister, coordinateRegister, pointerRegister] using one
  have hstore : Executes input tape (realStore pointerRegister src) 2 s0 s1 := by
    simpa [s1, s0, Store.put] using realStore_executes input tape s0 pointerRegister src
  have h := (staticPointer_executes input tape s 0 address).seq
    (hstore.seq ((literal_executes input tape s1 coordinateRegister address).seq
      (appendLog_executes input tape s2 hh ho)))
  simpa [setWord, block, RealSimulation.sequence, wordSet, s0, s1, s2, a] using h

end Maxwell.Cost.RealPrivate
