import Maxwell.Cost.RealSimulation.WriteFrame
import Maxwell.Cost.RealSimulation.IndexWidth
import Maxwell.Cost.RealSimulation.SourceBounds

namespace Maxwell.Cost.RealSimulation
open Control

def scratchCells : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 12, 13, 14, 15]

def clearCells : List ℕ → Code
  | [] => .skip
  | j :: js => .seq (literal j 0) (clearCells js)

def clearedCells (s : Store) : List ℕ → Store
  | [] => s
  | j :: js => clearedCells (s.put j 0) js

def clearScratch : Code := clearCells scratchCells
def clearedScratch (s : Store) : Store := clearedCells s scratchCells

theorem clearedCells_indices (s : Store) (js : List ℕ) (j : ℕ) :
    (clearedCells s js).val.indices j = if j ∈ js then 0 else s.val.indices j := by
  induction js generalizing s with
  | nil => rfl
  | cons a js ih =>
    simp only [clearedCells, ih, List.mem_cons, Store.put_indices]
    split_ifs <;> simp_all

theorem clearCells_executes (input : RAMInput) (tape : ℕ → Bool) (s : Store) (js : List ℕ) :
    Executes input tape (clearCells js) (2 * js.length + 1) s (clearedCells s js) := by
  induction js generalizing s with
  | nil => exact Executes.skip s
  | cons j js ih =>
    have he := (literal_executes input tape s j 0).seq (ih (s.put j 0))
    convert he using 1
    · rfl
    · simp [List.length_cons]; omega
    · rfl

theorem clearScratch_executes (input : RAMInput) (tape : ℕ → Bool) (s : Store) :
    Executes input tape clearScratch 27 s (clearedScratch s) :=
  clearCells_executes input tape s scratchCells

theorem clearCells_ready {L : Layout} {origin center : ℕ} {bits : List Bool}
    {source : BitRAMState} (s : Store) (h : Ready L origin center bits source s)
    (js : List ℕ) (hs : ∀ j ∈ js, j < 20 ∧ zeroRegister ≠ j ∧
      oneRegister ≠ j ∧ activeRegister ≠ j) :
    Ready L origin center bits source (clearedCells s js) := by
  induction js generalizing s with
  | nil => exact h
  | cons j js ih =>
    have hj := hs j (by simp)
    exact ih (s.put j 0) (h.put_scratch j 0 hj.1 hj.2.1 hj.2.2.1 hj.2.2.2)
      (fun k hk => hs k (by simp [hk]))

theorem clearScratch_ready {L : Layout} {origin center : ℕ} {bits : List Bool}
    {source : BitRAMState} (s : Store) (h : Ready L origin center bits source s) :
    Ready L origin center bits source (clearedScratch s) := by
  apply clearCells_ready s h scratchCells
  decide

theorem clearScratch_small {L : Layout} {origin center : ℕ} {bits : List Bool}
    {source : BitRAMState} (s : Store) (h : Ready L origin center bits source s)
    (j : ℕ) (hj : j < 16) : (clearedScratch s).val.indices j ≤ 1 := by
  rw [clearedScratch, clearedCells_indices]
  by_cases hm : j ∈ scratchCells
  · simp [hm]
  · have hn : j = zeroRegister ∨ j = oneRegister ∨ j = activeRegister := by
      simp only [scratchCells, List.mem_cons, List.not_mem_nil, or_false] at hm
      unfold zeroRegister oneRegister activeRegister
      omega
    rcases hn with rfl | rfl | rfl <;> simp [hm, h.zero, h.one, h.active]

theorem clearScratch_frame (L : Layout) (s : Store) : WriteFrame L s.val (clearedScratch s).val := by
  intro j hj
  left
  rw [clearedScratch, clearedCells_indices, ite_eq_right]
  intro hm
  have hs : j < 16 := by
    simp only [scratchCells, List.mem_cons, List.not_mem_nil, or_false] at hm
    omega
  exact hj (scalar_small L j hs)

theorem represented_scalar_bound {L : Layout} {origin center : ℕ} {bits : List Bool}
    {source : BitRAMState} {s : Store} {bound used : ℕ}
    (h : Ready L origin center bits source s) (hb : SourceBounds source used)
    (hu : used ≤ center) (hc : 2 * center ≤ bound) (hp : source.pc ≤ bound)
    (h2 : 2 ≤ bound) (small : ∀ j < 16, s.val.indices j ≤ 1)
    (j : ℕ) (hj : ScalarCell L j) : s.val.indices j ≤ bound := by
  rcases hj with hj | rfl | rfl | rfl | rfl | ⟨hl, hr⟩
  · exact (small j hj).trans (by omega)
  · simpa only [h.pc] using hp
  · rw [h.address_length]; have := hb.address; omega
  · rw [h.input_head]
    have hh := hb.input_upper
    have hl := hb.input_lower
    have he := centered_cast center source.inputHead (by omega)
    omega
  · rw [h.output_length]; have := hb.output; omega
  · by_cases hreg : j < 256 + L.registerCount
    · have he : j = L.bitRegister (j - 256) := by unfold Layout.bitRegister; omega
      rw [he, h.registers (j - 256) (by omega)]
      cases source.registers (j - 256) <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega
    · let k := j - (256 + L.registerCount)
      have hk : k < L.tapeCount := by unfold k Layout.frameEnd at *; omega
      have he : j = L.tapeHead k := by unfold Layout.tapeHead k; omega
      rw [he, h.tape_heads k hk]
      have hh := hb.tape_upper k
      have hl := hb.tape_lower k
      have he := centered_cast center (source.tapes k).head (by omega)
      omega

/-- The entry cap is re-established after every simulated instruction. Dead
caller cells retain their bounded values; every bank write is at most two. -/
theorem cleared_boundary_bound {L : Layout} {origin center : ℕ} {bits : List Bool}
    {source : BitRAMState} {s t : Store} {bound used : ℕ}
    (entry : IndexWidth.IndexBound bound s.val) (frame : WriteFrame L s.val t.val)
    (h : Ready L origin center bits source t) (hb : SourceBounds source used)
    (hu : used ≤ center) (hc : 2 * center ≤ bound) (hp : source.pc ≤ bound)
    (h2 : 2 ≤ bound) : IndexWidth.IndexBound bound (clearedScratch t).val := by
  have hf := frame.trans (clearScratch_frame L t)
  intro j
  by_cases hs : ScalarCell L j
  · exact represented_scalar_bound (clearScratch_ready t h) hb hu hc hp h2
      (clearScratch_small t h) j hs
  · rcases hf j hs with he | hh
    · rw [he]; exact entry j
    · exact hh.trans h2

end Maxwell.Cost.RealSimulation
