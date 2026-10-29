import Maxwell.Cost.RealMidpoint

namespace Maxwell.Cost.RealMidpointRegister

/-- Turn the standalone rounder into a subroutine. Its two input reads use
caller registers; its three output instructions become charged no-ops. -/
def adapt : RAMInstruction → RAMInstruction
  | .input _ _ => .copy 0 16
  | .inputIndex _ _ => .indexCopy 2 27
  | .output _ | .outputIndex _ => .indexCopy 0 0
  | instruction => instruction

def kernel : Machine := ⟨RealMidpoint.program.code.map adapt⟩

/-- Only the work registers are overlaid. Every caller buffer, observation,
and random-tape position is preserved. -/
noncomputable def overlay (base s : RAMState) : RAMState where
  pc := s.pc
  words := fun i => if i < 8 then s.words i else base.words i
  indices := fun i => if i < 6 then s.indices i else base.indices i
  randomCursor := base.randomCursor
  output := base.output
  indexOutput := base.indexOutput

theorem overlay_word (base s : RAMState) (i : ℕ) (v : ℝ) (hi : i < 8) :
    overlay base (s.setWord i v) = (overlay base s).setWord i v := by
  unfold overlay RAMState.setWord
  congr 1
  funext j
  by_cases hji : j = i
  · subst j; simp [hi]
  · simp [hji]

theorem overlay_index (base s : RAMState) (i v : ℕ) (hi : i < 6) :
    overlay base (s.setIndex i v) = (overlay base s).setIndex i v := by
  unfold overlay RAMState.setIndex
  congr 1
  funext j
  by_cases hji : j = i
  · subst j; simp [hi]
  · simp [hji]

@[simp] theorem overlay_pc (base s : RAMState) : (overlay base s).pc = s.pc := rfl
@[simp] theorem overlay_words (base s : RAMState) (i : ℕ) :
    (overlay base s).words i = if i < 8 then s.words i else base.words i := rfl
@[simp] theorem overlay_indices (base s : RAMState) (i : ℕ) :
    (overlay base s).indices i = if i < 6 then s.indices i else base.indices i := rfl
@[simp] theorem overlay_pc_update (base s : RAMState) (pc : ℕ) :
    overlay base {s with pc := pc} = {overlay base s with pc := pc} := rfl
@[simp] theorem overlay_output (base s : RAMState) (pc : ℕ) (output : List ℝ) :
    overlay base {s with pc := pc, output := output} = {overlay base s with pc := pc} := rfl
@[simp] theorem overlay_indexOutput (base s : RAMState) (pc : ℕ) (output : List ℕ) :
    overlay base {s with pc := pc, indexOutput := output} = {overlay base s with pc := pc} := rfl

theorem setIndex_self (s : RAMState) (i : ℕ) :
    s.setIndex i (s.indices i) = {s with pc := s.pc + 1} := by
  simp [RAMState.setIndex]

theorem setIndex_of_eq (s : RAMState) (i v : ℕ) (h : s.indices i = v) :
    s.setIndex i v = {s with pc := s.pc + 1} := by
  rw [← h, setIndex_self]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2200000 in
theorem next_overlay (input : RAMInput) (tape : ℕ → Bool) (base s : RAMState)
    (x : ℝ) (p : ℕ) (hx : base.words 16 = x) (hp : base.indices 27 = p)
    (hzero : s.indices 0 = 0) :
    kernel.next input tape (overlay base s) =
      (RealMidpoint.program.next (RealRound.input x p) tape s).map (overlay base) := by
  by_cases hpc : s.pc < 56
  · interval_cases he : s.pc <;>
      simp [kernel, RealMidpoint.program, RealRound.program, adapt, Machine.next, he,
        RealRound.input, hzero, hx, hp, overlay_word, overlay_index, setIndex_of_eq]
  · have hs : RealMidpoint.program.code[s.pc]? = none := List.getElem?_eq_none (by
      simpa [RealMidpoint.program, RealRound.program] using Nat.le_of_not_gt hpc)
    simp [kernel, Machine.next, overlay, hs, List.getElem?_map]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2200000 in
theorem next_zero (tape : ℕ → Bool) (s t : RAMState) (x : ℝ) (p : ℕ)
    (hzero : s.indices 0 = 0)
    (h : RealMidpoint.program.next (RealRound.input x p) tape s = some t) : t.indices 0 = 0 := by
  have hpc : s.pc < 56 := by
    simpa [RealMidpoint.program, RealRound.program] using
      RealMidpoint.program.next_code_present (RealRound.input x p) tape s t h
  interval_cases he : s.pc <;>
    simp [RealMidpoint.program, RealRound.program, Machine.next, he] at h <;>
    cases h <;> simp [RAMState.setWord, RAMState.setIndex, hzero]

theorem transport (input : RAMInput) (tape : ℕ → Bool) (base : RAMState)
    (x : ℝ) (p : ℕ) (hx : base.words 16 = x) (hp : base.indices 27 = p)
    {cost : ℕ} {s t : RAMState}
    (h : Terminates (RealMidpoint.program.next (RealRound.input x p) tape) cost s t)
    (hzero : s.indices 0 = 0) :
    Terminates (kernel.next input tape) cost (overlay base s) (overlay base t) := by
  induction h with
  | halt s hs =>
    exact Terminates.halt _ (by rw [next_overlay input tape base s x p hx hp hzero, hs]; rfl)
  | @step n s t u hs _ ih =>
    apply Terminates.step (by rw [next_overlay input tape base s x p hx hp hzero, hs]; rfl)
    exact ih (next_zero tape s t x p hzero hs)

end Maxwell.Cost.RealMidpointRegister
