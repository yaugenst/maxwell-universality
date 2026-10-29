import Maxwell.Cost.RealMidpointRegister.Program

namespace Maxwell.Cost.RealMidpointRegister
open RealSparse (execute_sound)

theorem approximation_sign (x : ℝ) (p : ℕ) :
    (decide ((RealMidpoint.approximation x p).num < 0)).toNat = if 0 ≤ x then 0 else 1 := by
  rw [RealMidpoint.approximation_num]
  by_cases hz : x = 0
  · subst x; simp
  · by_cases hpos : 0 ≤ x <;>
      simp [RealMidpoint.numerator, RealMidpoint.magnitude, hz, hpos]
    all_goals omega

/-- The full subroutine contract uses only registers already held by the
caller. No new external input or uncharged numeric conversion is needed. -/
theorem terminates (input : RAMInput) (tape : ℕ → Bool) (s : RAMState)
    (x : ℝ) (p : ℕ) (hpc : s.pc = 0) (hx : s.words 16 = x) (hp : s.indices 27 = p) :
    ∃ cost : ℕ, ∃ t : RAMState,
      cost ≤ 13 * p + 52 ∧ Terminates (program.next input tape) cost s t ∧
      t.pc = 77 ∧ t.words 4 = (RealMidpoint.approximation x p : ℝ) ∧
      t.indices 16 = (RealMidpoint.approximation x p).num.natAbs ∧
      t.indices 17 = (RealMidpoint.approximation x p).den ∧
      t.indices 18 = (decide ((RealMidpoint.approximation x p).num < 0)).toNat ∧
      (∀ i, 8 ≤ i → t.words i = s.words i) ∧
      (∀ i, 6 ≤ i → i ≠ 16 → i ≠ 17 → i ≠ 18 → t.indices i = s.indices i) ∧
      t.output = s.output ∧ t.indexOutput = s.indexOutput ∧ t.randomCursor = s.randomCursor := by
  obtain ⟨cost, f, hcost, hf, hfpc, hfvalue, hfnum, hfden, hfzero⟩ := source_terminates x p tape
  have hkernel := transport input tape s x p hx hp hf rfl
  have hcall := contains_kernel.call input tape hkernel.toSteps (by
    simp [kernel, RealMidpoint.program, RealRound.program, hfpc, overlay, adapt])
  have hclear := execute_sound _ (clear_steps input tape s hpc)
  rw [cleared_eq s hpc] at hclear
  let t := exported {overlay s f with pc := 70} x
  have hexport := execute_sound _ (export_steps input tape {overlay s f with pc := 70} x
    rfl (by simp [hfzero]) (by simp [hx]))
  refine ⟨14 + (cost + 1) + 5, t, by omega, ?_, by simp [t, exported], ?_, ?_, ?_, ?_,
    ?_, ?_, rfl, rfl, rfl⟩
  · exact ((hclear.trans hcall).trans hexport).terminates
      (Terminates.halt t (by
        simp [t, exported, program, kernel, RealMidpoint.program, RealRound.program, adapt,
          RAMInstruction.relocate, Machine.next, RAMState.setIndex]))
  · simpa [t, exported, RAMState.setIndex] using hfvalue
  · simpa [t, exported, RAMState.setIndex] using hfnum
  · simpa [t, exported, RAMState.setIndex] using hfden
  · rw [approximation_sign]
    simp [t, exported, RAMState.setIndex]
  · intro i hi
    simp [t, exported, RAMState.setIndex, overlay, show ¬ i < 8 by omega]
  · intro i hi h16 h17 h18
    simp [t, exported, RAMState.setIndex, overlay, show ¬ i < 6 by omega, h16, h17, h18]

end Maxwell.Cost.RealMidpointRegister
