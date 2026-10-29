import Maxwell.Cost.RealPrivate.Halt
import Maxwell.Cost.RealPrivate.RunFrame

namespace Maxwell.Cost.RealPrivate
open RealSimulation.Control

theorem FinishFrame.runFrame {s t : Store} (h : FinishFrame s t) (origin : ℕ) :
    RunFrame origin s.val t.val := by
  refine ⟨?_, ?_, h.output, h.indexOutput⟩
  · intro j _ _; rw [h.words]
  · intro j hj _ hm
    exact h.indices j (by unfold dispatchRegister; omega)
      (by unfold statusRegister; omega) (by unfold activeRegister; omega)

def loopBound (L : Layout) (M : Machine) : ℕ :=
  4 * M.code.length + instructionBound L + 10

structure LoopPost (L : Layout) (M : Machine) (sourceInput : RAMInput) (tape : ℕ → Bool)
    (origin fuel : ℕ) (source stop : RAMState) (written finalLog : List ℕ)
    (s t : Store) : Prop where
  represents : Represents origin stop finalLog t.val
  covered : Covered stop finalLog
  log_bound : finalLog.length ≤ written.length + fuel
  trace : Steps (M.next sourceInput tape) (runCapped (M.next sourceInput tape) fuel source).instructions source stop
  active : t.val.indices activeRegister = 0
  status : t.val.indices statusRegister = 0 ∨ t.val.indices statusRegister = 1
  finished : (runCapped (M.next sourceInput tape) fuel source).finished =
    if t.val.indices statusRegister = 1 then some stop else none
  fuel_bound : t.val.indices fuelRegister ≤ fuel
  frame : RunFrame origin s.val t.val

/-- The actual finite loop enforces its cap on every source input and tape.
Successful status agrees with the original machine's capped execution;
even an exhausted run retains a covered finite log for actual cleanup. -/
theorem cappedInterpreter_executes (L : Layout) (M : Machine)
    (externalInput sourceInput : RAMInput) (tape : ℕ → Bool)
    {origin : ℕ} {B : InputBuffer} (fuel : ℕ) (source : RAMState) (written : List ℕ)
    (s : Store) (h : Represents origin source written s.val)
    (hi : Inputs L origin B sourceInput s.val) (covered : Covered source written)
    (hf : s.val.indices fuelRegister = fuel) (hs : s.val.indices statusRegister = 0)
    (ha : s.val.indices activeRegister = 1) :
    ∃ cost t stop finalLog, cost ≤ loopBound L M * (fuel + 1) ∧
      Executes externalInput tape (cappedInterpreter L M) cost s t ∧
      LoopPost L M sourceInput tape origin fuel source stop written finalLog s t := by
  induction fuel generalizing source written s with
  | zero =>
    let t := s.put activeRegister 0
    have ht := h.put_control activeRegister 0 (Or.inr (Or.inr rfl))
    have htest : s.val.indices oneRegister ≤ s.val.indices activeRegister := by rw [h.one, ha]
    have hfuel : ¬ s.val.indices oneRegister ≤ s.val.indices fuelRegister := by rw [h.one, hf]; omega
    have hend : ¬ t.val.indices oneRegister ≤ t.val.indices activeRegister := by
      rw [ht.one]; simp [t]
    have he : Executes externalInput tape (cappedInterpreter L M) 5 s t :=
      Executes.more htest (Executes.no hfuel (literal_executes externalInput tape s activeRegister 0))
        (Executes.done hend)
    refine ⟨5, t, source, written, ?_, he, ht, covered, by omega, Steps.refl _, by simp [t], ?_, ?_, ?_, ?_⟩
    · unfold loopBound instructionBound; omega
    · left; simpa [t, statusRegister, activeRegister] using hs
    · simp [runCapped, t, statusRegister, activeRegister, show s.val.indices 166 = 0 from hs]
    · simpa [t, fuelRegister, activeRegister] using Nat.le_of_eq hf
    · exact runFrame_put s origin activeRegister 0 (Or.inr (Or.inl (by decide)))
  | succ fuel ih =>
    let s0 := s.put fuelRegister fuel
    have h0 := h.put_control fuelRegister fuel (Or.inl rfl)
    have frame0 : RunFrame origin s.val s0.val :=
      runFrame_put s origin fuelRegister fuel (Or.inr (Or.inl (by decide)))
    have input0 := frame0.inputs h.high hi
    have dec : Executes externalInput tape (subtract fuelRegister fuelRegister oneRegister) 2 s s0 := by
      simpa only [hf, h.one, Nat.add_sub_cancel] using
        subtract_executes externalInput tape s fuelRegister fuelRegister oneRegister
    have htest : s.val.indices oneRegister ≤ s.val.indices activeRegister := by rw [h.one, ha]
    have hmore : s.val.indices oneRegister ≤ s.val.indices fuelRegister := by rw [h.one, hf]; omega
    cases hn : M.next sourceInput tape source with
    | none =>
      obtain ⟨dcost, t, hd, ed, ht, _, hstatus, hactive, frame⟩ :=
        dispatch_next_none M externalInput sourceInput tape hn s0 h0 input0
      have hend : ¬ t.val.indices oneRegister ≤ t.val.indices activeRegister := by
        rw [ht.one, hactive]; omega
      have he : Executes externalInput tape (cappedInterpreter L M) (dcost + 5) s t := by
        have run := Executes.more htest (Executes.yes (no := literal activeRegister 0) hmore (dec.seq ed))
          (Executes.done hend)
        simpa only [cappedInterpreter,
          show 1 + (1 + (2 + dcost)) + 1 = dcost + 5 by omega] using run
      refine ⟨dcost + 5, t, source, written, ?_, he, ht, covered, by omega, ?_, hactive,
        Or.inr hstatus, ?_, ?_, frame0.trans (frame.runFrame origin)⟩
      · have hbase : dcost + 5 ≤ loopBound L M := by unfold loopBound instructionBound; omega
        exact hbase.trans (Nat.le_mul_of_pos_right _ (by omega))
      · simpa [runCapped, hn] using Steps.refl (next := M.next sourceInput tape) source
      · simp [runCapped, hn, hstatus]
      · rw [frame.indices fuelRegister (by decide) (by decide) (by decide)]
        simp [s0]
    | some next =>
      obtain ⟨op, hcode⟩ : ∃ op, M.code[source.pc]? = some op := by
        cases hc : M.code[source.pc]? with
        | none => simp [Machine.next, hc] at hn
        | some op => exact ⟨op, rfl⟩
      obtain ⟨dcost, u, hd, ed, hu, frame⟩ :=
        dispatch_next M externalInput sourceInput tape op hcode hn s0 h0 input0
      have huFuel : u.val.indices fuelRegister = fuel := by
        rw [frame.indices fuelRegister (by decide) (by unfold fuelRegister; have := h.high; omega)
          (by left; decide)]
        simp [s0]
      have huStatus : u.val.indices statusRegister = 0 := by
        rw [frame.indices statusRegister (by decide) (by unfold statusRegister; have := h.high; omega)
          (by left; decide)]
        simpa [s0, statusRegister, fuelRegister] using hs
      have huActive : u.val.indices activeRegister = 1 := by
        rw [frame.indices activeRegister (by decide) (by unfold activeRegister; have := h.high; omega)
          (by right; decide)]
        simpa [s0, activeRegister, fuelRegister] using ha
      obtain ⟨cost, t, stop, finalLog, hc, he, post⟩ := ih next (recorded op source written) u hu
        (frame.inputs h.high input0) (covered.next op hcode hn) huFuel huStatus huActive
      have run : Executes externalInput tape (cappedInterpreter L M) (dcost + cost + 4) s t := by
        have run := Executes.more htest (Executes.yes (no := literal activeRegister 0) hmore (dec.seq ed)) he
        simpa only [cappedInterpreter,
          show 1 + (1 + (2 + dcost)) + cost = dcost + cost + 4 by omega] using run
      refine ⟨dcost + cost + 4, t, stop, finalLog, ?_, run, post.represents, post.covered,
        ?_, ?_, post.active, post.status, ?_, post.fuel_bound.trans (by omega),
        frame0.trans (frame.runFrame.trans post.frame)⟩
      · have hbase : dcost + 4 ≤ loopBound L M := by unfold loopBound; omega
        calc
          dcost + cost + 4 ≤ loopBound L M + loopBound L M * (fuel + 1) := by omega
          _ = loopBound L M * (fuel + 1 + 1) := by ring
      · have hlen := recorded_length_le op source written
        have hpost := post.log_bound
        omega
      · simpa [runCapped, hn] using Steps.step hn post.trace
      · simpa [runCapped, hn] using post.finished

end Maxwell.Cost.RealPrivate
