import Maxwell.Cost.RealSimulation.WidthSimulation

namespace Maxwell.Cost.RealSimulation
open Control

/-- Every actual target state obeys the word bound. The source width premise
concerns actual charged prefixes, while the target bound is proved here by
the finite simulation, its concrete write frame, and charged scratch reset. -/
theorem width_interpreter_priced (M : BitRAM) (input : RAMInput) (tape : ℕ → Bool)
    {origin center : ℕ} {bits : List Bool} {a b : BitRAMState} {n W : ℕ}
    (source : PricedSteps (M.next bits tape) n a b) (halt : M.next bits tape b = none)
    (width : PrefixAddressBound M bits tape a n W)
    (used : ℕ) (bounds : SourceBounds a used) (cap : used + n ≤ center)
    (center_bound : 2 * center ≤ 2 ^ W) (pc_bound : programPCCap M ≤ 2 ^ W)
    (two : 2 ≤ 2 ^ W)
    (machine : Machine) (base exitPC : ℕ) (placement : Placed machine (widthInterpreter M) base exitPC)
    (literals : IndexWidth.LiteralBound (2 ^ W) machine)
    (inputs : IndexWidth.InputBound (2 ^ W) input)
    (s : Store) (hs : Ready (footprint M.code) origin center bits a s)
    (entry : IndexWidth.IndexBound (2 ^ W) s.val) :
    ∃ cost t, cost ≤ widthConstant M * n + terminalConstant M + 27 ∧
      Executes input tape (widthInterpreter M) cost s t ∧
      Represents (footprint M.code) origin center bits b t.val ∧
      VisitedSteps (machine.next input tape) (IndexWordWidth ((widthConstant M + 1) * (W + 1)))
        cost (s.place base) (t.place exitPC) := by
  have hconst : 1 ≤ widthConstant M := by unfold widthConstant; omega
  have hW : 1 ≤ W := by
    by_contra hn
    have hz : W = 0 := by omega
    simp [hz] at two
  induction source generalizing used s with
  | refl a =>
    obtain ⟨cost, t, hc, he, hr⟩ := width_terminal M input tape halt s hs
    have hc' : cost ≤ widthConstant M * (W + 1) := by
      have hh : terminalConstant M + 27 ≤ widthConstant M := by
        simp only [terminalConstant, widthConstant, dispatchConstant, instructionConstant]
        omega
      nlinarith
    exact ⟨cost, t, by simpa using hc, he, hr,
      visited_segment_width (s := s.place base) entry literals inputs hc'
        (he.placed machine base exitPC placement)⟩
  | @step n extra a b c hnext rest ih =>
    have hu : used < center := by omega
    have hw : a.address.length ≤ W := width 0 a (by omega) (.refl a)
    have hx : extra ≤ W := (source_extra_le hnext).trans (max_le hW hw)
    obtain ⟨cost, t, hc, he, ht, hf⟩ := dispatch_next_framed M input tape hnext s hs
      (bounds.input_before_cap hu) (fun t => bounds.tape_before_cap hu t)
    have hb : SourceBounds b (used + (extra + 1)) :=
      (bounds.step hnext).mono (by omega)
    have hready := clearScratch_ready t ht
    have hbnd := cleared_boundary_bound entry hf ht hb (by omega) center_bound
      ((next_pc_bound hnext).trans pc_bound) two
    obtain ⟨restCost, u, hr, er, hrepr, hvisited⟩ := ih halt (width.tail hnext)
      (used + (extra + 1)) hb (by omega) (clearedScratch t) hready hbnd
    have body : Executes input tape (widthBody M) (cost + 27) s (clearedScratch t) :=
      he.seq (clearScratch_executes input tape t)
    have test : Steps (machine.next input tape) 1 (s.place base) (s.place (base + 1)) := by
      apply Steps.step (rest := Steps.refl _)
      simp [Machine.next, Store.place, placement.loop_head, hs.one, hs.active]
    have segment : Steps (machine.next input tape) (1 + (cost + 27))
        (s.place base) ((clearedScratch t).place base) :=
      test.trans (body.placed machine (base + 1) base placement.loop_body)
    have hsCost : 1 + (cost + 27) ≤ widthConstant M * (W + 1) := by
      unfold widthConstant
      nlinarith
    have segmentVisited := visited_segment_width (s := s.place base) entry literals inputs hsCost segment
    refine ⟨1 + (cost + 27) + restCost, u, ?_,
      Executes.more (by rw [hs.one, hs.active]) body er, hrepr, segmentVisited.trans hvisited⟩
    unfold widthConstant at *
    nlinarith

end Maxwell.Cost.RealSimulation
