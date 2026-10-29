import Maxwell.Cost.MemoryWord
import Maxwell.Cost.MemoryBit.Width

namespace Maxwell.Cost.MemoryWord

set_option maxRecDepth 8192 in
private theorem fetch_visited (input : List Bool) (tape : ℕ→Bool)
    (s : BitRAMState) (b : Bool) (W : ℕ) (hpc : s.pc=0)
    (hread : (s.tapes 6).read=some b) (hw : Address.Within W s) :
    VisitedPriced (readProgram.next input tape) (Address.Within W) 3 s (fetched s b) := by
  apply checkedInstructions_sound _ (Address.Within W) (instructions := 2)
  simp [checkedInstructions,Address.Within,readProgram,BitRAM.next,hpc,hread,
    fetched,BitRAMState.setRegister,show s.address.length≤W from hw]

set_option maxRecDepth 8192 in
private theorem stop_visited (input : List Bool) (tape : ℕ→Bool)
    (s : BitRAMState) (W : ℕ) (hpc : s.pc=0)
    (hread : (s.tapes 6).read=none) (hw : Address.Within W s) :
    VisitedPriced (readProgram.next input tape) (Address.Within W) 3 s (stopped s) := by
  apply checkedInstructions_sound _ (Address.Within W) (instructions := 2)
  simp [checkedInstructions,Address.Within,readProgram,BitRAM.next,hpc,hread,
    stopped,BitRAMState.setRegister,show s.address.length≤W from hw]

set_option maxRecDepth 8192 in
private theorem advance_visited (input : List Bool) (tape : ℕ→Bool)
    (s : BitRAMState) (W : ℕ) (hpc : s.pc=11) (hw : Address.Within W s) :
    VisitedPriced (readProgram.next input tape) (Address.Within W) 4 s (advanced s) := by
  apply checkedInstructions_sound _ (Address.Within W) (instructions := 4)
  simp [checkedInstructions,Address.Within,readProgram,BitRAM.next,hpc,advanced,
    MemoryBit.program,Address.load,Increment.program,BitRAMInstruction.relocate,
    BitRAMState.setTape,BitTape.write,show s.address.length≤W from hw]

set_option maxRecDepth 8192 in
theorem cycle_visited (input : List Bool) (tape : ℕ→Bool) (s : BitRAMState)
    (address : List Bool) (origin : ℤ) (b : Bool) (hpc : s.pc=0)
    (haddress : s.tapes 5=BitTape.shiftedEnd address origin)
    (hclock : (s.tapes 6).read=some b) :
    ∃ cost t, cost≤15*address.length+24 ∧
      VisitedPriced (readProgram.next input tape)
        (Address.Within (max s.address.length address.length)) cost s t ∧ t.pc=0 ∧
      t.tapes 5=BitTape.shiftedEnd (Increment.bits address) origin ∧
      t.tapes 6={s.tapes 6 with head:=(s.tapes 6).head+1} ∧ t.address=address := by
  let W := max s.address.length address.length
  have hf := fetch_visited input tape s b W hpc hclock (le_max_left _ _)
  obtain ⟨r,hr,hrpc,hra,_,hr5,hrf⟩ := MemoryBit.read_steps 5 input tape address origin
    {fetched s b with pc:=0} rfl haddress
  have hr' := MemoryBit.access_trace_visited 5 (.readMemory 28) (Or.inl rfl)
    input tape address origin {fetched s b with pc:=0} r rfl haddress hr
  let readState : BitRAMState := {r with pc:=11}
  have hR : VisitedPriced (readProgram.next input tape) (Address.Within W)
      (7*address.length+7+1) (fetched s b) readState :=
    contains_read.visited_call_at input tape (fetched s b) r rfl hr'
      (by simp [MemoryBit.program,Address.load,hrpc,BitRAMInstruction.relocate])
  have ha := advance_visited input tape readState W rfl hR.finish
  have ha5 : (advanced readState).tapes 5=BitTape.shifted address origin := by
    simp [advanced,readState,hr5,BitTape.shifted]
  have ha6 : (advanced readState).tapes 6={s.tapes 6 with head:=(s.tapes 6).head+1} := by
    have hr6 : readState.tapes 6=s.tapes 6 := hrf.2.2.2.2.1 6 (by omega)
    simp [advanced,hr6]
  obtain ⟨ic,u,hic,hu,hupc,hu5,huf⟩ := Increment.simulation 5 input tape address origin
    {advanced readState with pc:=0} rfl ha5
  have hu' : VisitedPriced ((Increment.program 5).next input tape) (Address.Within W) ic
      {advanced readState with pc:=0} u :=
    hu.visited_noAddressPush (by decide) ha.finish
  let final : BitRAMState := {u with pc:=27}
  have hU : VisitedPriced (readProgram.next input tape) (Address.Within W) (ic+1)
      (advanced readState) final :=
    contains_increment.visited_call_at input tape (advanced readState) u rfl hu'
      (by simp [Increment.program,hupc])
  have hfooter : VisitedPriced (readProgram.next input tape) (Address.Within W) 1
      final {final with pc:=0} := by
    apply checkedInstructions_sound _ (Address.Within W) (instructions := 1)
    have hh : u.address.length≤W := hU.finish
    simp [checkedInstructions,Address.Within,readProgram,BitRAM.next,final,MemoryBit.program,
      Address.load,Increment.program,BitRAMInstruction.relocate,hh]
  refine ⟨_,{final with pc:=0},by omega,((hf.trans hR).trans ha).trans (hU.trans hfooter),rfl,hu5,?_,?_⟩
  · exact (huf.2.2.2.2.2.1 6 (by omega)).trans ha6
  · exact huf.1.trans hra

/-- All repeated reads have width bounded by the original address length
plus the requested bit count, also accounting for a larger caller address. -/
theorem loop_visited (input : List Bool) (tape : ℕ→Bool) (clock address : List Bool)
    (origin : ℤ) (B W : ℕ) (s : BitRAMState) (hwidth : address.length≤B)
    (hW : B+clock.length≤W) (hsW : Address.Within W s) (hpc : s.pc=0)
    (haddress : s.tapes 5=BitTape.shiftedEnd address origin)
    (hclock : TapeRepresents (s.tapes 6) clock) :
    ∃ cost t, cost≤clock.length*(15*(B+clock.length)+24)+3 ∧
      VisitedPriced (readProgram.next input tape) (Address.Within W) cost s t ∧ t.pc=28 := by
  induction clock generalizing address B s with
  | nil =>
    exact ⟨3,stopped s,by simp,stop_visited input tape s W hpc hclock.read hsW,rfl⟩
  | cons b clock ih =>
    obtain ⟨cc,a,hcc,ea,ha,ha5,ha6,_⟩ := cycle_visited input tape s address origin b hpc haddress hclock.read
    have ea' : VisitedPriced (readProgram.next input tape) (Address.Within W) cc s a := by
      apply ea.mono
      intro u hu
      have hm : max s.address.length address.length≤W := max_le hsW (by omega)
      exact hu.trans hm
    have hcwidth : (Increment.bits address).length≤B+1 := (Increment.bits_length_le address).trans (by omega)
    have hcclock : TapeRepresents (a.tapes 6) clock := by rw [ha6]; exact hclock.moveRight
    obtain ⟨rc,t,hrc,er,ht⟩ := ih (Increment.bits address) (B+1) a hcwidth (by simp at hW; omega)
      ea'.finish ha ha5 hcclock
    refine ⟨cc+rc,t,?_,ea'.trans er,ht⟩
    simp only [List.length_cons] at *
    nlinarith


/-- The prefix guarantee includes every actual charged prefix, independently
of a larger polynomial fuel cap supplied by a caller. -/
theorem read_prefix (input : List Bool) (tape : ℕ→Bool) (address clock : List Bool)
    (origin : ℤ) (s : BitRAMState) (hpc : s.pc=0)
    (haddress : s.tapes 5=BitTape.shiftedEnd address origin)
    (hclock : TapeRepresents (s.tapes 6) clock)
    (n : ℕ) (u : BitRAMState) (hu : PricedSteps (readProgram.next input tape) n s u) :
    u.address.length≤max s.address.length (address.length+clock.length) := by
  obtain ⟨cost,t,_,ht,hpcout⟩ := loop_visited input tape clock address origin address.length
    (max s.address.length (address.length+clock.length)) s le_rfl (le_max_right _ _) (le_max_left _ _)
    hpc haddress hclock
  apply ht.prefix_halt _ hu
  simp [BitRAM.next,readProgram,hpcout,MemoryBit.program,Address.load,Increment.program,BitRAMInstruction.relocate]

/-- Upgrade an existing word-read execution while preserving its exact
charged cost, final state, and all of its established functional results. -/
theorem read_trace_visited (input : List Bool) (tape : ℕ→Bool) (address clock : List Bool)
    (origin : ℤ) (s t : BitRAMState) (hpc : s.pc=0)
    (haddress : s.tapes 5=BitTape.shiftedEnd address origin)
    (hclock : TapeRepresents (s.tapes 6) clock) (cost : ℕ)
    (h : PricedSteps (readProgram.next input tape) cost s t) (hhalt : t.pc=28) :
    VisitedPriced (readProgram.next input tape)
      (Address.Within (max s.address.length (address.length+clock.length))) cost s t := by
  obtain ⟨nc,u,_,hu,hpcout⟩ := loop_visited input tape clock address origin address.length
    (max s.address.length (address.length+clock.length)) s le_rfl (le_max_right _ _) (le_max_left _ _)
    hpc haddress hclock
  have he := hu.steps.halted_unique (by
    simp [BitRAM.next,readProgram,hpcout,MemoryBit.program,Address.load,Increment.program,BitRAMInstruction.relocate]) h (by
    simp [BitRAM.next,readProgram,hhalt,MemoryBit.program,Address.load,Increment.program,BitRAMInstruction.relocate])
  rcases he with ⟨rfl,rfl⟩
  exact hu

end Maxwell.Cost.MemoryWord
