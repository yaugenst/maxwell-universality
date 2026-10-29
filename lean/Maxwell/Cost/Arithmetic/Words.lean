import Maxwell.Cost.Arithmetic.Frame
import Maxwell.Cost.TapeOps

namespace Maxwell.Cost

theorem BitTape.shifted_represents (bits : List Bool) (origin : ℤ) :
    TapeRepresents (BitTape.shifted bits origin) bits := by
  intro k
  simp [BitTape.shifted]

theorem writeCells_blank (bits : List Bool) (origin : ℤ) :
    writeCells (fun _ => none) origin bits = (BitTape.shifted bits origin).cells := by
  induction bits using List.reverseRecOn with
  | nil => simp [writeCells, BitTape.shifted]
  | append_singleton bits b ih =>
    rw [← writeCells_append, ih]
    have hh := congrArg BitTape.cells (BitTape.shiftedEnd_append_write bits origin b)
    simpa [writeCells, BitTape.shiftedEnd, BitTape.write] using hh

theorem TapeWrites.blank {s t : BitTape} {bits : List Bool} {origin : ℤ}
    (h : TapeWrites s t bits) (hs : s = {BitTape.blank with head := origin}) :
    t = BitTape.shiftedEnd bits origin := by
  apply BitTape.ext
  · simpa [hs, BitTape.shiftedEnd] using h.head
  · simpa [hs, BitTape.blank, BitTape.shiftedEnd, writeCells_blank] using h.cells

/-- A complete reusable addition contract for exact finite words at
arbitrary tape origins. All words and scratch-state changes are consequences
of the executed fixed code. -/
theorem rippleAdder_words (input : List Bool) (randomTape : ℕ → Bool)
    (s : BitRAMState) (xs ys : List Bool) (xorigin yorigin zorigin : ℤ)
    (hpc : s.pc = 0) (hcarry : s.registers 2 = false)
    (hx : s.tapes 0 = BitTape.shifted xs xorigin)
    (hy : s.tapes 1 = BitTape.shifted ys yorigin)
    (hz : s.tapes 2 = {BitTape.blank with head := zorigin}) :
    ∃ cost final, cost ≤ 18 * max xs.length ys.length + 28 ∧
      PricedSteps (rippleAdder.next input randomTape) cost s final ∧ final.pc = 17 ∧
      final.tapes 0 = {BitTape.shifted xs xorigin with
        head := xorigin + (addBits false xs ys).length} ∧
      final.tapes 1 = {BitTape.shifted ys yorigin with
        head := yorigin + (addBits false xs ys).length} ∧
      final.tapes 2 = BitTape.shiftedEnd (addBits false xs ys) zorigin ∧
      rippleFrame final = rippleFrame s := by
  have hxr : TapeRepresents (s.tapes 0) xs := hx ▸ BitTape.shifted_represents xs xorigin
  have hyr : TapeRepresents (s.tapes 1) ys := hy ▸ BitTape.shifted_represents ys yorigin
  obtain ⟨cost, final, hc, hsteps, hhalt, hwrites⟩ :=
    rippleAdder_simulation input randomTape s xs ys hpc hxr hyr
  rw [hcarry] at hwrites
  obtain ⟨hp, hxc, hyc, hxh, hyh⟩ :=
    rippleAdder_tape_effects input randomTape hsteps hpc hhalt hwrites
  refine ⟨cost, final, hc, hsteps, hp, ?_, ?_, hwrites.blank hz,
    rippleAdder_execution_frame input randomTape hsteps⟩
  · apply BitTape.ext
    · simpa [hx, BitTape.shifted] using hxh
    · simpa [hx] using hxc
  · apply BitTape.ext
    · simpa [hy, BitTape.shifted] using hyh
    · simpa [hy] using hyc

end Maxwell.Cost
