import Maxwell.Cost.Multiplication.Tapes

/-! The true-bit Horner addition cycle, assembled from actual contained
subroutines. Every return and the final jump are charged machine steps. -/

namespace Maxwell.Cost.HornerMultiply

/-- The addition cycle preserves multiplier tape 3 and every other tape
outside 0/1/2. Boolean registers outside the arithmetic and tape scratch
sets are preserved, including the outer loop's registers 12/13/14. -/
def addCycleFrame (s t : BitRAMState) : Prop :=
  t.address = s.address ∧ t.inputHead = s.inputHead ∧ t.memory = s.memory ∧
  t.randomCursor = s.randomCursor ∧ t.output = s.output ∧
  (∀ i, 3 ≤ i → t.tapes i = s.tapes i) ∧
  (∀ i, 12 ≤ i → i ≠ 24 → i ≠ 25 → i ≠ 26 → i ≠ 27 → t.registers i = s.registers i)

theorem addCycleFrame.trans {s t u : BitRAMState}
    (h : addCycleFrame s t) (k : addCycleFrame t u) : addCycleFrame s u := by
  rcases h with ⟨ha, hi, hm, hr, ho, ht, hg⟩
  rcases k with ⟨ka, ki, km, kr, ko, kt, kg⟩
  exact ⟨ka.trans ha, ki.trans hi, km.trans hm, kr.trans hr, ko.trans ho,
    fun i h3 => (kt i h3).trans (ht i h3),
    fun i h12 h24 h25 h26 h27 => (kg i h12 h24 h25 h26 h27).trans (hg i h12 h24 h25 h26 h27)⟩

theorem addCycleFrame_of_ripple {s t : BitRAMState} (h : rippleFrame t = rippleFrame s) :
    addCycleFrame s t := by
  simp only [rippleFrame, Prod.mk.injEq] at h
  rcases h with ⟨ha, hi, hm, hr, ho, hg, ht⟩
  refine ⟨ha, hi, hm, hr, ho, ?_, ?_⟩
  · intro i h3
    simpa [Nat.sub_add_cancel h3] using congrFun ht (i - 3)
  · intro i h12 _ _ _ _
    simpa [Nat.sub_add_cancel h12] using congrFun hg (i - 12)

theorem addCycleFrame_of_tapeOps {source target : ℕ} {s t : BitRAMState}
    (hsource : source < 3) (htarget : target < 3) (h : TapeOps.Frame source target s t) :
    addCycleFrame s t := by
  rcases h with ⟨ha, hi, hm, hr, ho, ht, hg⟩
  exact ⟨ha, hi, hm, hr, ho, fun i h3 => ht i (by omega) (by omega),
    fun i _ _ _ h26 h27 => hg i h26 h27⟩

theorem finishAt_addCycleFrame (workTape : ℕ) (hwork : workTape < 3) (origin : ℤ)
    (s : BitRAMState) : addCycleFrame s (Rewind.finishAt workTape origin s) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro i h3
    simp [Rewind.finishAt, show i ≠ workTape by omega]
  · intro i _ h24 h25 _ _
    simp [Rewind.finishAt, h24, h25]

private theorem call_at {body : BitRAM} {base returnPC cost : ℕ}
    (hc : program.Contains body base returnPC) (input : List Bool) (tape : ℕ → Bool)
    (s t : BitRAMState) (hpc : s.pc = base)
    (hsteps : PricedSteps (body.next input tape) cost {s with pc := 0} t)
    (hhalt : body.code[t.pc]? = some .halt) :
    PricedSteps (program.next input tape) (cost + 1) s {t with pc := returnPC} := by
  have h := hc.call input tape hsteps hhalt
  have hid : ({s with pc := 0} : BitRAMState).relocate base = s := by
    simp [BitRAMState.relocate, ← hpc]
  rwa [hid] at h

private theorem tapeOps_other_tape {source target : ℕ} {s t : BitRAMState}
    (h : TapeOps.Frame source target s t) (i : ℕ) (hs : i ≠ source) (ht : i ≠ target) :
    t.tapes i = s.tapes i := h.2.2.2.2.2.1 i hs ht

/-- Exact true-bit addition path in the fixed 72-instruction multiplier.
The new accumulator origin is the end of the cleared old accumulator;
the code discovers all origins by tape scans, not free pointer arithmetic. -/
theorem addCycle (input : List Bool) (tape : ℕ → Bool)
    (s : BitRAMState) (acc xs : List Bool) (ao xo zo : ℤ)
    (hacc : 0 < acc.length) (hxs : 0 < xs.length)
    (hpc : s.pc = 10) (hcarry : s.registers 2 = false)
    (h0 : s.tapes 0 = BitTape.shifted acc ao)
    (h1 : s.tapes 1 = BitTape.shifted xs xo)
    (h2 : s.tapes 2 = {BitTape.blank with head := zo}) :
    ∃ cost t, cost ≤ 50 * (acc.length + xs.length + 2) ∧
      PricedSteps (program.next input tape) cost s t ∧ t.pc = 2 ∧
      t.tapes 0 = BitTape.shifted (addBits false acc xs) (ao + acc.length) ∧
      t.tapes 1 = BitTape.shifted xs xo ∧
      t.tapes 2 = {BitTape.blank with head := zo + (addBits false acc xs).length} ∧
      addCycleFrame s t := by
  let sum := addBits false acc xs
  have hlen : max acc.length xs.length ≤ sum.length := addBits_length_ge false acc xs
  have hlenUpper : sum.length ≤ max acc.length xs.length + 1 := addBits_length_le false acc xs
  obtain ⟨addCost, a, hcost, hadd, hapc, ha0, ha1, ha2, haf⟩ :=
    rippleAdder_words input tape {s with pc := 0} acc xs ao xo zo rfl hcarry h0 h1 h2
  let sA : BitRAMState := {a with pc := 28}
  have hA : PricedSteps (program.next input tape) (addCost + 1) s sA :=
    call_at contains_add input tape s a hpc hadd (by simp [rippleAdder, hapc])
  have hAf : addCycleFrame s sA := addCycleFrame_of_ripple haf

  let r0 := RewindOvershoot.finish 0 ao {sA with pc := 0}
  let sR0 : BitRAMState := {r0 with pc := 37}
  have hr0 := RewindOvershoot.shifted_steps 0 ao input tape acc sum.length hacc
    ((le_max_left _ _).trans hlen) {sA with pc := 0} rfl ha0
  have hR0 : PricedSteps (program.next input tape) (4 * sum.length + 6 + 1) sA sR0 :=
    call_at contains_rewind_left input tape sA r0 rfl hr0
      (by simp [r0, RewindOvershoot.finish, RewindOvershoot.program,
        BitRAM.link, RewindOvershoot.preamble, Rewind.program])
  have hR0f : addCycleFrame sA sR0 := finishAt_addCycleFrame 0 (by omega) ao {sA with pc := 0}
  have hr00 : sR0.tapes 0 = BitTape.shifted acc ao :=
    RewindOvershoot.finish_shifted 0 ao acc sum.length {sA with pc := 0} ha0
  have hr01 : sR0.tapes 1 = {BitTape.shifted xs xo with head := xo + sum.length} := by
    simpa [sR0, r0, RewindOvershoot.finish, Rewind.finishAt, sA] using ha1
  have hr02 : sR0.tapes 2 = BitTape.shiftedEnd sum zo := by
    simpa [sR0, r0, RewindOvershoot.finish, Rewind.finishAt, sA] using ha2

  obtain ⟨c, hc, hcpc, hc0, hcf⟩ := TapeOps.clear_steps 0 input tape acc ao
    {sR0 with pc := 0} rfl hr00
  let sC : BitRAMState := {c with pc := 43}
  have hC : PricedSteps (program.next input tape) (6 * acc.length + 3 + 1) sR0 sC :=
    call_at contains_clear input tape sR0 c rfl hc (by simp [TapeOps.clear, hcpc])
  have hCf : addCycleFrame sR0 sC := addCycleFrame_of_tapeOps (by omega) (by omega) hcf
  have hc1 : sC.tapes 1 = {BitTape.shifted xs xo with head := xo + sum.length} :=
    (tapeOps_other_tape hcf 1 (by omega) (by omega)).trans hr01
  have hc2 : sC.tapes 2 = BitTape.shiftedEnd sum zo :=
    (tapeOps_other_tape hcf 2 (by omega) (by omega)).trans hr02

  let r2 := Rewind.finishAt 2 zo {sC with pc := 0}
  let sR2 : BitRAMState := {r2 with pc := 48}
  have hr2 := Rewind.shiftedEnd_steps 2 zo input tape sum {sC with pc := 0} rfl hc2
  have hR2 : PricedSteps (program.next input tape) (4 * sum.length + 5 + 1) sC sR2 :=
    call_at contains_rewind_output input tape sC r2 rfl hr2
      (by simp [r2, Rewind.finishAt, Rewind.program])
  have hR2f : addCycleFrame sC sR2 := finishAt_addCycleFrame 2 (by omega) zo {sC with pc := 0}
  have hr22 : sR2.tapes 2 = BitTape.shifted sum zo :=
    Rewind.finishAt_shiftedEnd 2 zo sum {sC with pc := 0} hc2
  have hr20 : sR2.tapes 0 = {BitTape.blank with head := ao + acc.length} := by
    simpa [sR2, r2, Rewind.finishAt, sC] using hc0
  have hr21 : sR2.tapes 1 = {BitTape.shifted xs xo with head := xo + sum.length} := by
    simpa [sR2, r2, Rewind.finishAt] using hc1

  obtain ⟨cp, hcp, hcppc, hcp2, hcp0, hcpf⟩ := TapeOps.copyClear_to_blank_steps 2 0 (by omega)
    input tape sum zo (ao + acc.length) {sR2 with pc := 0} rfl hr22 hr20
  let sCP : BitRAMState := {cp with pc := 56}
  have hCP : PricedSteps (program.next input tape) (8 * sum.length + 3 + 1) sR2 sCP :=
    call_at contains_copy input tape sR2 cp rfl hcp (by simp [TapeOps.copyClear, hcppc])
  have hCPf : addCycleFrame sR2 sCP := addCycleFrame_of_tapeOps (by omega) (by omega) hcpf
  have hcp1 : sCP.tapes 1 = {BitTape.shifted xs xo with head := xo + sum.length} :=
    (tapeOps_other_tape hcpf 1 (by omega) (by omega)).trans hr21

  let ra := Rewind.finishAt 0 (ao + acc.length) {sCP with pc := 0}
  let sRA : BitRAMState := {ra with pc := 61}
  have hra := Rewind.shiftedEnd_steps 0 (ao + acc.length) input tape sum {sCP with pc := 0} rfl hcp0
  have hRA : PricedSteps (program.next input tape) (4 * sum.length + 5 + 1) sCP sRA :=
    call_at contains_rewind_accumulator input tape sCP ra rfl hra
      (by simp [ra, Rewind.finishAt, Rewind.program])
  have hRAf : addCycleFrame sCP sRA :=
    finishAt_addCycleFrame 0 (by omega) (ao + acc.length) {sCP with pc := 0}
  have hra0 : sRA.tapes 0 = BitTape.shifted sum (ao + acc.length) :=
    Rewind.finishAt_shiftedEnd 0 (ao + acc.length) sum {sCP with pc := 0} hcp0
  have hra1 : sRA.tapes 1 = {BitTape.shifted xs xo with head := xo + sum.length} := by
    simpa [sRA, ra, Rewind.finishAt] using hcp1
  have hra2 : sRA.tapes 2 = {BitTape.blank with head := zo + sum.length} := by
    simpa [sRA, ra, Rewind.finishAt, sCP] using hcp2

  let rr := RewindOvershoot.finish 1 xo {sRA with pc := 0}
  let sRR : BitRAMState := {rr with pc := 70}
  have hrr := RewindOvershoot.shifted_steps 1 xo input tape xs sum.length hxs
    ((le_max_right _ _).trans hlen) {sRA with pc := 0} rfl hra1
  have hRR : PricedSteps (program.next input tape) (4 * sum.length + 6 + 1) sRA sRR :=
    call_at contains_rewind_right input tape sRA rr rfl hrr
      (by simp [rr, RewindOvershoot.finish, RewindOvershoot.program,
        BitRAM.link, RewindOvershoot.preamble, Rewind.program])
  have hRRf : addCycleFrame sRA sRR := finishAt_addCycleFrame 1 (by omega) xo {sRA with pc := 0}
  have hrr1 : sRR.tapes 1 = BitTape.shifted xs xo :=
    RewindOvershoot.finish_shifted 1 xo xs sum.length {sRA with pc := 0} hra1
  have hfooter : PricedSteps (program.next input tape) 1 sRR {sRR with pc := 2} := by
    apply executeInstructions_sound (instructions := 1)
    simp [executeInstructions, BitRAM.next, program, sRR, rippleAdder, RewindOvershoot.program,
      RewindOvershoot.preamble, BitRAM.link, Rewind.program, TapeOps.clear, TapeOps.copyClear,
      BitRAMInstruction.relocate]
  have hall := ((((((hA.trans hR0).trans hC).trans hR2).trans hCP).trans hRA).trans hRR).trans hfooter
  refine ⟨_, {sRR with pc := 2}, ?_, hall, rfl, ?_, hrr1, ?_,
    (((((hAf.trans hR0f).trans hCf).trans hR2f).trans hCPf).trans hRAf).trans hRRf⟩
  · have hm : max acc.length xs.length ≤ acc.length + xs.length := max_le (by omega) (by omega)
    omega
  · simpa [sRR, rr, RewindOvershoot.finish, Rewind.finishAt] using hra0
  · simpa [sRR, rr, RewindOvershoot.finish, Rewind.finishAt] using hra2

end Maxwell.Cost.HornerMultiply
