import Maxwell.Cost.SourceCircuit.HornerData
import Maxwell.Cost.SourceCircuit.ReverseBits

namespace Maxwell.Cost.SourceCircuit.HornerLoop
open Structured
open RationalAccumulator (Blank)

def work : Finset ℕ := insert 83 HornerStep.work

structure LoopFrame (s t : Store) : Prop where
  inputHead : t.val.inputHead = s.val.inputHead
  randomCursor : t.val.randomCursor = s.val.randomCursor
  output : t.val.output = s.val.output
  memory : t.val.memory = s.val.memory
  sign : t.val.registers 23 = s.val.registers 23
  tapes : ∀ j, (j = 4 ∨ 10 ≤ j) → j ∉ work → t.val.tapes j = s.val.tapes j
  control : ∀ j, 32 ≤ j → t.val.registers j = s.val.registers j

theorem LoopFrame.refl (s : Store) : LoopFrame s s :=
  ⟨rfl,rfl,rfl,rfl,rfl,fun _ _ _ => rfl,fun _ _ => rfl⟩

theorem LoopFrame.trans {s t u : Store} (h : LoopFrame s t) (k : LoopFrame t u) : LoopFrame s u :=
  ⟨k.inputHead.trans h.inputHead,k.randomCursor.trans h.randomCursor,k.output.trans h.output,
    k.memory.trans h.memory,k.sign.trans h.sign,
    fun j hj hn => (k.tapes j hj hn).trans (h.tapes j hj hn),
    fun j hj => (k.control j hj).trans (h.control j hj)⟩

theorem loopFrame_passive {s t : Store} (h : ScanBits.Passive 83 s t) : LoopFrame s t := by
  refine ⟨h.inputHead,h.randomCursor,h.output,h.memory,
    h.registers 23 (by omega) (by omega),?_,fun j hj => h.registers j (by omega) (by omega)⟩
  intro j _ hj
  exact h.tapes j (fun he => hj (by simp [work,he]))

theorem loopFrame_step {s t : Store} (h : Frame HornerStep.work s.val t.val)
    (hm : t.val.memory = s.val.memory) : LoopFrame s t := by
  refine ⟨h.inputHead,h.randomCursor,h.output,hm,h.sign,?_,fun j hj => h.control j (by omega)⟩
  intro j hj hn
  exact h.tapes j hj (fun hh => hn (Finset.mem_insert_of_mem hh))

theorem Ready.passive {clock : List Bool} {d : Data} {s t : Store}
    (h : Ready clock d s) (p : ScanBits.Passive 83 s t) : Ready clock d t :=
  ⟨scratch_of_tapes h.scratch (fun j hj => p.tapes j (by omega)),
    RationalAccumulator.blank_of_eq (p.tapes 96 (by omega)) h.blank96,
    RationalAccumulator.blank_of_eq (p.tapes 99 (by omega)) h.blank99,
    BankArray.word_of_eq (p.tapes 95 (by omega)) h.next,
    BankArray.word_of_eq (p.tapes 94 (by omega)) h.accumulator,
    (p.tapes 97 (by omega)).trans h.gates,(p.tapes 103 (by omega)).trans h.leaves,
    BankArray.word_of_eq (p.tapes 93 (by omega)) h.clock⟩

def code : Code := ReverseBits.code 83 HornerStep.code

set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
theorem executes (input : List Bool) (tape : ℕ → Bool) (width : ℕ)
    (clock bits : List Bool) (origin : ℤ) (d : Data) (s : Store)
    (hclock : clock.length = width) (hready : Ready clock d s)
    (hvalid : Valid width bits d) (hbits : s.val.tapes 83 = BitTape.shiftedEnd bits origin) :
    ∃ cost t, cost ≤ bits.length*(144*width+191)+8 ∧ Executes input tape code cost s t ∧
      Ready clock (bits.foldr step d) t ∧ Valid width [] (bits.foldr step d) ∧
      t.val.tapes 83 = BitTape.shifted bits origin ∧ LoopFrame s t := by
  let inv : List Bool → Data → Store → Prop := fun bits d t =>
    Ready clock d t ∧ Valid width bits d ∧ LoopFrame s t
  have stable : ∀ bits d u v, ScanBits.Passive 83 u v → inv bits d u → inv bits d v := by
    rintro bits d u v hp ⟨hr,hv,hf⟩
    exact ⟨hr.passive hp,hv,hf.trans (loopFrame_passive hp)⟩
  have body : ∀ bits bit d u, inv (bits ++ [bit]) d u → u.val.registers 30 = bit →
      u.val.registers 31 = true → ∃ cost t, cost ≤ 144*width+185 ∧
        Executes input tape HornerStep.code cost u t ∧ inv bits (step bit d) t ∧
        t.val.tapes 83 = u.val.tapes 83 := by
    rintro bits bit d u ⟨hr,hv,hf⟩ hb _
    cases bit with
    | false =>
      obtain ⟨cost,t,hcost,he,hn,ha,h96,hg,hm,hs,ht⟩ :=
        HornerStep.false_executes input tape d.next d.accumulator d.gates u hr.scratch
          hr.blank96 hr.next hr.accumulator hr.gates
          (hv.accumulatorLength.trans hv.nextLength.symm) hb
      have ready : Ready clock (step false d) t :=
        ⟨hs,h96,RationalAccumulator.blank_of_eq
            (ht.tapes 99 (by omega) (by simp [accumulatorWork])) hr.blank99,
          hn,ha,hg,(ht.tapes 103 (by omega) (by simp [accumulatorWork])).trans hr.leaves,
          BankArray.word_of_eq (ht.tapes 93 (by omega) (by simp [accumulatorWork])) hr.clock⟩
      have ht' : Frame HornerStep.work u.val t.val :=
        ht.mono (by simp [accumulatorWork,HornerStep.work])
      exact ⟨cost,t,by rw [hv.nextLength] at hcost; omega,he,
        ⟨ready,valid_step width bits false d hv,hf.trans (loopFrame_step ht' hm)⟩,
        ht.tapes 83 (by omega) (by simp [accumulatorWork])⟩
    | true =>
      obtain ⟨_,hlast,hdecomp⟩ := last_word hv
      have hl : u.val.tapes 103 =
          BitTape.atEnd (d.leaves.dropLast.flatten ++ d.leaves.getLastD []) := by
        rw [hr.leaves,← hdecomp,List.flatten_append]
        simp
      have room : addressValue d.next + 2 < 2 ^ d.next.length := by
        rw [hv.nextLength]
        have hh := hv.room
        simp at hh
        omega
      obtain ⟨cost,t,hcost,he,hn,ha,h96,h99,hl,hg,hm,hs,ht⟩ :=
        HornerStep.true_executes input tape d.next d.accumulator (d.leaves.getLastD [])
          d.gates d.leaves.dropLast.flatten clock u hr.scratch hr.blank96 hr.blank99
          hr.next hr.accumulator hr.gates hl hr.clock
          (hv.accumulatorLength.trans hv.nextLength.symm) (hlast.trans hv.nextLength.symm)
          (hclock.trans hv.nextLength.symm) room hb
      have ready : Ready clock (step true d) t :=
        ⟨hs,h96,h99,hn,ha,hg,hl,
          BankArray.word_of_eq (ht.tapes 93 (by omega) (by simp [HornerStep.work])) hr.clock⟩
      exact ⟨cost,t,by rwa [hv.nextLength] at hcost,he,
        ⟨ready,valid_step width bits true d hv,hf.trans (loopFrame_step ht hm)⟩,
        ht.tapes 83 (by omega) (by simp [HornerStep.work])⟩
  obtain ⟨cost,t,hcost,he,hi,hs⟩ := ReverseBits.executes_word 83 HornerStep.code step
    input tape inv (144*width+185) stable body bits origin d s hbits
    ⟨hready,hvalid,LoopFrame.refl s⟩
  exact ⟨cost,t,by simpa using hcost,he,hi.1,hi.2.1,hs,hi.2.2⟩

end Maxwell.Cost.SourceCircuit.HornerLoop
