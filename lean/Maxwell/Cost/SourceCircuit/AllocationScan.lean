import Maxwell.Cost.SourceCircuit.Occurrence
import Maxwell.Cost.SourceCircuit.ScanBits

namespace Maxwell.Cost.SourceCircuit
open Structured
open RationalAccumulator (Blank)

structure AllocationData (n : ℕ) where
  roots : Vector (List Bool) n
  next : List Bool
  gates : List Bool
  leaves : List Bool
  memory : ℕ → Bool

def AllocationData.split {n : ℕ} (base width : ℕ) (i : Fin n) (d : AllocationData n) : AllocationData n where
  roots := d.roots.set i (Increment.bits d.next)
  next := Increment.bits (Increment.bits d.next)
  gates := d.gates ++ copyTag ++ d.roots.get i ++ copyTag ++ d.roots.get i
  leaves := d.leaves ++ d.next
  memory := MemoryWord.writeBits d.memory (base+i.val*width) (Increment.bits d.next)

structure AllocationReady {n : ℕ} (width index base clock : List Bool)
    (d : AllocationData n) (s : Store) : Prop where
  scratch : BankArray.Scratch s.val
  blank7 : Blank s.val 7
  blank94 : Blank s.val 94
  blank96 : Blank s.val 96
  width : BankArray.Word s.val 90 width
  index : BankArray.Word s.val 91 index
  base : BankArray.Word s.val 92 base
  clock : BankArray.Word s.val 93 clock
  next : BankArray.Word s.val 95 d.next
  gates : s.val.tapes 97 = BitTape.atEnd d.gates
  leaves : s.val.tapes 98 = BitTape.atEnd d.leaves
  memory : s.val.memory = d.memory

structure AllocationValid {n : ℕ} (base width : ℕ) (bits : List Bool)
    (d : AllocationData n) : Prop where
  array : BitArray.Represents d.memory base width d.roots
  length : d.next.length = width
  room : addressValue d.next + 2 * bits.count true < 2 ^ width

def allocationScanWork : Finset ℕ := {83,94,95,96,97,98}

structure ScanFrame (s t : Store) : Prop where
  inputHead : t.val.inputHead = s.val.inputHead
  randomCursor : t.val.randomCursor = s.val.randomCursor
  output : t.val.output = s.val.output
  sign : t.val.registers 23 = s.val.registers 23
  tapes : ∀ j, (j = 4 ∨ 10 ≤ j) → j ∉ allocationScanWork → t.val.tapes j = s.val.tapes j

theorem ScanFrame.refl (s : Store) : ScanFrame s s := ⟨rfl,rfl,rfl,rfl,fun _ _ _ => rfl⟩

theorem ScanFrame.trans {s t u : Store} (h : ScanFrame s t) (k : ScanFrame t u) : ScanFrame s u :=
  ⟨k.inputHead.trans h.inputHead,k.randomCursor.trans h.randomCursor,k.output.trans h.output,
    k.sign.trans h.sign,fun j hj hn => (k.tapes j hj hn).trans (h.tapes j hj hn)⟩

theorem scanFrame_passive {s t : Store} (h : ScanBits.Passive 83 s t) : ScanFrame s t := by
  refine ⟨h.inputHead,h.randomCursor,h.output,h.registers 23 (by omega) (by omega),?_⟩
  intro j _ hj
  have hj83 : j ≠ 83 := by intro he; exact hj (by simp [allocationScanWork,he])
  exact h.tapes j hj83

theorem scanFrame_occurrence {s t : Store} (h : Frame occurrenceWork s.val t.val) : ScanFrame s t := by
  refine ⟨h.inputHead,h.randomCursor,h.output,h.sign,?_⟩
  intro j hj hn
  exact h.tapes j hj (fun hh => hn (by
    simp only [occurrenceWork,Finset.mem_insert,Finset.mem_singleton] at hh
    simp only [allocationScanWork,Finset.mem_insert,Finset.mem_singleton]
    exact Or.inr hh))

theorem AllocationReady.passive {n : ℕ} {width index base clock : List Bool}
    {d : AllocationData n} {s t : Store} (h : AllocationReady width index base clock d s)
    (p : ScanBits.Passive 83 s t) : AllocationReady width index base clock d t := by
  refine ⟨scratch_of_tapes h.scratch (fun j hj => p.tapes j (by omega)),
    RationalAccumulator.blank_of_eq (p.tapes 7 (by omega)) h.blank7,
    RationalAccumulator.blank_of_eq (p.tapes 94 (by omega)) h.blank94,
    RationalAccumulator.blank_of_eq (p.tapes 96 (by omega)) h.blank96,
    BankArray.word_of_eq (p.tapes 90 (by omega)) h.width,
    BankArray.word_of_eq (p.tapes 91 (by omega)) h.index,
    BankArray.word_of_eq (p.tapes 92 (by omega)) h.base,
    BankArray.word_of_eq (p.tapes 93 (by omega)) h.clock,
    BankArray.word_of_eq (p.tapes 95 (by omega)) h.next,
    (p.tapes 97 (by omega)).trans h.gates,(p.tapes 98 (by omega)).trans h.leaves,
    p.memory.trans h.memory⟩

def allocationScanCode : Code := ScanBits.code 83 occurrenceCode

set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
theorem allocationScan_executes {n : ℕ} (input : List Bool) (tape : ℕ → Bool)
    (width index base clock : List Bool) (i : Fin n)
    (hwidth : 0 < width.length) (hindex : addressValue index = i.val)
    (hclock : clock.length = addressValue width)
    (bits : List Bool) (origin : ℤ) (d : AllocationData n) (s : Store)
    (hready : AllocationReady width index base clock d s)
    (hvalid : AllocationValid (addressValue base) (addressValue width) bits d)
    (hbits : s.val.tapes 83 = BitTape.shifted bits origin) :
    ∃ cost, ∃ t : Store, cost ≤ bits.length*(occurrenceCost width index base clock+8)+4 ∧
      Executes input tape allocationScanCode cost s t ∧
      AllocationReady width index base clock
        (ScanBits.fold (AllocationData.split (addressValue base) (addressValue width) i) bits d) t ∧
      AllocationValid (addressValue base) (addressValue width) []
        (ScanBits.fold (AllocationData.split (addressValue base) (addressValue width) i) bits d) ∧
      t.val.tapes 83 = BitTape.shiftedEnd bits origin ∧ ScanFrame s t := by
  let step := AllocationData.split (addressValue base) (addressValue width) i
  let inv : List Bool → AllocationData n → Store → Prop := fun bits d t => AllocationReady width index base clock d t ∧
    AllocationValid (addressValue base) (addressValue width) bits d ∧ ScanFrame s t
  have stable : ∀ bits d u v, ScanBits.Passive 83 u v → inv bits d u → inv bits d v := by
    rintro bits d u v hp ⟨hr,hv,hf⟩
    exact ⟨hr.passive hp,hv,hf.trans (scanFrame_passive hp)⟩
  have hfalse : ∀ bits d u, inv (false::bits) d u → inv bits d u := by
    rintro bits d u ⟨hr,hv,hf⟩
    refine ⟨hr,⟨hv.array,hv.length,?_⟩,hf⟩
    simpa using hv.room
  have hbody : ∀ bits d u, inv (true::bits) d u →
      ∃ cost t, cost ≤ occurrenceCost width index base clock ∧
        Executes input tape occurrenceCode cost u t ∧ inv bits (step d) t ∧
        t.val.tapes 83 = u.val.tapes 83 := by
    rintro bits d u ⟨hr,hv,hf⟩
    have room : addressValue d.next + 2 < 2 ^ d.next.length := by
      rw [hv.length]
      have hh := hv.room
      simp only [List.count_cons_self] at hh
      omega
    obtain ⟨cost,t,hcost,he,hn,h94,h96,h7,h97,h98,hm,ha,hs,ht,hlen⟩ :=
      occurrence_executes input tape width index base clock d.next d.gates d.leaves d.roots i
        hwidth hindex hclock hv.length room u hr.scratch hr.blank7 hr.blank94 hr.blank96
        hr.width hr.index hr.base hr.clock hr.next hr.gates hr.leaves
        (by simpa [hr.memory] using hv.array)
    have memory : t.val.memory = (step d).memory := by
      simpa [step,AllocationData.split,hr.memory] using hm
    have ready : AllocationReady width index base clock (step d) t :=
      ⟨hs,h7,h94,h96,
        BankArray.word_of_eq (ht.tapes 90 (by omega) (by simp [occurrenceWork])) hr.width,
        BankArray.word_of_eq (ht.tapes 91 (by omega) (by simp [occurrenceWork])) hr.index,
        BankArray.word_of_eq (ht.tapes 92 (by omega) (by simp [occurrenceWork])) hr.base,
        BankArray.word_of_eq (ht.tapes 93 (by omega) (by simp [occurrenceWork])) hr.clock,
        hn,h97,h98,memory⟩
    have valid : AllocationValid (addressValue base) (addressValue width) bits (step d) := by
      refine ⟨?_,hlen,?_⟩
      · rw [memory] at ha
        exact ha
      · change addressValue (Increment.bits (Increment.bits d.next)) + 2 * bits.count true < _
        rw [Increment.bits_value,Increment.bits_value]
        have hh := hv.room
        simp only [List.count_cons_self] at hh
        omega
    exact ⟨cost,t,hcost,he,⟨ready,valid,hf.trans (scanFrame_occurrence ht)⟩,
      ht.tapes 83 (by omega) (by simp [occurrenceWork])⟩
  obtain ⟨cost,t,hcost,he,hi,hs⟩ := ScanBits.executes 83 occurrenceCode step input tape inv
    (occurrenceCost width index base clock) stable hfalse hbody bits [] origin d s
    (by simpa [Increment.cursor,BitTape.shifted] using hbits) ⟨hready,hvalid,ScanFrame.refl s⟩
  exact ⟨cost,t,hcost,he,hi.1,hi.2.1,by simpa using hs,hi.2.2⟩

end Maxwell.Cost.SourceCircuit
