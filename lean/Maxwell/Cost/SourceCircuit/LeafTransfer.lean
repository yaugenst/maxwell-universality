import Maxwell.Cost.SourceCircuit.ReadLeaf
import Maxwell.Cost.SourceCircuit.ScanBits

namespace Maxwell.Cost.SourceCircuit.LeafTransfer
open Structured

structure Data where
  remaining : List (List Bool)
  copied : List (List Bool)

def step (d : Data) : Data := ⟨d.remaining.tail,d.copied ++ [d.remaining.headD []]⟩

structure Ready (beforeAll suffix clock : List Bool) (d : Data) (s : Store) : Prop where
  source : s.val.tapes 98 = Increment.cursor (beforeAll ++ d.copied.flatten) (d.remaining.flatten ++ suffix) 0
  target : s.val.tapes 103 = BitTape.atEnd d.copied.flatten
  clock : BankArray.Word s.val 93 clock

structure Valid (width : ℕ) (leaves : List (List Bool)) (bits : List Bool) (d : Data) : Prop where
  count : d.remaining.length = bits.count true
  lengths : ∀ word ∈ d.remaining, word.length = width
  decomposition : d.copied ++ d.remaining = leaves

def work : Finset ℕ := {83,98,103}

structure Frame (s t : Store) : Prop where
  address : t.val.address = s.val.address
  memory : t.val.memory = s.val.memory
  inputHead : t.val.inputHead = s.val.inputHead
  randomCursor : t.val.randomCursor = s.val.randomCursor
  output : t.val.output = s.val.output
  sign : t.val.registers 23 = s.val.registers 23
  tapes : ∀ j, j ∉ work → t.val.tapes j = s.val.tapes j
  control : ∀ j, 32 ≤ j → t.val.registers j = s.val.registers j

theorem Frame.refl (s : Store) : Frame s s :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,fun _ _ => rfl,fun _ _ => rfl⟩

theorem Frame.trans {s t u : Store} (h : Frame s t) (k : Frame t u) : Frame s u :=
  ⟨k.address.trans h.address,k.memory.trans h.memory,k.inputHead.trans h.inputHead,
    k.randomCursor.trans h.randomCursor,k.output.trans h.output,k.sign.trans h.sign,
    fun j hj => (k.tapes j hj).trans (h.tapes j hj),
    fun j hj => (k.control j hj).trans (h.control j hj)⟩

theorem frame_passive {s t : Store} (h : ScanBits.Passive 83 s t) : Frame s t := by
  refine ⟨h.address,h.memory,h.inputHead,h.randomCursor,h.output,
    h.registers 23 (by omega) (by omega),?_,fun j hj => h.registers j (by omega) (by omega)⟩
  intro j hj
  exact h.tapes j (fun he => hj (by simp [work,he]))

theorem Ready.passive {beforeAll suffix clock : List Bool} {d : Data} {s t : Store}
    (h : Ready beforeAll suffix clock d s) (p : ScanBits.Passive 83 s t) : Ready beforeAll suffix clock d t :=
  ⟨(p.tapes 98 (by omega)).trans h.source,(p.tapes 103 (by omega)).trans h.target,
    BankArray.word_of_eq (p.tapes 93 (by omega)) h.clock⟩

theorem cursor_represents (beforeAll suffix : List Bool) :
    TapeRepresents (Increment.cursor beforeAll suffix 0) suffix := by
  intro k
  have hz : (0:ℤ) ≤ beforeAll.length + k := by omega
  have hn : ((beforeAll.length:ℤ)+k).toNat = beforeAll.length+k := by omega
  simp [Increment.cursor,BitTape.shifted,hz,hn,List.getElem?_append]

def scanCode : Code := ScanBits.code 83 ReadLeaf.code
def code : Code := .seq scanCode (.call (Rewind.program 83))

set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
theorem scan_executes (input : List Bool) (tape : ℕ → Bool)
    (width : ℕ) (bits beforeAll suffix clock : List Bool) (leaves : List (List Bool))
    (origin : ℤ) (s : Store) (hlen : clock.length = width)
    (hl : leaves.length = bits.count true) (hwords : ∀ word ∈ leaves, word.length = width)
    (hs : s.val.tapes 98 = Increment.cursor beforeAll (leaves.flatten ++ suffix) 0)
    (ht : s.val.tapes 103 = BitTape.blank) (hc : BankArray.Word s.val 93 clock)
    (hb : s.val.tapes 83 = BitTape.shifted bits origin) :
    ∃ cost t, cost ≤ bits.length*(14*width+18)+4 ∧ Executes input tape scanCode cost s t ∧
      t.val.tapes 98 = Increment.cursor (beforeAll ++ leaves.flatten) suffix 0 ∧
      t.val.tapes 103 = BitTape.atEnd leaves.flatten ∧
      t.val.tapes 83 = BitTape.shiftedEnd bits origin ∧ Frame s t := by
  let inv : List Bool → Data → Store → Prop := fun bits d t =>
    Ready beforeAll suffix clock d t ∧ Valid width leaves bits d ∧ Frame s t
  have stable : ∀ bits d u v, ScanBits.Passive 83 u v → inv bits d u → inv bits d v := by
    rintro bits d u v hp ⟨hr,hv,hf⟩
    exact ⟨hr.passive hp,hv,hf.trans (frame_passive hp)⟩
  have no : ∀ bits d u, inv (false::bits) d u → inv bits d u := by
    rintro bits d u ⟨hr,hv,hf⟩
    exact ⟨hr,⟨by simpa using hv.count,hv.lengths,hv.decomposition⟩,hf⟩
  have yes : ∀ bits d u, inv (true::bits) d u → ∃ cost t, cost ≤ 14*width+10 ∧
      Executes input tape ReadLeaf.code cost u t ∧ inv bits (step d) t ∧
      t.val.tapes 83 = u.val.tapes 83 := by
    rintro bits d u ⟨hr,hv,hf⟩
    cases he : d.remaining with
    | nil => have hh := hv.count; simp [he] at hh
    | cons word rest =>
      have hword : word.length = width := hv.lengths word (by simp [he])
      obtain ⟨co,hclock⟩ := hr.clock
      obtain ⟨t,et,t98,t103,_,tm,tf,tk,ta⟩ := ReadLeaf.executes input tape word
        (rest.flatten ++ suffix) d.copied.flatten clock co u (hlen.trans hword.symm) hclock
        (by rw [hr.source]; simpa [he,List.append_assoc] using
          (cursor_represents (beforeAll ++ d.copied.flatten) ((word::rest).flatten ++ suffix))) hr.target
      have ready : Ready beforeAll suffix clock (step d) t := by
        refine ⟨?_,?_,BankArray.word_of_eq (tk 93 (by omega) (by omega)) hr.clock⟩
        · simp only [t98,hr.source,step,he,List.tail_cons,List.headD_cons,List.flatten_cons,
            List.flatten_append]
          simp [Increment.cursor,BitTape.shifted,List.append_assoc,Nat.cast_add]
          omega
        · simpa [step,he] using t103
      have valid : Valid width leaves bits (step d) := by
        refine ⟨?_,?_,?_⟩
        · have hh := hv.count
          simpa [he,step] using hh
        · intro w hw
          apply hv.lengths w
          simpa [step,he] using List.mem_cons_of_mem word hw
        · simpa [step,he,List.append_assoc] using hv.decomposition
      have frame : Frame u t := by
        refine ⟨?_,tm,tf.inputHead,tf.randomCursor,tf.output,tf.sign,?_,
          fun j hj => tf.control j (by omega)⟩
        · -- Neither fixed-width copying nor the rewind changes the address word.
          exact ta
        · intro j hj
          exact tk j (fun he => hj (by simp [work,he])) (fun he => hj (by simp [work,he]))
      exact ⟨14*word.length+10,t,by omega,et,⟨ready,valid,hf.trans frame⟩,
        tk 83 (by omega) (by omega)⟩
  obtain ⟨cost,t,hcost,et,hi,hb'⟩ := ScanBits.executes 83 ReadLeaf.code step input tape inv
    (14*width+10) stable no yes bits [] origin ⟨leaves,[]⟩ s
    (by simpa [Increment.cursor,BitTape.shifted] using hb)
    ⟨⟨by simpa using hs,by simpa [BitTape.atEnd_nil] using ht,hc⟩,⟨hl,hwords,by simp⟩,Frame.refl s⟩
  have rem : (ScanBits.fold step bits ⟨leaves,[]⟩).remaining = [] := by
    have hh := hi.2.1.count
    simpa using hh
  have copied : (ScanBits.fold step bits ⟨leaves,[]⟩).copied = leaves := by
    simpa [rem] using hi.2.1.decomposition
  exact ⟨cost,t,hcost,et,by simpa [rem,copied] using hi.1.source,
    by simpa [copied] using hi.1.target,by simpa using hb',hi.2.2⟩

theorem executes (input : List Bool) (tape : ℕ → Bool)
    (width : ℕ) (bits beforeAll suffix clock : List Bool) (leaves : List (List Bool))
    (origin : ℤ) (s : Store) (hlen : clock.length = width)
    (hl : leaves.length = bits.count true) (hwords : ∀ word ∈ leaves, word.length = width)
    (hs : s.val.tapes 98 = Increment.cursor beforeAll (leaves.flatten ++ suffix) 0)
    (ht : s.val.tapes 103 = BitTape.blank) (hc : BankArray.Word s.val 93 clock)
    (hb : s.val.tapes 83 = BitTape.shifted bits origin) :
    ∃ cost t, cost ≤ bits.length*(14*width+22)+10 ∧ Executes input tape code cost s t ∧
      t.val.tapes 98 = Increment.cursor (beforeAll ++ leaves.flatten) suffix 0 ∧
      t.val.tapes 103 = BitTape.atEnd leaves.flatten ∧
      t.val.tapes 83 = BitTape.shifted bits origin ∧ Frame s t := by
  obtain ⟨cost,a,hcost,ea,a98,a103,a83,af⟩ := scan_executes input tape width bits beforeAll suffix
    clock leaves origin s hlen hl hwords hs ht hc hb
  have er := WordTransfer.rewind_shifted 83 origin input tape bits a.val a.property a83
  let t := Store.ofState (Rewind.finishAt 83 origin a.val)
  have eR : Executes input tape (.call (Rewind.program 83)) (4*bits.length+6) a t :=
    .call _ a _ _ er.1 (by simp [Rewind.program,Rewind.finishAt])
  have frame : Frame a t := by
    refine ⟨rfl,rfl,rfl,rfl,rfl,rfl,?_,?_⟩
    · intro j hj
      have hj83 : j ≠ 83 := fun he => hj (by simp [work,he])
      simp [t,Store.ofState,Rewind.finishAt,hj83]
    · intro j hj
      simp [t,Store.ofState,Rewind.finishAt,show j ≠ 24 by omega,show j ≠ 25 by omega]
  refine ⟨cost+(4*bits.length+6),t,?_,ea.seq eR,
    by simpa [t,Store.ofState,Rewind.finishAt] using a98,
    by simpa [t,Store.ofState,Rewind.finishAt] using a103,er.2,af.trans frame⟩
  nlinarith

end Maxwell.Cost.SourceCircuit.LeafTransfer
