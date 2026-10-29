import Maxwell.Cost.RealSimulation.TapeFrame
import Maxwell.Cost.RealSimulation.AddressAccess

namespace Maxwell.Cost.RealSimulation

open Control

theorem tapeLeft_instruction (input : RAMInput) (tape : ℕ → Bool)
    {L : Layout} {origin center : ℕ} {bits : List Bool} {source : BitRAMState}
    (s : Store) (h : Ready L origin center bits source s) (t : ℕ)
    (ht : t < L.tapeCount) (hh : -(center : ℤ) < (source.tapes t).head) :
    ∃ u, Executes input tape (instruction L Address.code (.tapeLeft t)) 4 s u ∧
      Ready L origin center bits
        (source.setTape t {source.tapes t with head := (source.tapes t).head - 1}) u := by
  have he := subtract_executes input tape s (L.tapeHead t) (L.tapeHead t) oneRegister
  rw [h.tape_heads t ht, h.one, ← centered_left center (source.tapes t).head hh] at he
  have hp := incrementPC_executes input tape _
    (h.put_tapeHead t ht ((source.tapes t).head - 1))
  exact ⟨_, he.seq hp.1, hp.2⟩

theorem tapeRight_instruction (input : RAMInput) (tape : ℕ → Bool)
    {L : Layout} {origin center : ℕ} {bits : List Bool} {source : BitRAMState}
    (s : Store) (h : Ready L origin center bits source s) (t : ℕ)
    (ht : t < L.tapeCount) (hh : -(center : ℤ) ≤ (source.tapes t).head) :
    ∃ u, Executes input tape (instruction L Address.code (.tapeRight t)) 4 s u ∧
      Ready L origin center bits
        (source.setTape t {source.tapes t with head := (source.tapes t).head + 1}) u := by
  have he := add_executes input tape s (L.tapeHead t) (L.tapeHead t) oneRegister
  rw [h.tape_heads t ht, h.one, ← centered_right center (source.tapes t).head hh] at he
  have hp := incrementPC_executes input tape _
    (h.put_tapeHead t ht ((source.tapes t).head + 1))
  exact ⟨_, he.seq hp.1, hp.2⟩

theorem eraseTape_instruction (input : RAMInput) (tape : ℕ → Bool)
    {L : Layout} {origin center : ℕ} {bits : List Bool} {source : BitRAMState}
    (s : Store) (h : Ready L origin center bits source s) (t : ℕ)
    (ht : t < L.tapeCount) (hh : -(center : ℤ) ≤ (source.tapes t).head) :
    ∃ u, Executes input tape (instruction L Address.code (.eraseTape t))
        (2 * L.stride + 9) s u ∧
      Ready L origin center bits (source.setTape t ((source.tapes t).write none)) u := by
  let p := L.slot origin (2 + t) (centered center (source.tapes t).head)
  let s0 := s.put pointerRegister p
  have e0 : Executes input tape (bankPointer L (2 + t) (L.tapeHead t))
      (2 * L.stride + 5) s s0 := by
    simpa only [h.origin_word, h.tape_heads t ht] using
      bankPointer_executes input tape L s (2 + t) (L.tapeHead t)
        (by unfold Layout.tapeHead pointerRegister; omega)
  have h0 : Ready L origin center bits source s0 := h.put_scratch _ _ (by decide)
    (by decide) (by decide) (by decide)
  have e1 : Executes input tape (save pointerRegister zeroRegister) 2 s0 (s0.put p 0) := by
    simpa only [show s0.val.indices pointerRegister = p by simp [s0], h0.zero] using
      save_executes input tape s0 pointerRegister zeroRegister
  have e2 := incrementPC_executes input tape _ (h0.put_tapeCell t ht none hh)
  refine ⟨_, ?_, e2.2⟩
  convert e0.seq (e1.seq e2.1) using 1
  rfl

theorem writeTape_instruction (input : RAMInput) (tape : ℕ → Bool)
    {L : Layout} {origin center : ℕ} {bits : List Bool} {source : BitRAMState}
    (s : Store) (h : Ready L origin center bits source s) (t src : ℕ)
    (ht : t < L.tapeCount) (hs : src < L.registerCount)
    (hh : -(center : ℤ) ≤ (source.tapes t).head) :
    ∃ u, Executes input tape (instruction L Address.code (.writeTape t src))
        (2 * L.stride + 11) s u ∧
      Ready L origin center bits
        (source.setTape t ((source.tapes t).write (some (source.registers src)))) u := by
  let b := source.registers src
  let s0 := s.put valueRegister (symbol (some b))
  have e0 : Executes input tape (add valueRegister (L.bitRegister src) oneRegister) 2 s s0 := by
    simpa only [s0, b, symbol_some, h.registers src hs, h.one] using
      add_executes input tape s valueRegister (L.bitRegister src) oneRegister
  have h0 : Ready L origin center bits source s0 := h.put_scratch _ _ (by decide)
    (by decide) (by decide) (by decide)
  let p := L.slot origin (2 + t) (centered center (source.tapes t).head)
  let s1 := s0.put pointerRegister p
  have e1 : Executes input tape (bankPointer L (2 + t) (L.tapeHead t))
      (2 * L.stride + 5) s0 s1 := by
    simpa only [h0.origin_word, h0.tape_heads t ht] using
      bankPointer_executes input tape L s0 (2 + t) (L.tapeHead t)
        (by unfold Layout.tapeHead pointerRegister; omega)
  have h1 : Ready L origin center bits source s1 := h0.put_scratch _ _ (by decide)
    (by decide) (by decide) (by decide)
  have e2 : Executes input tape (save pointerRegister valueRegister) 2 s1
      (s1.put p (symbol (some b))) := by
    simpa only [show s1.val.indices pointerRegister = p by simp [s1],
      show s1.val.indices valueRegister = symbol (some b) by
        simp [s1, s0, valueRegister, pointerRegister]] using
      save_executes input tape s1 pointerRegister valueRegister
  have e3 := incrementPC_executes input tape _ (h1.put_tapeCell t ht (some b) hh)
  refine ⟨_, ?_, e3.2⟩
  convert e0.seq (e1.seq (e2.seq e3.1)) using 1
  · rfl
  · omega

/-- The presence update comes last, including when both output registers coincide. -/
theorem readTape_instruction (input : RAMInput) (tape : ℕ → Bool)
    {L : Layout} {origin center : ℕ} {bits : List Bool} {source : BitRAMState}
    (s : Store) (h : Ready L origin center bits source s) (t dst present : ℕ)
    (ht : t < L.tapeCount) (hd : dst < L.registerCount) (hp : present < L.registerCount)
    (hh : -(center : ℤ) ≤ (source.tapes t).head) :
    ∃ u, Executes input tape (instruction L Address.code (.readTape t dst present))
        (2 * L.stride + 14) s u ∧
      Ready L origin center bits
        {source.setRegister dst ((source.tapes t).read.getD false) with
          registers := Function.update (Function.update source.registers dst
            ((source.tapes t).read.getD false)) present ((source.tapes t).read.isSome)} u := by
  let b := (source.tapes t).read
  let p := L.slot origin (2 + t) (centered center (source.tapes t).head)
  let s0 := s.put pointerRegister p
  have e0 : Executes input tape (bankPointer L (2 + t) (L.tapeHead t))
      (2 * L.stride + 5) s s0 := by
    simpa only [h.origin_word, h.tape_heads t ht] using
      bankPointer_executes input tape L s (2 + t) (L.tapeHead t)
        (by unfold Layout.tapeHead pointerRegister; omega)
  have h0 : Ready L origin center bits source s0 := h.put_scratch _ _ (by decide)
    (by decide) (by decide) (by decide)
  let s1 := s0.put valueRegister (symbol b)
  have e1 : Executes input tape (load valueRegister pointerRegister) 2 s0 s1 := by
    have hv : s0.val.indices p = symbol b := h0.tape_cells t ht (source.tapes t).head hh
    simpa only [show s0.val.indices pointerRegister = p by simp [s0],
      hv] using
      load_executes input tape s0 valueRegister pointerRegister
  have h1 : Ready L origin center bits source s1 := h0.put_scratch _ _ (by decide)
    (by decide) (by decide) (by decide)
  let s2 := s1.put (L.bitRegister dst) (b.getD false).toNat
  have e2 : Executes input tape (subtract (L.bitRegister dst) valueRegister oneRegister) 2 s1 s2 := by
    simpa only [show s1.val.indices valueRegister = symbol b by simp [s1],
      h1.one, symbol_getD] using
      subtract_executes input tape s1 (L.bitRegister dst) valueRegister oneRegister
  have h2 := h1.put_register dst (b.getD false) hd
  have hv : s2.val.indices valueRegister = symbol b := by
    have hn : valueRegister ≠ L.bitRegister dst := by unfold valueRegister Layout.bitRegister; omega
    simp [s2, s1, hn]
  have e3 : Executes input tape
      (.branch valueRegister zeroRegister (literal (L.bitRegister present) 0)
        (literal (L.bitRegister present) 1)) 3 s2
      (s2.put (L.bitRegister present) b.isSome.toNat) := by
    cases hb : b with
    | none =>
      have test : s2.val.indices valueRegister ≤ s2.val.indices zeroRegister := by
        rw [hv, h2.zero, hb]; rfl
      simpa only [hb, Option.isSome_none, Bool.toNat_false] using
        Executes.yes test (literal_executes input tape s2 (L.bitRegister present) 0)
    | some v =>
      have test : ¬ s2.val.indices valueRegister ≤ s2.val.indices zeroRegister := by
        rw [hv, h2.zero, hb]; simp
      simpa only [hb, Option.isSome_some, Bool.toNat_true] using
        Executes.no test (literal_executes input tape s2 (L.bitRegister present) 1)
  have e4 := incrementPC_executes input tape _ (h2.put_register present b.isSome hp)
  refine ⟨_, ?_, e4.2⟩
  convert e0.seq (e1.seq (e2.seq (e3.seq e4.1))) using 1
  rfl

end Maxwell.Cost.RealSimulation
