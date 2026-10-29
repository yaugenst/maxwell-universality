import Maxwell.Cost.RealSimulation.StackFrame
import Maxwell.Cost.RealSimulation.AddressAccess

namespace Maxwell.Cost.RealSimulation
open Control

theorem addressPop_instruction (input : RAMInput) (tape : ℕ → Bool)
    {L : Layout} {origin center : ℕ} {bits : List Bool} {source : BitRAMState}
    (s : Store) (h : Ready L origin center bits source s) :
    ∃ t, Executes input tape (instruction L Address.code .addressPop) 4 s t ∧
      Ready L origin center bits {source with pc := source.pc + 1, address := source.address.tail} t := by
  have e : Executes input tape (subtract addressLength addressLength oneRegister) 2 s
      (s.put addressLength (source.address.length - 1)) := by
    simpa only [h.address_length, h.one] using
      subtract_executes input tape s addressLength addressLength oneRegister
  have hp := incrementPC_executes input tape _ h.pop_address
  exact ⟨_, e.seq hp.1, hp.2⟩

theorem addressClear_instruction (input : RAMInput) (tape : ℕ → Bool)
    {L : Layout} {origin center : ℕ} {bits : List Bool} {source : BitRAMState}
    (s : Store) (h : Ready L origin center bits source s) :
    ∃ t, Executes input tape (instruction L Address.code .addressClear) 4 s t ∧
      Ready L origin center bits {source with pc := source.pc + 1, address := []} t := by
  have hp := incrementPC_executes input tape _ h.clear_address
  exact ⟨_, (literal_executes input tape s addressLength 0).seq hp.1, hp.2⟩

theorem addressIsEmpty_instruction (input : RAMInput) (tape : ℕ → Bool)
    {L : Layout} {origin center : ℕ} {bits : List Bool} {source : BitRAMState}
    (s : Store) (h : Ready L origin center bits source s) (dst : ℕ)
    (hd : dst < L.registerCount) :
    ∃ t, Executes input tape (instruction L Address.code (.addressIsEmpty dst)) 5 s t ∧
      Ready L origin center bits (source.setRegister dst source.address.isEmpty) t := by
  have e : Executes input tape
      (.branch addressLength zeroRegister (literal (L.bitRegister dst) 1)
        (literal (L.bitRegister dst) 0)) 3 s
      (s.put (L.bitRegister dst) source.address.isEmpty.toNat) := by
    cases ha : source.address with
    | nil =>
      have test : s.val.indices addressLength ≤ s.val.indices zeroRegister := by
        simp [h.address_length, h.zero, ha]
      simpa only [ha, List.isEmpty_nil, Bool.toNat_true] using
        Executes.yes test (literal_executes input tape s (L.bitRegister dst) 1)
    | cons b rest =>
      have test : ¬ s.val.indices addressLength ≤ s.val.indices zeroRegister := by
        simp [h.address_length, h.zero, ha]
      simpa only [ha, List.isEmpty_cons, Bool.toNat_false] using
        Executes.no test (literal_executes input tape s (L.bitRegister dst) 0)
  have hp := incrementPC_executes input tape _ (h.put_register dst source.address.isEmpty hd)
  exact ⟨_, e.seq hp.1, hp.2⟩

theorem addressPush_instruction (input : RAMInput) (tape : ℕ → Bool)
    {L : Layout} {origin center : ℕ} {bits : List Bool} {source : BitRAMState}
    (s : Store) (h : Ready L origin center bits source s) (src : ℕ)
    (hs : src < L.registerCount) :
    ∃ t, Executes input tape (instruction L Address.code (.addressPush src))
        (2 * L.stride + 11) s t ∧
      Ready L origin center bits
        {source with pc := source.pc + 1, address := source.registers src :: source.address} t := by
  let bankAddress := L.slot origin 1 source.address.length
  let p := s.put pointerRegister bankAddress
  have ep : Executes input tape (bankPointer L 1 addressLength) (2 * L.stride + 5) s p := by
    simpa only [h.origin_word, h.address_length] using
      bankPointer_executes input tape L s 1 addressLength (by decide)
  have hp : Ready L origin center bits source p := h.put_scratch _ _ (by decide)
    (by decide) (by decide) (by decide)
  let w := p.put bankAddress (source.registers src).toNat
  have ew : Executes input tape (save pointerRegister (L.bitRegister src)) 2 p w := by
    simpa only [show p.val.indices pointerRegister = bankAddress by simp [p], hp.registers src hs] using
      save_executes input tape p pointerRegister (L.bitRegister src)
  have hat : 256 ≤ bankAddress := by
    have := h.origin_above_frame
    have := L.slot_ge_origin origin 1 source.address.length
    unfold Layout.frameEnd at *
    omega
  have el : Executes input tape (add addressLength addressLength oneRegister) 2 w
      (w.put addressLength (source.address.length + 1)) := by
    simpa only [w, Store.put_indices, show addressLength ≠ bankAddress by unfold addressLength; omega,
      show oneRegister ≠ bankAddress by unfold oneRegister; omega, ↓reduceIte,
      hp.address_length, hp.one] using add_executes input tape w addressLength addressLength oneRegister
  have hpush : Ready L origin center bits {source with address := source.registers src :: source.address}
      (w.put addressLength (source.address.length + 1)) := hp.push_address (source.registers src)
  have efinish := incrementPC_executes input tape _ hpush
  refine ⟨_, ?_, efinish.2⟩
  have e := ep.seq (ew.seq (el.seq efinish.1))
  convert e using 1
  rfl

theorem addressPeek_instruction (input : RAMInput) (tape : ℕ → Bool)
    {L : Layout} {origin center : ℕ} {bits : List Bool} {source : BitRAMState}
    (s : Store) (h : Ready L origin center bits source s) (dst : ℕ)
    (hd : dst < L.registerCount) :
    ∃ cost t, cost ≤ 2 * L.stride + 30 ∧
      Executes input tape (instruction L Address.code (.addressPeek dst)) cost s t ∧
      Ready L origin center bits (source.setRegister dst (source.address.headD false)) t := by
  by_cases ha : source.address = []
  · have test : s.val.indices addressLength ≤ s.val.indices zeroRegister := by
      simp [h.address_length, h.zero, ha]
    have e : Executes input tape
        (.branch addressLength zeroRegister (literal (L.bitRegister dst) 0)
          (sequence [subtract coordinateRegister addressLength oneRegister,
            bankPointer L 1 coordinateRegister, load (L.bitRegister dst) pointerRegister])) 3 s
        (s.put (L.bitRegister dst) (source.address.headD false).toNat) := by
      simpa [ha] using Executes.yes test (literal_executes input tape s (L.bitRegister dst) 0)
    have hp := incrementPC_executes input tape _ (h.put_register dst (source.address.headD false) hd)
    exact ⟨5, _, by omega, e.seq hp.1, hp.2⟩
  · have hlen : 0 < source.address.length := List.length_pos_iff.mpr ha
    let c := s.put coordinateRegister (source.address.length - 1)
    have ec : Executes input tape (subtract coordinateRegister addressLength oneRegister) 2 s c := by
      simpa only [h.address_length, h.one] using
        subtract_executes input tape s coordinateRegister addressLength oneRegister
    have hc : Ready L origin center bits source c := h.put_scratch _ _ (by decide)
      (by decide) (by decide) (by decide)
    let bankAddress := L.slot origin 1 (source.address.length - 1)
    let p := c.put pointerRegister bankAddress
    have ep : Executes input tape (bankPointer L 1 coordinateRegister) (2 * L.stride + 5) c p := by
      simpa only [hc.origin_word, show c.val.indices coordinateRegister = source.address.length - 1 by simp [c]] using
        bankPointer_executes input tape L c 1 coordinateRegister (by decide)
    have hp : Ready L origin center bits source p := hc.put_scratch _ _ (by decide)
      (by decide) (by decide) (by decide)
    have top : p.val.indices bankAddress = (source.address.headD false).toNat := by
      have ht := hp.stack_cells (source.address.length - 1) (by omega)
      rw [reverse_top source.address ha] at ht
      exact ht
    have el : Executes input tape (load (L.bitRegister dst) pointerRegister) 2 p
        (p.put (L.bitRegister dst) (source.address.headD false).toNat) := by
      simpa only [show p.val.indices pointerRegister = bankAddress by simp [p], top] using
        load_executes input tape p (L.bitRegister dst) pointerRegister
    have efinish := incrementPC_executes input tape _ (hp.put_register dst (source.address.headD false) hd)
    have test : ¬ s.val.indices addressLength ≤ s.val.indices zeroRegister := by
      rw [h.address_length, h.zero]
      omega
    have ebranch : Executes input tape
        (.branch addressLength zeroRegister (literal (L.bitRegister dst) 0)
          (sequence [subtract coordinateRegister addressLength oneRegister,
            bankPointer L 1 coordinateRegister, load (L.bitRegister dst) pointerRegister]))
        (1 + (2 + (2 * L.stride + 5 + 2))) s
        (p.put (L.bitRegister dst) (source.address.headD false).toNat) :=
      Executes.no test (ec.seq (ep.seq el))
    refine ⟨2 * L.stride + 12, _, by omega, ?_, efinish.2⟩
    convert ebranch.seq efinish.1 using 1
    · rfl
    · omega

end Maxwell.Cost.RealSimulation
