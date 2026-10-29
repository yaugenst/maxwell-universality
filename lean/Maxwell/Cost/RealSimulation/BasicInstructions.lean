import Maxwell.Cost.RealSimulation.Compiler
import Maxwell.Cost.RealSimulation.Frame
import Maxwell.Cost.RealSimulation.Address

namespace Maxwell.Cost.RealSimulation

open Control

structure Ready (L : Layout) (origin center : ℕ) (bits : List Bool)
    (source : BitRAMState) (target : Store) : Prop extends
    Represents L origin center bits source target.val where
  zero : target.val.indices zeroRegister = 0
  one : target.val.indices oneRegister = 1
  active : target.val.indices activeRegister = 1

theorem Ready.put_pc {L : Layout} {origin center : ℕ} {bits : List Bool}
    {source : BitRAMState} {s : Store} (h : Ready L origin center bits source s) (pc : ℕ) :
    Ready L origin center bits {source with pc := pc} (s.put virtualPC pc) := by
  refine ⟨h.toRepresents.put_pc pc, ?_, ?_, ?_⟩
  · simpa [zeroRegister, virtualPC] using h.zero
  · simpa [oneRegister, virtualPC] using h.one
  · simpa [activeRegister, virtualPC] using h.active

theorem Ready.put_register {L : Layout} {origin center : ℕ} {bits : List Bool}
    {source : BitRAMState} {s : Store} (h : Ready L origin center bits source s)
    (r : ℕ) (b : Bool) (hr : r < L.registerCount) :
    Ready L origin center bits {source with registers := Function.update source.registers r b}
      (s.put (L.bitRegister r) b.toNat) := by
  have hn (j : ℕ) (hj : j < 256) : j ≠ L.bitRegister r := by
    unfold Layout.bitRegister
    omega
  refine ⟨h.toRepresents.put_register r b hr, ?_, ?_, ?_⟩
  · simpa [hn _ (by decide : zeroRegister < 256)] using h.zero
  · simpa [hn _ (by decide : oneRegister < 256)] using h.one
  · simpa [hn _ (by decide : activeRegister < 256)] using h.active

theorem Ready.put_scratch {L : Layout} {origin center : ℕ} {bits : List Bool}
    {source : BitRAMState} {s : Store} (h : Ready L origin center bits source s)
    (r v : ℕ) (hr : r < 20) (hz : zeroRegister ≠ r) (ho : oneRegister ≠ r)
    (ha : activeRegister ≠ r) : Ready L origin center bits source (s.put r v) := by
  refine ⟨h.toRepresents.put_scratch r v hr, ?_, ?_, ?_⟩
  · simpa [hz] using h.zero
  · simpa [ho] using h.one
  · simpa [ha] using h.active

theorem incrementPC_executes (input : RAMInput) (tape : ℕ → Bool)
    {L : Layout} {origin center : ℕ} {bits : List Bool} {source : BitRAMState}
    (s : Store) (h : Ready L origin center bits source s) :
    Executes input tape incrementPC 2 s (s.put virtualPC (source.pc + 1)) ∧
      Ready L origin center bits {source with pc := source.pc + 1}
        (s.put virtualPC (source.pc + 1)) := by
  constructor
  · simpa [incrementPC, h.pc, h.one] using
      add_executes input tape s virtualPC virtualPC oneRegister
  · exact h.put_pc _

theorem literal_instruction (input : RAMInput) (tape : ℕ → Bool)
    {L : Layout} {origin center : ℕ} {bits : List Bool} {source : BitRAMState}
    (s : Store) (h : Ready L origin center bits source s) (r : ℕ) (b : Bool)
    (hr : r < L.registerCount) :
    ∃ t, Executes input tape (instruction L Address.code (.literal r b)) 4 s t ∧
      Ready L origin center bits (source.setRegister r b) t := by
  let t := s.put (L.bitRegister r) b.toNat
  have ht := h.put_register r b hr
  have hp := incrementPC_executes input tape t ht
  refine ⟨_, (literal_executes input tape s (L.bitRegister r) b.toNat).seq hp.1, ?_⟩
  exact hp.2

theorem not_instruction (input : RAMInput) (tape : ℕ → Bool)
    {L : Layout} {origin center : ℕ} {bits : List Bool} {source : BitRAMState}
    (s : Store) (h : Ready L origin center bits source s) (dst src : ℕ)
    (hd : dst < L.registerCount) (hs : src < L.registerCount) :
    ∃ t, Executes input tape (instruction L Address.code (.bitNot dst src)) 4 s t ∧
      Ready L origin center bits (source.setRegister dst (!source.registers src)) t := by
  have hv : s.val.indices oneRegister - s.val.indices (L.bitRegister src) =
      (!source.registers src).toNat := by
    rw [h.one, h.registers src hs]
    cases source.registers src <;> rfl
  have he := subtract_executes input tape s (L.bitRegister dst) oneRegister (L.bitRegister src)
  rw [hv] at he
  have ht := h.put_register dst (!source.registers src) hd
  have hp := incrementPC_executes input tape _ ht
  exact ⟨_, he.seq hp.1, hp.2⟩

theorem and_instruction (input : RAMInput) (tape : ℕ → Bool)
    {L : Layout} {origin center : ℕ} {bits : List Bool} {source : BitRAMState}
    (s : Store) (h : Ready L origin center bits source s) (dst left right : ℕ)
    (hd : dst < L.registerCount) (hl : left < L.registerCount) (hr : right < L.registerCount) :
    ∃ t, Executes input tape (instruction L Address.code (.bitAnd dst left right)) 5 s t ∧
      Ready L origin center bits
        (source.setRegister dst (source.registers left && source.registers right)) t := by
  let b := source.registers left && source.registers right
  have he : Executes input tape
      (.branch (L.bitRegister left) zeroRegister (literal (L.bitRegister dst) 0)
        (copy (L.bitRegister dst) (L.bitRegister right))) 3 s
      (s.put (L.bitRegister dst) b.toNat) := by
    cases hb : source.registers left with
    | false =>
      have hc : s.val.indices (L.bitRegister left) ≤ s.val.indices zeroRegister := by
        simp [h.registers left hl, h.zero, hb]
      simpa [b, hb] using Executes.yes hc (literal_executes input tape s (L.bitRegister dst) 0)
    | true =>
      have hc : ¬ s.val.indices (L.bitRegister left) ≤ s.val.indices zeroRegister := by
        simp [h.registers left hl, h.zero, hb]
      simpa [b, hb, h.registers right hr] using
        Executes.no hc (copy_executes input tape s (L.bitRegister dst) (L.bitRegister right))
  have hp := incrementPC_executes input tape _ (h.put_register dst b hd)
  exact ⟨_, he.seq hp.1, hp.2⟩

theorem jump_instruction (input : RAMInput) (tape : ℕ → Bool)
    {L : Layout} {origin center : ℕ} {bits : List Bool} {source : BitRAMState}
    (s : Store) (h : Ready L origin center bits source s) (pc : ℕ) :
    ∃ t, Executes input tape (instruction L Address.code (.jump pc)) 2 s t ∧
      Ready L origin center bits {source with pc := pc} t := by
  exact ⟨_, literal_executes input tape s virtualPC pc, h.put_pc pc⟩

theorem branch_instruction (input : RAMInput) (tape : ℕ → Bool)
    {L : Layout} {origin center : ℕ} {bits : List Bool} {source : BitRAMState}
    (s : Store) (h : Ready L origin center bits source s) (r yes no : ℕ)
    (hr : r < L.registerCount) :
    ∃ t, Executes input tape (instruction L Address.code (.branch r yes no)) 3 s t ∧
      Ready L origin center bits
        {source with pc := if source.registers r then yes else no} t := by
  cases hb : source.registers r with
  | false =>
    have hc : s.val.indices (L.bitRegister r) ≤ s.val.indices zeroRegister := by
      simp [h.registers r hr, h.zero, hb]
    refine ⟨_, Executes.yes hc (literal_executes input tape s virtualPC no), ?_⟩
    simpa [hb] using h.put_pc no
  | true =>
    have hc : ¬ s.val.indices (L.bitRegister r) ≤ s.val.indices zeroRegister := by
      simp [h.registers r hr, h.zero, hb]
    refine ⟨_, Executes.no hc (literal_executes input tape s virtualPC yes), ?_⟩
    simpa [hb] using h.put_pc yes

end Maxwell.Cost.RealSimulation
