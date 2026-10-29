import Maxwell.Cost.SparseEmission.GateBinding
import Maxwell.Cost.BankArray.Increment

namespace Maxwell.Cost.SparseEmission
open Structured

def activeTapes : Finset ℕ := {97,110,111,112,113,114}

structure Frame (s t : BitRAMState) : Prop where
  address : t.address = s.address
  memory : t.memory = s.memory
  inputHead : t.inputHead = s.inputHead
  randomCursor : t.randomCursor = s.randomCursor
  output : t.output = s.output
  tapes : ∀ i, i ∉ activeTapes → t.tapes i = s.tapes i
  sign : t.registers 23 = s.registers 23
  control : ∀ i, 30 ≤ i → i ≠ 40 → i ≠ 41 → i ≠ 42 → i ≠ 43 → t.registers i = s.registers i

theorem Frame.refl (s : BitRAMState) : Frame s s := by constructor <;> intros <;> rfl
theorem Frame.trans {s t u : BitRAMState} (h : Frame s t) (k : Frame t u) : Frame s u :=
  ⟨k.address.trans h.address,k.memory.trans h.memory,k.inputHead.trans h.inputHead,
    k.randomCursor.trans h.randomCursor,k.output.trans h.output,
    fun i hi => (k.tapes i hi).trans (h.tapes i hi),k.sign.trans h.sign,
    fun i a b c d e => (k.control i a b c d e).trans (h.control i a b c d e)⟩

theorem Frame.of_reader {s t : BitRAMState} (h : ReadGate.Frame s t) : Frame s t :=
  ⟨h.address,h.memory,h.inputHead,h.randomCursor,h.output,
    fun i hi => h.tapes i (by simp_all [activeTapes]) (by simp_all [activeTapes])
      (by simp_all [activeTapes]),h.sign,h.control⟩

theorem Frame.of_emitter {changed : Finset ℕ} {s t : BitRAMState}
    (hc : changed ⊆ activeTapes) (h : SourceCircuit.Frame changed s t)
    (ha : t.address = s.address) (hm : t.memory = s.memory)
    (hk : ∀ i, i ∉ changed → t.tapes i = s.tapes i) : Frame s t :=
  ⟨ha,hm,h.inputHead,h.randomCursor,h.output,fun i hi => hk i (fun hmem => hi (hc hmem)),h.sign,
    fun i hi _ _ _ _ => h.control i hi⟩

def incrementCode : Code := BankArray.incrementCode 113

theorem increment_executes (input : List Bool) (randomTape : ℕ → Bool)
    (width id : ℕ) (origin : ℤ) (s : Store)
    (hroom : id+1 < 2^width)
    (hw : s.val.tapes 113 = BitTape.shifted (SourceCircuit.fixedWidth width id) origin) :
    ∃ cost t, cost ≤ 12*width+18 ∧ Executes input randomTape incrementCode cost s t ∧
      t.val.tapes 113 = BitTape.shifted (SourceCircuit.fixedWidth width (id+1)) origin ∧
      Frame s.val t.val ∧ (∀ i, i ≠ 113 → t.val.tapes i = s.val.tapes i) := by
  let bits := SourceCircuit.fixedWidth width id
  have hlen : bits.length = width := SourceCircuit.fixedWidth_length _ _
  have hvalue : addressValue bits = id := SourceCircuit.fixedWidth_value _ _ (by omega)
  have hbits : Increment.bits bits = SourceCircuit.fixedWidth width (id+1) :=
    SourceCircuit.fixedWidth_eq
      (by rw [SourceCircuit.increment_length bits (by rw [hvalue,hlen]; exact hroom),hlen])
      (by rw [Increment.bits_value,hvalue])
  obtain ⟨cost,u,hcost,eu,up,uw,uf⟩ := Increment.simulation 113 input randomTape bits origin s.val s.property hw
  let a := Store.ofState u
  have ea : Executes input randomTape (.call (Increment.program 113)) (cost+1) s a :=
    .call _ _ _ _ eu (by rw [up]; rfl)
  have hr := WordTransfer.rewind_shifted 113 origin input randomTape (Increment.bits bits) a.val a.property uw
  let t := Store.ofState (Rewind.finishAt 113 origin a.val)
  have et : Executes input randomTape (.call (Rewind.program 113)) (4*(Increment.bits bits).length+6) a t :=
    .call _ _ _ _ hr.1 rfl
  have rf : WordTransfer.Frame 113 113 a.val t.val := WordTransfer.frame_rewind 113 113 113 (Or.inl rfl) origin a.val
  have keep (i : ℕ) (hi : i ≠ 113) : t.val.tapes i = s.val.tapes i :=
    (rf.2.2.2.2.2.1 i hi hi).trans (uf.2.2.2.2.2.1 i hi)
  refine ⟨_,t,?_,ea.seq et,?_,?_,keep⟩
  · rw [hbits,SourceCircuit.fixedWidth_length]
    have := hcost
    rw [hlen] at this
    omega
  · simpa only [t,Store.ofState,hbits] using hr.2
  · refine ⟨rf.1.trans uf.1,rf.2.2.1.trans uf.2.2.1,rf.2.1.trans uf.2.1,
      rf.2.2.2.1.trans uf.2.2.2.1,rf.2.2.2.2.1.trans uf.2.2.2.2.1,
      fun i hi => keep i (by simp_all [activeTapes]),?_,?_⟩
    · exact (rf.2.2.2.2.2.2 23 (by omega) (by omega) (by omega) (by omega)).trans
        (uf.2.2.2.2.2.2 23 (by omega) (by omega) (by omega) (by omega))
    · intro i hi _ _ _ _
      exact (rf.2.2.2.2.2.2 i (by omega) (by omega) (by omega) (by omega)).trans
        (uf.2.2.2.2.2.2 i (by omega) (by omega) (by omega) (by omega))

end Maxwell.Cost.SparseEmission
