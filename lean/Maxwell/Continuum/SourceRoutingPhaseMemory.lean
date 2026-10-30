import Maxwell.Continuum.SourceRoutingPhaseLayout

namespace Maxwell.Cost.RoutingPorts.Complete.GeometryPhase

def MemoryFrame {q : ℕ} (p : Plan q) (before after : ℕ→Bool) : Prop :=
  ∀address,(∀slot : Fin 5,2 ≤ slot.val →
    address<p.base slot ∨ p.base slot+q*q*p.width ≤ address) → after address=before address

theorem MemoryFrame.refl {q : ℕ} (p : Plan q) (memory : ℕ→Bool) : MemoryFrame p memory memory := fun _ _ => rfl
theorem MemoryFrame.trans {q : ℕ} {p : Plan q} {a b c : ℕ→Bool}
    (h : MemoryFrame p a b) (k : MemoryFrame p b c) : MemoryFrame p a c :=
  fun address outside => (k address outside).trans (h address outside)
theorem MemoryFrame.of_eq {q : ℕ} (p : Plan q) {a b : ℕ→Bool} (h : b=a) : MemoryFrame p a b :=
  fun address _ => congrFun h address

theorem write_memoryFrame {q : ℕ} (p : Plan q) (slot : Fin 5) (hs : 2 ≤ slot.val)
    (index : Fin (q*q)) (value : ℕ) (memory : ℕ→Bool) :
    MemoryFrame p memory (MemoryWord.writeBits memory (p.base slot+index.val*p.width)
      (IncidenceEncoding.word p.width value)) := by
  intro address outside
  apply MemoryWord.writeBits_outside
  rw [IncidenceEncoding.word_length]
  have bound:=Nat.mul_le_mul_right p.width index.isLt
  rcases outside slot hs with before|after
  · left;omega
  · right
    simp only [Nat.succ_mul] at bound
    omega

#print axioms write_memoryFrame
end Maxwell.Cost.RoutingPorts.Complete.GeometryPhase
