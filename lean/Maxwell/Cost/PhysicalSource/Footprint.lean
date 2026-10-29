import Maxwell.Cost.PhysicalSource.Overlay

namespace Maxwell.Cost.PhysicalSource.Overlay

def Outside {n : ℕ} (l : Layout n) (s t : BitRAMState) : Prop :=
  ∀ p, (∀ port, p<addressValue (l.bases port) ∨
    addressValue (l.bases port)+n*addressValue l.width≤p) → t.memory p=s.memory p

theorem Outside.refl {n : ℕ} (l : Layout n) (s : BitRAMState) : Outside l s s := fun _ _ => rfl

theorem Outside.trans {n : ℕ} {l : Layout n} {s t u : BitRAMState}
    (h : Outside l s t) (k : Outside l t u) : Outside l s u :=
  fun p hp => (k p hp).trans (h p hp)

theorem Outside.of_memory {n : ℕ} (l : Layout n) {s t : BitRAMState}
    (h : t.memory=s.memory) : Outside l s t := fun p _ => congrFun h p

theorem Outside.of_write {n : ℕ} (l : Layout n) (port : Fin 3) (i : Fin n) (v : ℕ)
    {s t : BitRAMState}
    (hm : t.memory=MemoryWord.writeBits s.memory
      (addressValue (l.bases port)+i.val*addressValue l.width)
      (FixedWidth.bits (addressValue l.width) v.bits)) : Outside l s t := by
  intro p hp
  rw [hm,MemoryWord.writeBits_outside]
  rcases hp port with h|h
  · left; omega
  · right
    rw [FixedWidth.bits_length]
    have hi := Nat.mul_le_mul_right (addressValue l.width) (show i.val+1≤n by omega)
    nlinarith only [h,hi]

/-- Any separately allocated read-only array survives source initialization
and scatter; the proof follows the exact writer's global memory footprint. -/
theorem Outside.preserve_array {n m : ℕ} (l : Layout n) {s t : BitRAMState}
    (h : Outside l s t) (base width : ℕ) (words : Vector (List Bool) m)
    (ha : BitArray.Represents s.memory base width words)
    (hsep : ∀ port, IncidenceEncoding.Separated base (m*width)
      (addressValue (l.bases port)) (n*addressValue l.width)) :
    BitArray.Represents t.memory base width words := by
  refine ⟨ha.length,?_⟩
  intro i j hj
  rw [h]
  · exact ha.bits i j hj
  · intro port
    have hi := Nat.mul_le_mul_right width (show i.val+1≤m by omega)
    rcases hsep port with hsep|hsep
    · left; nlinarith
    · right; omega

end Maxwell.Cost.PhysicalSource.Overlay
