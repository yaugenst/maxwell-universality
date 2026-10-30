import Maxwell.Continuum.SourceRoutingOperations

/-! The two routing arrays are the complete memory footprint of cursor
completion. Source archives and other allocated arrays survive the pass. -/

namespace Maxwell.Cost.RoutingPorts.Complete

def RoutingOutside {n : ℕ} (l : Layout n) (s t : BitRAMState) : Prop :=
  ∀a, (a<l.forward ∨ l.forward+n*n.bits.length≤a) →
    (a<l.backward ∨ l.backward+n*n.bits.length≤a) → t.memory a=s.memory a

theorem RoutingOutside.refl {n : ℕ} (l : Layout n) (s : BitRAMState) : RoutingOutside l s s :=
  fun _ _ _ => rfl

theorem RoutingOutside.trans {n : ℕ} {l : Layout n} {s t u : BitRAMState}
    (h : RoutingOutside l s t) (k : RoutingOutside l t u) : RoutingOutside l s u :=
  fun a ha hb => (k a ha hb).trans (h a ha hb)

theorem RoutingOutside.of_memory {n : ℕ} {l : Layout n} {s t : BitRAMState}
    (h : t.memory=s.memory) : RoutingOutside l s t := fun a _ _ => congrFun h a

theorem RoutingOutside.of_pair_write {n : ℕ} (l : Layout n) (i j : Fin n) {s t : BitRAMState}
    (hm : t.memory=MemoryWord.writeBits
      (MemoryWord.writeBits s.memory (l.forward+i.val*n.bits.length)
        (FixedWidth.bits n.bits.length j.val.bits))
      (l.backward+j.val*n.bits.length) (FixedWidth.bits n.bits.length i.val.bits)) :
    RoutingOutside l s t := by
  intro a ha hb
  have outside (base : ℕ) (k : Fin n) (hx : a<base ∨ base+n*n.bits.length≤a)
      (word : List Bool) (hl : word.length=n.bits.length) :
      a<base+k.val*n.bits.length ∨ base+k.val*n.bits.length+word.length≤a := by
    rcases hx with hx|hx
    · left
      omega
    · right
      have hk := Nat.mul_le_mul_right n.bits.length (show k.val+1≤n by omega)
      rw [hl]
      nlinarith only [hx,hk]
  rw [hm,MemoryWord.writeBits_outside _ _ _ _ (outside _ j hb _ (FixedWidth.bits_length _ _)),
    MemoryWord.writeBits_outside _ _ _ _ (outside _ i ha _ (FixedWidth.bits_length _ _))]

#print axioms RoutingOutside.of_pair_write

end Maxwell.Cost.RoutingPorts.Complete
