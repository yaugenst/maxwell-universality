import Maxwell.Cost.PhysicalMaterial.Dense

namespace Maxwell.Cost.PhysicalMaterial.Dense
open Structured RationalAccumulator

def filled {n : ℕ} (words : Vector (List Bool) n) (bits : List Bool) (k : ℕ) : Vector (List Bool) n :=
  Vector.ofFn fun i => if i.val < k then bits else words.get i

@[simp] theorem filled_get {n : ℕ} (words : Vector (List Bool) n) (bits : List Bool) (k : ℕ) (i : Fin n) :
    (filled words bits k).get i = if i.val < k then bits else words.get i := by simp [filled, Vector.get, Fin.cast]

@[simp] theorem filled_zero {n : ℕ} (words : Vector (List Bool) n) (bits : List Bool) :
    filled words bits 0 = words := by
  apply Vector.ext
  intro i hi
  simp [filled, Vector.get]

theorem filled_step {n : ℕ} (words : Vector (List Bool) n) (bits : List Bool) (i : Fin n) :
    (filled words bits i.val).set i bits = filled words bits (i.val+1) := by
  ext j
  simp only [Vector.get, Vector.getElem_set, filled, Vector.getElem_ofFn]
  split_ifs <;> simp_all <;> omega

@[simp] theorem filled_all {n : ℕ} (words : Vector (List Bool) n) (bits : List Bool) :
    filled words bits n = Vector.replicate n bits := by
  apply Vector.ext
  intro i hi
  simp [filled]

/-- The whole-array footprint permits independent descriptor/source archives
to survive all initialization and scatter writes. -/
def Outside {n : ℕ} (l : Layout n) (s t : BitRAMState) : Prop :=
  ∀ p, (p < addressValue l.numBase ∨ addressValue l.numBase+n*addressValue l.width ≤ p) →
    (p < addressValue l.denBase ∨ addressValue l.denBase+n*addressValue l.width ≤ p) →
    t.memory p = s.memory p

theorem Outside.refl {n : ℕ} (l : Layout n) (s : BitRAMState) : Outside l s s := fun _ _ _ => rfl

theorem Outside.trans {n : ℕ} {l : Layout n} {s t u : BitRAMState}
    (h : Outside l s t) (k : Outside l t u) : Outside l s u :=
  fun p hp hq => (k p hp hq).trans (h p hp hq)

theorem Outside.of_memory {n : ℕ} (l : Layout n) {s t : BitRAMState}
    (h : t.memory = s.memory) : Outside l s t := fun p _ _ => congrFun h p

theorem Outside.of_write {n : ℕ} (l : Layout n) (i : Fin n) (num den : ℕ) {s t : BitRAMState}
    (hm : t.memory = MemoryWord.writeBits
      (MemoryWord.writeBits s.memory (addressValue l.numBase+i.val*addressValue l.width)
        (FixedWidth.bits (addressValue l.width) num.bits))
      (addressValue l.denBase+i.val*addressValue l.width)
        (FixedWidth.bits (addressValue l.width) den.bits)) : Outside l s t := by
  intro p hp hq
  have outside (base : ℕ) (hx : p < base ∨ base+n*addressValue l.width ≤ p) (bits : List Bool)
      (hlen : bits.length = addressValue l.width) :
      p < base+i.val*addressValue l.width ∨ base+i.val*addressValue l.width+bits.length ≤ p := by
    rcases hx with hx | hx
    · left; omega
    · right
      have hi : (i.val+1)*addressValue l.width ≤ n*addressValue l.width :=
        Nat.mul_le_mul_right _ (by omega)
      rw [hlen]
      nlinarith only [hx, hi]
  rw [hm, MemoryWord.writeBits_outside _ _ _ _ (outside _ hq _ (FixedWidth.bits_length _ _)),
    MemoryWord.writeBits_outside _ _ _ _ (outside _ hp _ (FixedWidth.bits_length _ _))]

/-- Any actual memory supplies its old array contents; initialization never
requires a host-provided zero-filled array. -/
def snapshot (memory : ℕ → Bool) (base width n : ℕ) : Vector (List Bool) n :=
  Vector.ofFn fun i => MemoryWord.readBits memory (base+i.val*width) width

theorem snapshot_represents (memory : ℕ → Bool) (base width n : ℕ) :
    BitArray.Represents memory base width (snapshot memory base width n) := by
  refine ⟨?_, ?_⟩
  · intro i
    simp [snapshot, Vector.get]
  · intro i j hj
    simpa [snapshot, Vector.get, Fin.cast] using (MemoryWord.readBits_getElem memory (base+i.val*width) width j hj).symm

end Maxwell.Cost.PhysicalMaterial.Dense
