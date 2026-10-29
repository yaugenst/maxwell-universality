import Maxwell.Cost.DoublingPass
import Maxwell.Cost.DoublingPass.MemoryFrame
import Maxwell.Cost.BankArray.WriteCanonical

namespace Maxwell.Cost.BitArray

/-- Every finite memory interval has an exact saved-word view. This is only
a specification for the existing bits, not a runtime memory-reading oracle. -/
def snapshot (memory : ℕ → Bool) (base width n : ℕ) : Vector (List Bool) n :=
  Vector.ofFn (fun i => MemoryWord.readBits memory (base+i.val*width) width)

@[simp] theorem snapshot_get (memory : ℕ → Bool) (base width n : ℕ) (i : Fin n) :
    (snapshot memory base width n).get i = MemoryWord.readBits memory (base+i.val*width) width := by
  simp [snapshot,Vector.get,Fin.cast]

theorem snapshot_represents (memory : ℕ → Bool) (base width n : ℕ) :
    Represents memory base width (snapshot memory base width n) where
  length i := by simp only [snapshot_get,MemoryWord.readBits_length]
  bits i j hj := by
    simp only [snapshot_get]
    exact (MemoryWord.readBits_getElem memory _ width j hj).symm

theorem read_write_slot {n : ℕ} (memory : ℕ → Bool) (base width : ℕ) (i j : Fin n)
    (word : List Bool) (hword : word.length = width) :
    MemoryWord.readBits (MemoryWord.writeBits memory (base+i.val*width) word) (base+j.val*width) width =
      if i=j then word else MemoryWord.readBits memory (base+j.val*width) width := by
  have h := ((snapshot_represents memory base width n).write i word hword).read j
  simpa only [Maxwell.Logical.Routing.DummyFill.get_set,snapshot_get] using h

end Maxwell.Cost.BitArray

namespace Maxwell.Cost.DoublingInit
open Maxwell.Logical.Routing
open DoublingPass (State)

structure Layout where
  route : DoublingPass.Layout
  inputA : ℕ
  inputB : ℕ

def Layout.base (layout : Layout) (i : Fin 6) : ℕ :=
  match i.val with
  | 0 => layout.inputA
  | 1 => layout.inputB
  | 2 => layout.route.oldJump
  | 3 => layout.route.oldMinimum
  | 4 => layout.route.newJump
  | _ => layout.route.newMinimum

def Layout.Separated (layout : Layout) (n : ℕ) : Prop :=
  ∀ i j : Fin 6, i ≠ j → IncidenceEncoding.Separated
    (layout.base i) (n*layout.route.width) (layout.base j) (n*layout.route.width)

theorem Layout.Separated.pingPong {layout : Layout} {n : ℕ} (h : layout.Separated n) :
    layout.route.PingPong n := by
  exact ⟨⟨h 2 4 (by decide),h 2 5 (by decide),h 3 4 (by decide),h 3 5 (by decide),h 4 5 (by decide)⟩,
    ⟨h 4 2 (by decide),h 4 3 (by decide),h 5 2 (by decide),h 5 3 (by decide),h 2 3 (by decide)⟩⟩

def identity {n : ℕ} : Vector (Fin n) n := Vector.ofFn id
@[simp] theorem identity_get {n : ℕ} (i : Fin n) : identity.get i = i := by simp [identity,Vector.get,Fin.cast]

def permutation {n : ℕ} (p : Equiv.Perm (Fin n)) : Vector (Fin n) n := Vector.ofFn p
@[simp] theorem permutation_get {n : ℕ} (p : Equiv.Perm (Fin n)) (i : Fin n) :
    (permutation p).get i = p i := by simp [permutation,Vector.get,Fin.cast]

/-- The output buffers contain valid identity labels, including the empty case. -/
def initialOutput (n : ℕ) : State n := ⟨identity,identity⟩

def Prefix {n : ℕ} (memory : ℕ → Bool) (base width : ℕ) (values : Vector (Fin n) n) (limit : ℕ) : Prop :=
  ∀ i : Fin n, i.val < limit → MemoryWord.readBits memory (base+i.val*width) width =
    IncidenceEncoding.word width (values.get i).val

theorem Prefix.zero {n : ℕ} (memory : ℕ → Bool) (base width : ℕ) (values : Vector (Fin n) n) :
    Prefix memory base width values 0 := by intro i hi; omega

theorem Prefix.complete {n : ℕ} {memory : ℕ → Bool} {base width : ℕ} {values : Vector (Fin n) n}
    (h : Prefix memory base width values n) : BitArray.Represents memory base width (DoublingPass.words width values) := by
  have he : BitArray.snapshot memory base width n = DoublingPass.words width values := by
    apply Vector.ext
    intro i hi
    have hh := h ⟨i,hi⟩ hi
    change (BitArray.snapshot memory base width n).get ⟨i,hi⟩ = (DoublingPass.words width values).get ⟨i,hi⟩
    simpa only [BitArray.snapshot_get,DoublingPass.words_get] using hh
  rw [← he]
  exact BitArray.snapshot_represents _ _ _ _

theorem Prefix.write_same {n : ℕ} {memory : ℕ → Bool} {base width : ℕ} {values : Vector (Fin n) n}
    {limit : ℕ} (h : Prefix memory base width values limit) (hlt : limit < n) :
    Prefix (MemoryWord.writeBits memory (base+limit*width)
      (IncidenceEncoding.word width (values.get ⟨limit,hlt⟩).val)) base width values (limit+1) := by
  intro i hi
  rw [BitArray.read_write_slot memory base width ⟨limit,hlt⟩ i _ (by simp)]
  split_ifs with he
  · subst i; rfl
  · have hne : i.val ≠ limit := fun hval => he (Fin.ext hval.symm)
    exact h i (by omega)

theorem Prefix.write_other {n : ℕ} {memory : ℕ → Bool} {base width other : ℕ}
    {values : Vector (Fin n) n} {limit : ℕ} (h : Prefix memory base width values limit)
    (hs : IncidenceEncoding.Separated base (n*width) other (n*width)) (i : Fin n)
    (word : List Bool) (hword : word.length = width) :
    Prefix (MemoryWord.writeBits memory (other+i.val*width) word) base width values limit := by
  have rep := IncidenceEncoding.represents_write_disjoint (BitArray.snapshot_represents memory base width n)
    other width i word hword hs
  intro j hj
  have he := rep.read j
  rw [BitArray.snapshot_get] at he
  exact he.trans (h j hj)

structure Represents {n : ℕ} (layout : Layout) (memory : ℕ → Bool)
    (a b : Equiv.Perm (Fin n)) (limit : ℕ) : Prop where
  inputA : BitArray.Represents memory layout.inputA layout.route.width (DoublingPass.words layout.route.width (permutation a))
  inputB : BitArray.Represents memory layout.inputB layout.route.width (DoublingPass.words layout.route.width (permutation b))
  jump : Prefix memory layout.route.oldJump layout.route.width (permutation (a*b)) limit
  minimum : Prefix memory layout.route.oldMinimum layout.route.width (identity (n := n)) limit
  newJump : Prefix memory layout.route.newJump layout.route.width (identity (n := n)) limit
  newMinimum : Prefix memory layout.route.newMinimum layout.route.width (identity (n := n)) limit

theorem Represents.complete {n : ℕ} {layout : Layout} {memory : ℕ → Bool} {a b : Equiv.Perm (Fin n)}
    (h : Represents layout memory a b n) : DoublingPass.Represents layout.route memory
      (Doubling.initial (Equiv.refl (Fin n)) (a*b)) (initialOutput n) :=
  ⟨h.jump.complete,h.minimum.complete,h.newJump.complete,h.newMinimum.complete⟩

def stepMemory {n : ℕ} (layout : Layout) (a b : Equiv.Perm (Fin n)) (i : Fin n) (memory : ℕ → Bool) : ℕ → Bool :=
  let m1 := MemoryWord.writeBits memory (layout.route.oldJump+i.val*layout.route.width)
    (IncidenceEncoding.word layout.route.width (a (b i)).val)
  let word := IncidenceEncoding.word layout.route.width i.val
  let m2 := MemoryWord.writeBits m1 (layout.route.oldMinimum+i.val*layout.route.width) word
  let m3 := MemoryWord.writeBits m2 (layout.route.newJump+i.val*layout.route.width) word
  MemoryWord.writeBits m3 (layout.route.newMinimum+i.val*layout.route.width) word

/-- The four initialization writes preserve every bit outside the routing
arrays, irrespective of those arrays' previous contents. -/
theorem stepMemory_frame {n : ℕ} (layout : Layout) (a b : Equiv.Perm (Fin n))
    (i : Fin n) (memory : ℕ → Bool) :
    DoublingPass.MemoryFrame layout.route n memory (stepMemory layout a b i memory) := by
  intro address ha
  have outside_slot (base : ℕ)
      (h : address < base ∨ base + n * layout.route.width ≤ address) :
      address < base + i.val * layout.route.width ∨
        base + i.val * layout.route.width + layout.route.width ≤ address := by
    have hi := Nat.mul_le_mul_right layout.route.width (show i.val + 1 ≤ n by omega)
    rcases h with h | h
    · left
      omega
    · right
      simpa only [Nat.add_mul, Nat.one_mul, Nat.add_assoc] using
        (Nat.add_le_add_left hi base).trans h
  unfold stepMemory
  rw [MemoryWord.writeBits_outside, MemoryWord.writeBits_outside,
    MemoryWord.writeBits_outside, MemoryWord.writeBits_outside]
  · simpa only [IncidenceEncoding.word_length] using outside_slot _ ha.1
  · simpa only [IncidenceEncoding.word_length] using outside_slot _ ha.2.1
  · simpa only [IncidenceEncoding.word_length] using outside_slot _ ha.2.2.1
  · simpa only [IncidenceEncoding.word_length] using outside_slot _ ha.2.2.2

end Maxwell.Cost.DoublingInit
