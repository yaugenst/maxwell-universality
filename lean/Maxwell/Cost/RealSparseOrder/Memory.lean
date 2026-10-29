import Maxwell.Cost.RealSparseOrder.Buffer

namespace Maxwell.Cost.RealSparseOrder

def Buffer.shift (b : Buffer) (n : ℕ) : Buffer :=
  ⟨b.coefficients+n,b.coordinates+2*n⟩

def Buffer.Safe (b : Buffer) : Prop := 100≤b.coefficients ∧100≤b.coordinates

@[simp] theorem Buffer.shift_zero (b : Buffer) : b.shift 0=b := by cases b; rfl
@[simp] theorem Buffer.shift_shift (b : Buffer) (m n : ℕ) :
    (b.shift m).shift n=b.shift (m+n) := by
  cases b
  simp [shift,Nat.mul_add,Nat.add_assoc]

theorem Buffer.Safe.shift {b : Buffer} (h : b.Safe) (n : ℕ) : (b.shift n).Safe := by
  simp only [Buffer.Safe,Buffer.shift] at *
  omega

/-- Exact records in addressed memory; the recursive form exposes consumed heads. -/
def Records (b : Buffer) (s : RAMState) : List SparseEntry →Prop
  | [] => True
  | e::es => s.indices b.coordinates=e.row ∧s.indices (b.coordinates+1)=e.column ∧
      s.words b.coefficients=e.value ∧Records (b.shift 1) s es

@[simp] theorem records_nil (b : Buffer) (s : RAMState) : Records b s [] := trivial

theorem records_stored (b : Buffer) (s : RAMState) (es : List SparseEntry) :
    Records b s es ↔Stored b s es := by
  induction es generalizing b with
  | nil => simp [Records,Stored,StoredPrefix]
  | cons e es ih =>
    rw [Records,ih]
    constructor
    · rintro ⟨hr,hc,hv,ht⟩ i hi
      cases i with
      | zero => simpa [Buffer.row,Buffer.column,Buffer.value,RealSparse.entryAt] using ⟨hr,hc,hv⟩
      | succ i =>
        have h := ht i (by simpa using hi)
        simpa [Buffer.shift,Buffer.row,Buffer.column,Buffer.value,RealSparse.entryAt,
          Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h
    · intro h
      have hh := h 0 (by simp)
      refine ⟨?_,?_,?_,?_⟩
      · simpa [Buffer.row,RealSparse.entryAt] using hh.1
      · simpa [Buffer.column,RealSparse.entryAt] using hh.2.1
      · simpa [Buffer.value,RealSparse.entryAt] using hh.2.2
      · intro i hi
        have ht := h (i+1) (by simpa using Nat.succ_lt_succ hi)
        simpa [Buffer.shift,Buffer.row,Buffer.column,Buffer.value,RealSparse.entryAt,
          Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ht

/-- All cells outside this destination interval remain unchanged, including
unused cells and unrelated arrays. The finite register bank is excluded. -/
def MemoryFrame (b : Buffer) (n : ℕ) (s t : RAMState) : Prop :=
  (∀j,17≤j→(j<b.coordinates ∨b.coordinates+2*n≤j)→t.indices j=s.indices j) ∧
  (∀j,1≤j→(j<b.coefficients ∨b.coefficients+n≤j)→t.words j=s.words j)

theorem MemoryFrame.refl (b : Buffer) (n : ℕ) (s : RAMState) : MemoryFrame b n s s :=
  ⟨fun _ _ _=>rfl,fun _ _ _=>rfl⟩

theorem MemoryFrame.mono {b : Buffer} {m n : ℕ} {s t : RAMState}
    (h : MemoryFrame b m s t) (hmn : m≤n) : MemoryFrame b n s t := by
  constructor
  · intro j hj ho
    exact h.1 j hj (by omega)
  · intro j hj ho
    exact h.2 j hj (by omega)

theorem MemoryFrame.trans {b : Buffer} {n : ℕ} {s t u : RAMState}
    (h : MemoryFrame b n s t) (k : MemoryFrame b n t u) : MemoryFrame b n s u :=
  ⟨fun j hj ho=>(k.1 j hj ho).trans (h.1 j hj ho),
    fun j hj ho=>(k.2 j hj ho).trans (h.2 j hj ho)⟩

theorem MemoryFrame.shift_subset {b : Buffer} {m n : ℕ} {s t : RAMState}
    (h : MemoryFrame (b.shift m) n s t) : MemoryFrame b (m+n) s t := by
  constructor
  · intro j hj ho
    apply h.1 j hj
    simp only [Buffer.shift]
    omega
  · intro j hj ho
    apply h.2 j hj
    simp only [Buffer.shift]
    omega

/-- Separation of the coordinate and coefficient intervals is checked once
at the buffer boundary. The two address spaces are independent. -/
def Separated (a : Buffer) (m : ℕ) (b : Buffer) (n : ℕ) : Prop :=
  (a.coordinates+2*m≤b.coordinates ∨b.coordinates+2*n≤a.coordinates) ∧
  (a.coefficients+m≤b.coefficients ∨b.coefficients+n≤a.coefficients)

theorem Separated.symm {a b : Buffer} {m n : ℕ} (h : Separated a m b n) :
    Separated b n a m := ⟨h.1.symm,h.2.symm⟩

theorem Separated.subset {a b : Buffer} {m n i j r q : ℕ}
    (h : Separated a m b n) (hi : i+r≤m) (hj : j+q≤n) :
    Separated (a.shift i) r (b.shift j) q := by
  simp only [Separated,Buffer.shift] at *
  constructor <;> omega

theorem Records.frame {a b : Buffer} {s t : RAMState} {es : List SparseEntry} {n : ℕ}
    (h : Records a s es) (ha : a.Safe) (hs : Separated a es.length b n)
    (hf : MemoryFrame b n s t) : Records a t es := by
  rw [records_stored] at h ⊢
  intro i hi
  rcases h i hi with ⟨hr,hc,hv⟩
  unfold Separated at hs
  unfold Buffer.Safe at ha
  have hrow := hf.1 (a.row i) (by simp only [Buffer.row]; omega) (by
    simp only [Buffer.row]; omega)
  have hcol := hf.1 (a.column i) (by simp only [Buffer.column]; omega) (by
    simp only [Buffer.column]; omega)
  have hval := hf.2 (a.value i) (by simp only [Buffer.value]; omega) (by
    simp only [Buffer.value]; omega)
  exact ⟨hrow.trans hr,hcol.trans hc,hval.trans hv⟩

end Maxwell.Cost.RealSparseOrder
