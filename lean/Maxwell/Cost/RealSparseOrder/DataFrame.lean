import Maxwell.Cost.RealSparseOrder.Memory

namespace Maxwell.Cost.RealSparseOrder

/-- Full passes use the finite control bank below address one hundred.
Only the two destination data intervals can change above that bank. -/
def DataFrame (b : Buffer) (n : ℕ) (s t : RAMState) : Prop :=
  (∀j,100≤j→(j<b.coordinates ∨b.coordinates+2*n≤j)→t.indices j=s.indices j) ∧
  (∀j,1≤j→(j<b.coefficients ∨b.coefficients+n≤j)→t.words j=s.words j)

theorem MemoryFrame.dataFrame {b : Buffer} {n : ℕ} {s t : RAMState}
    (h : MemoryFrame b n s t) : DataFrame b n s t :=
  ⟨fun j hj ho=>h.1 j (by omega) ho,h.2⟩

theorem DataFrame.refl (b : Buffer) (n : ℕ) (s : RAMState) : DataFrame b n s s :=
  ⟨fun _ _ _=>rfl,fun _ _ _=>rfl⟩

theorem DataFrame.mono {b : Buffer} {m n : ℕ} {s t : RAMState}
    (h : DataFrame b m s t) (hmn : m≤n) : DataFrame b n s t := by
  constructor
  · intro j hj ho; exact h.1 j hj (by omega)
  · intro j hj ho; exact h.2 j hj (by omega)

theorem DataFrame.trans {b : Buffer} {n : ℕ} {s t u : RAMState}
    (h : DataFrame b n s t) (k : DataFrame b n t u) : DataFrame b n s u :=
  ⟨fun j hj ho=>(k.1 j hj ho).trans (h.1 j hj ho),
    fun j hj ho=>(k.2 j hj ho).trans (h.2 j hj ho)⟩

theorem DataFrame.shift_subset {b : Buffer} {m n : ℕ} {s t : RAMState}
    (h : DataFrame (b.shift m) n s t) : DataFrame b (m+n) s t := by
  constructor
  · intro j hj ho
    apply h.1 j hj
    simp only [Buffer.shift]
    omega
  · intro j hj ho
    apply h.2 j hj
    simp only [Buffer.shift]
    omega

theorem Records.dataFrame {a b : Buffer} {s t : RAMState} {es : List SparseEntry} {n : ℕ}
    (h : Records a s es) (ha : a.Safe) (hs : Separated a es.length b n)
    (hf : DataFrame b n s t) : Records a t es := by
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

/-- A control-only routine preserves every stored array. -/
theorem Records.dataFrame_zero {a b : Buffer} {s t : RAMState} {es : List SparseEntry}
    (h : Records a s es) (ha : a.Safe) (hf : DataFrame b 0 s t) : Records a t es := by
  rw [records_stored] at h ⊢
  intro i hi
  rcases h i hi with ⟨hr,hc,hv⟩
  unfold Buffer.Safe at ha
  have hrow := hf.1 (a.row i) (by simp only [Buffer.row]; omega) (by omega)
  have hcol := hf.1 (a.column i) (by simp only [Buffer.column]; omega) (by omega)
  have hval := hf.2 (a.value i) (by simp only [Buffer.value]; omega) (by omega)
  exact ⟨hrow.trans hr,hcol.trans hc,hval.trans hv⟩

end Maxwell.Cost.RealSparseOrder
