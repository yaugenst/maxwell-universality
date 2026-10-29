import Maxwell.Cost.RealSparseOrder.RelabelEffect

namespace Maxwell.Cost.RealSparseOrder.Relabel
open RealSimulation.Control

/-- The scan changes only record coordinates and the reserved map/RHS
intervals. Its finite control bank and one real temporary are excluded. -/
def Frame (b : Buffer) (n map rhs count : ℕ) (s t : RAMState) : Prop :=
  (∀j,100≤j→(j<b.coordinates ∨b.coordinates+2*n≤j)→
    (j<map+count ∨map+count+n≤j)→t.indices j=s.indices j) ∧
  (∀j,1≤j→(j<rhs+count ∨rhs+count+n≤j)→t.words j=s.words j)

theorem Frame.refl (b : Buffer) (n map rhs count : ℕ) (s : RAMState) : Frame b n map rhs count s s :=
  ⟨fun _ _ _ _=>rfl,fun _ _ _=>rfl⟩

theorem Frame.trans {b : Buffer} {n map rhs count : ℕ} {s t u : RAMState}
    (h : Frame b n map rhs count s t) (k : Frame b n map rhs count t u) :
    Frame b n map rhs count s u :=
  ⟨fun j hj hb hm=>(k.1 j hj hb hm).trans (h.1 j hj hb hm),
    fun j hj hr=>(k.2 j hj hr).trans (h.2 j hj hr)⟩

theorem Frame.mono {b : Buffer} {n N map rhs count : ℕ} {s t : RAMState}
    (h : Frame b n map rhs count s t) (hn : n≤N) : Frame b N map rhs count s t := by
  constructor
  · intro j hj hb hm; exact h.1 j hj (by omega) (by omega)
  · intro j hj hr; exact h.2 j hj (by omega)

theorem Frame.tail {b : Buffer} {n map rhs count c : ℕ} {s t : RAMState}
    (h : Frame (b.shift 1) n map rhs c s t) (hl : count≤c) (hu : c≤count+1) :
    Frame b (n+1) map rhs count s t := by
  constructor
  · intro j hj hb hm
    apply h.1 j hj
    · simp only [Buffer.shift]; omega
    · omega
  · intro j hj hr; exact h.2 j hj (by omega)

theorem processed_frame {input : RAMInput} {s : Store} {b : Buffer} {remaining : ℕ}
    {previous : Option ℕ} {count m map rhs row : ℕ}
    (h : Config s.val b remaining previous count m map rhs)
    (hm : 100≤map) (hr : s.val.indices b.coordinates=row) :
    Frame b 1 map rhs count s.val (processed input previous row s).val := by
  constructor
  · intro j hj hrow hmap
    rw [processed_indices h hm hr j hj]
    simp [show j≠b.coordinates by omega,show j≠map+count by omega]
  · intro j hj hrow
    rw [processed_words h hm hr j hj]
    simp [show j≠rhs+count by omega]

theorem Records.congr_intervals {b : Buffer} {s t : RAMState} {es : List SparseEntry}
    (h : Records b s es)
    (hi : ∀j,b.coordinates≤j→j<b.coordinates+2*es.length→t.indices j=s.indices j)
    (hw : ∀j,b.coefficients≤j→j<b.coefficients+es.length→t.words j=s.words j) :
    Records b t es := by
  rw [records_stored] at h ⊢
  intro i hi'
  obtain ⟨hr,hc,hv⟩ := h i hi'
  refine ⟨(hi (b.row i) ?_ ?_).trans hr,(hi (b.column i) ?_ ?_).trans hc,
    (hw (b.value i) ?_ ?_).trans hv⟩ <;>
    simp only [Buffer.row,Buffer.column,Buffer.value] <;> omega

end Maxwell.Cost.RealSparseOrder.Relabel
