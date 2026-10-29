import Maxwell.Cost.RealSparseOrder.IndexBounds
import Maxwell.Cost.RealSparseOrder.MergeStep

namespace Maxwell.Cost.RealSparseOrder.Merge
open RealSimulation.Control RealSimulation.IndexWidth

/-- The cap covers all stored natural values and both endpoints of each
remaining array interval, so repeated cursors cannot accumulate extra width. -/
structure Bounded (B : ℕ) (s : RAMState) (a b out : Buffer) (xs ys : List SparseEntry) : Prop where
  invariant : Invariant s a b out xs ys
  indices : IndexBound B s
  leftEnd : Within B a xs.length
  rightEnd : Within B b ys.length
  outEnd : Within B out (xs.length+ys.length)

@[simp] theorem bounded_ofState (B : ℕ) (s : RAMState) (a b out : Buffer) (xs ys : List SparseEntry) :
    Bounded B (Store.ofState s).val a b out xs ys ↔Bounded B s a b out xs ys := by
  constructor <;> intro h
  · exact ⟨(invariant_ofState _ _ _ _ _ _).mp h.invariant,h.indices,h.leftEnd,h.rightEnd,h.outEnd⟩
  · exact ⟨(invariant_ofState _ _ _ _ _ _).mpr h.invariant,h.indices,h.leftEnd,h.rightEnd,h.outEnd⟩

theorem Bounded.compare {B : ℕ} {s : RAMState} {a b out : Buffer} {xs ys : List SparseEntry}
    (h : Bounded B s a b out xs ys) (hx : 0<xs.length) (hy : 0<ys.length) :
    Bounded B (Compare.loaded s) a b out xs ys :=
  ⟨h.invariant.compare,compare_index_bound h.invariant h.indices h.leftEnd h.rightEnd hx hy,
    h.leftEnd,h.rightEnd,h.outEnd⟩

theorem Bounded.emit_left {B : ℕ} {s : RAMState} {a b out : Buffer} {e : SparseEntry}
    {xs ys : List SparseEntry} (h : Bounded B s a b out (e::xs) ys) :
    Bounded B (Emit.advanced true s) (a.shift 1) b (out.shift 1) xs ys := by
  refine ⟨h.invariant.emit_left,
    emit_index_bound true h.invariant h.indices h.leftEnd h.rightEnd h.outEnd (by simp),
    h.leftEnd.subset ?_,h.rightEnd,h.outEnd.subset ?_⟩
  · simp only [List.length_cons]; omega
  · simp only [List.length_cons]; omega

theorem Bounded.emit_right {B : ℕ} {s : RAMState} {a b out : Buffer} {e : SparseEntry}
    {xs ys : List SparseEntry} (h : Bounded B s a b out xs (e::ys)) :
    Bounded B (Emit.advanced false s) a (b.shift 1) (out.shift 1) xs ys := by
  refine ⟨h.invariant.emit_right,
    emit_index_bound false h.invariant h.indices h.leftEnd h.rightEnd h.outEnd (by simp),
    h.leftEnd,h.rightEnd.subset ?_,h.outEnd.subset ?_⟩
  · simp only [List.length_cons]; omega
  · simp only [List.length_cons]; omega

/-- A complete actual body returns to the same global index cap. -/
theorem bounded_step (input : RAMInput) (tape : ℕ→Bool) (B : ℕ) (s : Store)
    (a b out : Buffer) (xs ys : List SparseEntry)
    (h : Bounded B s.val a b out xs ys) (hne : 0<xs.length+ys.length) :
    ∃cost t xs' ys' a' b', cost≤27 ∧Executes input tape body cost s t ∧
      xs'.length+ys'.length+1=xs.length+ys.length ∧
      Bounded B t.val a' b' (out.shift 1) xs' ys' := by
  cases xs with
  | nil =>
    cases ys with
    | nil => simp at hne
    | cons e ys =>
      refine ⟨16,Store.ofState (Emit.advanced false s.val),[],ys,a,b.shift 1,by omega,?_,by simp,
        (bounded_ofState _ _ _ _ _ _ _).mpr h.emit_right⟩
      exact Executes.yes (by rw [h.invariant.config.leftCount,h.invariant.config.zero]; simp)
        (Emit.executes false input tape s (h.invariant.emit_ready false))
  | cons e xs =>
    cases ys with
    | nil =>
      refine ⟨17,Store.ofState (Emit.advanced true s.val),xs,[],a.shift 1,b,by omega,?_,by simp,
        (bounded_ofState _ _ _ _ _ _ _).mpr h.emit_left⟩
      exact Executes.no (by rw [h.invariant.config.leftCount,h.invariant.config.zero]; simp)
        (Executes.yes (by rw [h.invariant.config.rightCount,h.invariant.config.zero]; simp)
          (Emit.executes true input tape s (h.invariant.emit_ready true)))
    | cons f ys =>
      let mid := Store.ofState (Compare.loaded s.val)
      have hm : Bounded B mid.val a b out (e::xs) (f::ys) :=
        (bounded_ofState _ _ _ _ _ _ _).mpr (h.compare (by simp) (by simp))
      have hload := Compare.executes input tape s h.invariant.compare_ready
      by_cases hk : mid.val.indices 13<mid.val.indices 15 ∨
          (mid.val.indices 13=mid.val.indices 15 ∧mid.val.indices 14≤mid.val.indices 16)
      · obtain ⟨cost,hcost,run⟩ := Compare.choose_left input tape (.call (Emit.program true))
          (.call (Emit.program false)) mid (Store.ofState (Emit.advanced true mid.val)) 15 hk
          (Emit.executes true input tape mid (hm.invariant.emit_ready true))
        refine ⟨1+(1+(7+cost)),Store.ofState (Emit.advanced true mid.val),xs,f::ys,a.shift 1,b,
          by omega,?_,by simp; omega,(bounded_ofState _ _ _ _ _ _ _).mpr hm.emit_left⟩
        exact Executes.no (by rw [h.invariant.config.leftCount,h.invariant.config.zero]; simp)
          (Executes.no (by rw [h.invariant.config.rightCount,h.invariant.config.zero]; simp)
            (Executes.seq hload run))
      · obtain ⟨cost,hcost,run⟩ := Compare.choose_right input tape (.call (Emit.program true))
          (.call (Emit.program false)) mid (Store.ofState (Emit.advanced false mid.val)) 15 hk
          (Emit.executes false input tape mid (hm.invariant.emit_ready false))
        refine ⟨1+(1+(7+cost)),Store.ofState (Emit.advanced false mid.val),e::xs,ys,a,b.shift 1,
          by omega,?_,by simp; omega,(bounded_ofState _ _ _ _ _ _ _).mpr hm.emit_right⟩
        exact Executes.no (by rw [h.invariant.config.leftCount,h.invariant.config.zero]; simp)
          (Executes.no (by rw [h.invariant.config.rightCount,h.invariant.config.zero]; simp)
            (Executes.seq hload run))

end Maxwell.Cost.RealSparseOrder.Merge
