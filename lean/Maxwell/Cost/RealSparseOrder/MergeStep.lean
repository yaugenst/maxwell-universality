import Maxwell.Cost.RealSparseOrder.MergeInvariant

namespace Maxwell.Cost.RealSparseOrder.Merge
open RealSimulation.Control

def body : Code :=
  .branch 3 0 (.call (Emit.program false))
    (.branch 4 0 (.call (Emit.program true))
      (.seq (.call Compare.program)
        (Compare.choose (.call (Emit.program true)) (.call (Emit.program false)))))

def loopCode : Code := .loop 1 5 body

def Channels (s t : RAMState) : Prop :=
  t.randomCursor=s.randomCursor ∧t.output=s.output ∧t.indexOutput=s.indexOutput

structure StepResult (s t : RAMState) (out : Buffer) (xs ys : List SparseEntry)
    (e : SparseEntry) (xs' ys' : List SparseEntry) (a' b' : Buffer) : Prop where
  merge_eq : merge xs ys=e::merge xs' ys'
  length : xs'.length+ys'.length+1=xs.length+ys.length
  invariant : Invariant t a' b' (out.shift 1) xs' ys'
  head : Records out t [e]
  frame : MemoryFrame out 1 s t
  channels : Channels s t

private theorem left_result {s : Store} {a b out : Buffer} {e : SparseEntry}
    {xs ys : List SparseEntry} (h : Invariant s.val a b out (e::xs) ys)
    (hm : merge (e::xs) ys=e::merge xs ys) :
    StepResult s.val (Store.ofState (Emit.advanced true s.val)).val out (e::xs) ys
      e xs ys (a.shift 1) b := by
  refine ⟨hm,by simp; omega,(invariant_ofState _ _ _ _ _ _).mpr h.emit_left,
    (records_ofState _ _ _).mpr ?_,emit_frame true h.config,?_⟩
  · exact emit_head true s.val e out h.config.outRow h.config.outValue h.safeOut h.left_head
  · exact ⟨rfl,rfl,rfl⟩

private theorem right_result {s : Store} {a b out : Buffer} {e : SparseEntry}
    {xs ys : List SparseEntry} (h : Invariant s.val a b out xs (e::ys))
    (hm : merge xs (e::ys)=e::merge xs ys) :
    StepResult s.val (Store.ofState (Emit.advanced false s.val)).val out xs (e::ys)
      e xs ys a (b.shift 1) := by
  refine ⟨hm,by simp; omega,(invariant_ofState _ _ _ _ _ _).mpr h.emit_right,
    (records_ofState _ _ _).mpr ?_,emit_frame false h.config,?_⟩
  · exact emit_head false s.val e out h.config.outRow h.config.outValue h.safeOut h.right_head
  · exact ⟨rfl,rfl,rfl⟩

private theorem StepResult.before_compare {s : Store} {out : Buffer} {xs ys xs' ys' : List SparseEntry}
    {t : Store} {e : SparseEntry} {a' b' : Buffer}
    (h : StepResult (Store.ofState (Compare.loaded s.val)).val t.val out xs ys e xs' ys' a' b') :
    StepResult s.val t.val out xs ys e xs' ys' a' b' := by
  refine ⟨h.merge_eq,h.length,h.invariant,h.head,?_,h.channels⟩
  exact ((compare_frame s.val out).mono (by omega)).trans h.frame

/-- Every nonempty merge step reads the selected stored record and advances
its actual cursor. The largest branch costs at most twenty-seven instructions. -/
theorem step (input : RAMInput) (tape : ℕ→Bool) (s : Store)
    (a b out : Buffer) (xs ys : List SparseEntry)
    (h : Invariant s.val a b out xs ys) (hne : 0<xs.length+ys.length) :
    ∃cost t e xs' ys' a' b', cost≤27 ∧ Executes input tape body cost s t ∧
      StepResult s.val t.val out xs ys e xs' ys' a' b' := by
  cases xs with
  | nil =>
    cases ys with
    | nil => simp at hne
    | cons e ys =>
      have run := Emit.executes false input tape s (h.emit_ready false)
      refine ⟨16,_,e,[],ys,a,b.shift 1,by omega,?_,right_result h ?_⟩
      · exact Executes.yes (by rw [h.config.leftCount,h.config.zero]; simp) run
      · simp [merge]
  | cons e xs =>
    cases ys with
    | nil =>
      have run := Emit.executes true input tape s (h.emit_ready true)
      refine ⟨17,_,e,xs,[],a.shift 1,b,by omega,?_,left_result h ?_⟩
      · exact Executes.no (by rw [h.config.leftCount,h.config.zero]; simp)
          (Executes.yes (by rw [h.config.rightCount,h.config.zero]; simp) run)
      · simp [merge]
    | cons f ys =>
      let mid := Store.ofState (Compare.loaded s.val)
      have hm : Invariant mid.val a b out (e::xs) (f::ys) :=
        (invariant_ofState _ _ _ _ _ _).mpr h.compare
      have hload := Compare.executes input tape s h.compare_ready
      have hkey : (mid.val.indices 13<mid.val.indices 15 ∨
          (mid.val.indices 13=mid.val.indices 15 ∧mid.val.indices 14≤mid.val.indices 16)) ↔
          KeyLE e f := by
        rcases Compare.registers s.val with ⟨h13,h14,h15,h16⟩
        change ((Compare.loaded s.val).indices 13<(Compare.loaded s.val).indices 15 ∨
          ((Compare.loaded s.val).indices 13=(Compare.loaded s.val).indices 15 ∧
          (Compare.loaded s.val).indices 14≤(Compare.loaded s.val).indices 16)) ↔_
        rw [h13,h14,h15,h16,h.config.leftRow,h.config.rightRow,h.left.1,h.left.2.1,
          h.right.1,h.right.2.1]
        rfl
      by_cases hk : KeyLE e f
      · obtain ⟨cost,hcost,run⟩ := Compare.choose_left input tape (.call (Emit.program true)) (.call (Emit.program false))
          mid (Store.ofState (Emit.advanced true mid.val)) 15
          (hkey.mpr hk) (Emit.executes true input tape mid (hm.emit_ready true))
        refine ⟨1+(1+(7+cost)),Store.ofState (Emit.advanced true mid.val),e,xs,f::ys,a.shift 1,b,by omega,?_,?_⟩
        · exact Executes.no (by rw [h.config.leftCount,h.config.zero]; simp)
            (Executes.no (by rw [h.config.rightCount,h.config.zero]; simp)
              (Executes.seq hload run))
        · apply StepResult.before_compare
          exact left_result hm (by simp [merge,hk])
      · obtain ⟨cost,hcost,run⟩ := Compare.choose_right input tape (.call (Emit.program true)) (.call (Emit.program false))
          mid (Store.ofState (Emit.advanced false mid.val)) 15
          (fun hh=>hk (hkey.mp hh)) (Emit.executes false input tape mid (hm.emit_ready false))
        refine ⟨1+(1+(7+cost)),Store.ofState (Emit.advanced false mid.val),f,e::xs,ys,a,b.shift 1,by omega,?_,?_⟩
        · exact Executes.no (by rw [h.config.leftCount,h.config.zero]; simp)
            (Executes.no (by rw [h.config.rightCount,h.config.zero]; simp)
              (Executes.seq hload run))
        · apply StepResult.before_compare
          exact right_result hm (by simp [merge,hk])

end Maxwell.Cost.RealSparseOrder.Merge
