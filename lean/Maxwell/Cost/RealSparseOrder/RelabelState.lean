import Maxwell.Cost.RealSparseOrder.RelabelOps

namespace Maxwell.Cost.RealSparseOrder.Relabel
open RealSimulation.Control

structure Config (s : RAMState) (b : Buffer) (remaining : ℕ) (previous : Option ℕ)
    (count m map rhs : ℕ) : Prop where
  zero : s.indices 0=0
  one : s.indices 1=1
  two : s.indices 2=2
  originalCount : s.indices 26=m
  remaining : s.indices 32=remaining
  cursor : s.indices 33=b.coordinates
  previousValue : s.indices 34=previous.getD 0
  count : s.indices 35=count
  seen : s.indices 36=if previous.isSome then 1 else 0
  mapBase : s.indices 40=map
  rhsBase : s.indices 41=rhs

@[simp] theorem config_ofState (s : RAMState) (b : Buffer) (remaining : ℕ)
    (previous : Option ℕ) (count m map rhs : ℕ) :
    Config (Store.ofState s).val b remaining previous count m map rhs ↔
      Config s b remaining previous count m map rhs := by
  constructor <;> intro h <;> exact ⟨h.zero,h.one,h.two,h.originalCount,h.remaining,
    h.cursor,h.previousValue,h.count,h.seen,h.mapBase,h.rhsBase⟩

theorem Config.loaded {s : RAMState} {b : Buffer} {remaining : ℕ} {previous : Option ℕ}
    {count m map rhs : ℕ} (h : Config s b remaining previous count m map rhs) :
    Config (loaded s) b remaining previous count m map rhs := by
  constructor <;> simp [Relabel.loaded,RAMState.setIndex,h.zero,h.one,h.two,h.originalCount,
    h.remaining,h.cursor,h.previousValue,h.count,h.seen,h.mapBase,h.rhsBase]

theorem Config.created {input : RAMInput} {s : RAMState} {b : Buffer} {remaining : ℕ}
    {previous : Option ℕ} {count m map rhs row : ℕ}
    (h : Config s b remaining previous count m map rhs)
    (hm : 100≤map) (hr : s.indices 37=row) :
    Config (created input s) b remaining (some row) (count+1) m map rhs := by
  have hd : ∀j:ℕ,j<42→j≠map+count := by omega
  constructor <;> simp [Relabel.created,RAMState.setIndex,RAMState.setWord,hd,hr,
    h.zero,h.one,h.two,h.originalCount,h.remaining,h.cursor,h.count,h.mapBase,h.rhsBase]

theorem Config.rewritten {s : RAMState} {b : Buffer} {remaining : ℕ} {previous : Option ℕ}
    {count m map rhs : ℕ} (h : Config s b remaining previous count m map rhs)
    (hb : 100≤b.coordinates) :
    Config (rewritten s) (b.shift 1) (remaining-1) previous count m map rhs := by
  have hd : ∀j:ℕ,j<42→j≠b.coordinates := by omega
  constructor <;> simp [Relabel.rewritten,RAMState.setIndex,hd,Buffer.shift,h.zero,h.one,h.two,
    h.originalCount,h.remaining,h.cursor,h.previousValue,h.count,h.seen,h.mapBase,h.rhsBase]

theorem Config.create_ready {s : Store} {b : Buffer} {remaining : ℕ} {previous : Option ℕ}
    {count m map rhs : ℕ} (h : Config s.val b remaining previous count m map rhs)
    (hm : 100≤map) (hr : 100≤rhs) : CreateReady s.val :=
  ⟨s.property,h.one,by simpa only [h.mapBase] using hm,by simpa only [h.rhsBase] using hr⟩

theorem Config.rewrite_ready {s : Store} {b : Buffer} {remaining : ℕ} {previous : Option ℕ}
    {count m map rhs : ℕ} (h : Config s.val b remaining previous count m map rhs)
    (hb : 100≤b.coordinates) : RewriteReady s.val :=
  ⟨s.property,h.one,h.two,by simpa only [h.cursor] using hb⟩

/-- Stored gathered values are keyed by the corresponding retained original
row label. The natural and real arrays use independent address spaces. -/
def Gathered (map rhs : ℕ) (s : RAMState) (vector : ℕ→ℝ) : List ℕ→Prop
  | [] => True
  | row::rows => s.indices map=row ∧s.words rhs=vector row ∧
      Gathered (map+1) (rhs+1) s vector rows

end Maxwell.Cost.RealSparseOrder.Relabel
