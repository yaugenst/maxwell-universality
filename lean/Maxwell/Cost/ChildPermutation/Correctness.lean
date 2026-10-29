import Maxwell.Cost.ChildPermutation.Encoding

namespace Maxwell.Cost.ChildPermutation
open IncidenceEncoding (word)

private theorem vector_get_set {α : Type*} {n : ℕ} (v : Vector α n) (i j : Fin n) (x : α) :
    (v.set i.val x i.isLt).get j = if i=j then x else v.get j := by
  simp [Vector.get, Fin.cast, Array.getElem_set, Fin.ext_iff]

theorem stepOutputs_apply {k : ℕ} (width : ℕ) (d : Data k) (i : Fin (2^k))
    (out : Outputs k) (s : Fin 4) :
    stepOutputs width d i out s = (out s).set (d.writeIndex s i).val
      (word width (d.writeValue s i).val) (d.writeIndex s i).isLt := by
  fin_cases s <;> simp [stepOutputs,writeOutput]

theorem stepOutputs_get {k : ℕ} (width : ℕ) (d : Data k) (i j : Fin (2^k))
    (out : Outputs k) (s : Fin 4) :
    (stepOutputs width d i out s).get j =
      if d.writeIndex s i=j then word width (d.writeValue s i).val else (out s).get j := by
  rw [stepOutputs_apply,vector_get_set]

def fillOutputs {k : ℕ} (width : ℕ) (d : Data k) (out : Outputs k) :
    (limit : ℕ) → limit ≤ 2^k → Outputs k
  | 0, _ => out
  | limit+1, h => stepOutputs width d ⟨limit,by omega⟩ (fillOutputs width d out limit (by omega))

def fillMemory {k : ℕ} (l : Layout) (d : Data k) (memory : ℕ → Bool) :
    (limit : ℕ) → limit ≤ 2^k → (ℕ → Bool)
  | 0, _ => memory
  | limit+1, h => stepMemory l d ⟨limit,by omega⟩ (fillMemory l d memory limit (by omega))

theorem fill_represents {k : ℕ} {l : Layout} {memory : ℕ → Bool} {d : Data k} {out : Outputs k}
    (h : Represents l memory d out) (hs : l.Separated k) (limit : ℕ) (hl : limit ≤ 2^k) :
    Represents l (fillMemory l d memory limit hl) d (fillOutputs l.childWidth d out limit hl) := by
  induction limit with
  | zero => exact h
  | succ limit ih => exact represents_step (ih (by omega)) hs ⟨limit,by omega⟩

theorem fillMemory_frame {k : ℕ} (l : Layout) (d : Data k) (memory : ℕ → Bool)
    (limit : ℕ) (hl : limit ≤ 2^k) : MemoryFrame l k memory (fillMemory l d memory limit hl) := by
  induction limit with
  | zero => intro p _; rfl
  | succ limit ih => exact (ih (by omega)).trans (stepMemory_frame l d ⟨limit,by omega⟩ _)

/-- The inverse scatter visits precisely the inverse image of an output
address. This characterizes both completed entries and unvisited entries. -/
theorem fillOutputs_get {k : ℕ} (width : ℕ) (d : Data k) (out : Outputs k)
    (limit : ℕ) (hl : limit ≤ 2^k) (s : Fin 4) (j : Fin (2^k)) :
    (fillOutputs width d out limit hl s).get j =
      if ((d.writeIndex s).symm j).val < limit then
        word width (d.finalPerm s j).val else (out s).get j := by
  induction limit with
  | zero => simp [fillOutputs]
  | succ limit ih =>
    rw [fillOutputs,stepOutputs_get]
    by_cases he : d.writeIndex s ⟨limit,by omega⟩=j
    · rw [ite_eq_left he]
      rw [← he]
      simp [Data.finalPerm]
    · rw [ite_eq_right he,ih]
      have hne : ((d.writeIndex s).symm j).val ≠ limit := by
        intro hval
        have hj : (d.writeIndex s).symm j = ⟨limit,by omega⟩ := Fin.ext hval
        exact he ((congrArg (d.writeIndex s) hj).symm.trans ((d.writeIndex s).apply_symm_apply j))
      have hiff : ((d.writeIndex s).symm j).val < limit ↔
          ((d.writeIndex s).symm j).val < limit+1 := by omega
      simp only [hiff]

def finalOutputs {k : ℕ} (width : ℕ) (d : Data k) : Outputs k :=
  fun s => Vector.ofFn (fun j => word width (d.finalPerm s j).val)

/-- A full pass emits all four actual permutation arrays. The old output
contents have disappeared, including at inverse-scattered addresses. -/
theorem fill_output {k : ℕ} (width : ℕ) (d : Data k) (out : Outputs k) :
    fillOutputs width d out (2^k) le_rfl = finalOutputs width d := by
  funext s
  apply Vector.ext
  intro j hj
  have h := fillOutputs_get width d out (2^k) le_rfl s ⟨j,hj⟩
  simpa [finalOutputs,Vector.get,Fin.cast,((d.writeIndex s).symm ⟨j,hj⟩).isLt] using h

theorem final_represents {k : ℕ} {l : Layout} {memory : ℕ → Bool} {d : Data k} {out : Outputs k}
    (h : Represents l memory d out) (hs : l.Separated k) :
    Represents l (fillMemory l d memory (2^k) le_rfl) d (finalOutputs l.childWidth d) := by
  rw [← fill_output l.childWidth d out]
  exact fill_represents h hs (2^k) le_rfl

end Maxwell.Cost.ChildPermutation
