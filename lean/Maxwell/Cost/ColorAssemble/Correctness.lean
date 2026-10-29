import Maxwell.Cost.ColorAssemble.Encoding

namespace Maxwell.Cost.ColorAssemble
open ChildPermutation (Layout)

/-- The chronological pass updates one saved output array per iteration. -/
def fillOutput {k : ℕ} (layout : Layout) (data : Data k) (out : Output k) :
    (limit : ℕ) → limit≤2*(2^k) → Output k
  | 0,_ => out
  | limit+1,hl => stepOutput layout data ⟨limit,by omega⟩ (fillOutput layout data out limit (by omega))

theorem fillOutput_get {k : ℕ} (layout : Layout) (data : Data k) (out : Output k)
    (limit : ℕ) (hl : limit≤2*(2^k)) (j : Fin (2*(2^k))) :
    (fillOutput layout data out limit hl).get j =
      if j.val<limit then IncidenceEncoding.word layout.parentWidth (data.value j).val else out.get j := by
  induction limit with
  | zero => simp [fillOutput]
  | succ limit ih =>
    simp only [fillOutput,stepOutput]
    rw [Maxwell.Logical.Routing.DummyFill.get_set _ ⟨limit,by omega⟩ j]
    by_cases he : (⟨limit,by omega⟩ : Fin (2*(2^k)))=j
    · have hj : j.val=limit := (congrArg Fin.val he).symm
      simp [he,hj]
    · have hj : j.val≠limit := fun h => he (Fin.ext h.symm)
      simp only [he,↓reduceIte,ih (by omega)]
      have hiff : j.val<limit+1 ↔ j.val<limit := by omega
      simp only [hiff]

def finalOutput {k : ℕ} (layout : Layout) (data : Data k) : Output k :=
  DoublingPass.words layout.parentWidth data.values

theorem fillOutput_complete {k : ℕ} (layout : Layout) (data : Data k) (out : Output k) :
    fillOutput layout data out (2*(2^k)) le_rfl = finalOutput layout data := by
  apply Vector.ext
  intro j hj
  have h := fillOutput_get layout data out (2*(2^k)) le_rfl ⟨j,hj⟩
  simpa [hj,finalOutput,DoublingPass.words,IncidenceEncoding.words,Data.values,Vector.get,Fin.cast] using h

theorem fillOutput_congr {k : ℕ} (layout : Layout) (data : Data k) (out : Output k)
    {a b : ℕ} (h : a=b) (ha : a≤2*(2^k)) (hb : b≤2*(2^k)) :
    fillOutput layout data out a ha=fillOutput layout data out b hb := by subst b; rfl

end Maxwell.Cost.ColorAssemble
