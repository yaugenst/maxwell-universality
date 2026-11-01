import Maxwell.Continuum.Main

/-! Machine-cost constants can enlarge the analytic bounds without changing
the represented continuum instance or its conditioning and tolerance powers. -/
namespace Maxwell.Continuum.Realization
open RealizationParameters

/-- Retain the analytic powers while accommodating execution and word bounds. -/
def Constants.enlarge (C : Constants) (overhead words : ℕ) : Constants where
  overhead := max C.overhead overhead
  wordCoefficient := max C.wordCoefficient words
  conditionPower := C.conditionPower
  tolerancePower := C.tolerancePower
  overhead_pos := C.overhead_pos.trans_le (le_max_left _ _)
  wordCoefficient_pos := C.wordCoefficient_pos.trans_le (le_max_left _ _)
  conditionPower_pos := C.conditionPower_pos
  tolerancePower_pos := C.tolerancePower_pos

theorem budget_enlarge (C : Constants) (overhead words : ℕ) (S : Source.SparseSystem) (k : ℕ) :
    budget C S k≤budget (C.enlarge overhead words) S k := by
  unfold budget Constants.enlarge
  gcongr
  exact_mod_cast le_max_left C.overhead overhead

theorem wordBudget_enlarge (C : Constants) (overhead words : ℕ) (S : Source.SparseSystem) :
    wordBudget C S≤wordBudget (C.enlarge overhead words) S :=
  Nat.mul_le_mul_right _ (le_max_left _ _)

theorem Resources.enlarge {p : Source.Parameters} {C : Constants} {S : Source.SparseSystem}
    {hm : 0<S.nnz} {hb : S.source≠0} {j : Fin (drawCount p S hm)}
    (h : Resources p C S hm hb j) (overhead words : ℕ) :
    Resources p (C.enlarge overhead words) S hm hb j := by
  obtain ⟨sides,material,source,templates,volume,description,grid,format,output,positive,tolerance,
    residual,energy,random⟩:=h
  have hb' :=budget_enlarge C overhead words S
  have hw :=wordBudget_enlarge C overhead words S
  exact ⟨sides,material,source,templates,volume.trans (hb' 24),description.trans (hb' 64),
    grid.trans (hb' 24),format.trans hw,(fun w i=>(output w i).trans hw),positive,tolerance,
    residual.trans hw,energy.trans hw,random.trans hw⟩

theorem GoodDraw.enlarge {p : Source.Parameters} {C : Constants} {S : Source.SparseSystem}
    {hm : 0<S.nnz} {hb : S.source≠0} {j : Fin (drawCount p S hm)}
    (h : GoodDraw p C S hm hb j) (overhead words : ℕ) :
    GoodDraw p (C.enlarge overhead words) S hm hb j := h

#print axioms Resources.enlarge
#print axioms GoodDraw.enlarge
end Maxwell.Continuum.Realization
