import Maxwell.Logical.GateTrace

/-! Exact sparse output chronology: selected boundary rows precede the
reverse chronological gate groups emitted by the finite archive compiler. -/
namespace Maxwell.Logical

theorem traceEntries_row_ge (start : ℕ) (gates : List GateRecord)
    (e : RationalCode.Entry) (he : e ∈ traceEntries start gates) : start ≤ e.row := by
  induction gates generalizing start with
  | nil => simp [traceEntries] at he
  | cons gate rest ih =>
    rw [traceEntries, List.mem_append] at he
    rcases he with he | he
    · exact Nat.le_trans (by omega) (ih (start+1) he)
    · cases gate <;> simp [GateRecord.entries] at he <;> rcases he with rfl | rfl | rfl <;> exact Nat.le_refl _

theorem RationalCode.squareEntries_trace {n d : ℕ} (c : RationalCode n d)
    (output : Fin n → Fin d) :
    c.squareEntries output =
      List.ofFn (fun i : Fin n => (⟨i.val,(output i).val,1⟩ : RationalCode.Entry)) ++
        traceEntries n c.trace := by
  rw [squareEntries,entries_trace,List.filter_append]
  have ht : (traceEntries n c.trace).filter (fun e => n ≤ e.row) = traceEntries n c.trace := by
    apply List.filter_eq_self.mpr
    intro e he
    simpa using traceEntries_row_ge n c.trace e he
  have hi : (RationalCode.input (n := n)).entries.filter (fun e => n ≤ e.row) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro e he
    simp only [entries,List.mem_ofFn] at he
    obtain ⟨i,rfl⟩ := he
    simp [i.isLt]
  rw [ht,hi,List.append_nil]

theorem sourceSquareEntries_trace (S : Source.SparseSystem) (precision : ℕ) :
    sourceSquareEntries S precision =
      List.ofFn (fun i : Fin S.n => (⟨i.val,(sourceOutput S precision i).val,1⟩ : RationalCode.Entry)) ++
        traceEntries S.n (sourceCircuit_rational S precision).code.trace :=
  RationalCode.squareEntries_trace _ _

end Maxwell.Logical
