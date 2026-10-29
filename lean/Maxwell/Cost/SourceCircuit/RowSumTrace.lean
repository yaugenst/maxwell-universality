import Maxwell.Cost.SourceCircuit.RowSumData
import Maxwell.Cost.SourceCircuit.HornerTrace

namespace Maxwell.Cost.SourceCircuit.RowSumTrace
open Logical

set_option backward.isDefEq.respectTransparency false

def sumTrace : List ℕ → ℕ → ℕ → HornerTrace.Result
  | [], next, accumulator => ⟨next, accumulator, []⟩
  | term :: terms, next, accumulator =>
      let tail := sumTrace terms next accumulator
      ⟨tail.next+1, tail.next, tail.gates ++ [.add term tail.output]⟩

theorem sumTrace_append (a b : List ℕ) (next accumulator : ℕ) :
    sumTrace (a ++ b) next accumulator =
      let tail := sumTrace b next accumulator
      let head := sumTrace a tail.next tail.output
      ⟨head.next, head.output, tail.gates ++ head.gates⟩ := by
  induction a generalizing next accumulator with
  | nil => simp [sumTrace]
  | cons term terms ih => simp [sumTrace, ih, List.append_assoc]

structure Data where
  next : ℕ
  accumulator : ℕ
  gates : List GateRecord
  terms : List ℕ

def step (d : Data) : Data where
  next := d.next+1
  accumulator := d.next
  gates := d.gates ++ [.add (d.terms.getLastD 0) d.accumulator]
  terms := d.terms.dropLast

def complete (d : Data) : Data := (step^[d.terms.length]) d

theorem complete_step (d : Data) (hne : d.terms ≠ []) : complete (step d) = complete d := by
  have hn := List.length_pos_iff.mpr hne
  unfold complete
  have hl : (step d).terms.length + 1 = d.terms.length := by
    simp only [step, List.length_dropLast]
    omega
  rw [← hl, Function.iterate_succ_apply]

theorem complete_compiles (d : Data) :
    complete d =
      let result := sumTrace d.terms d.next d.accumulator
      ⟨result.next, result.output, d.gates ++ result.gates, []⟩ := by
  suffices ∀ terms : List ℕ, ∀ d : Data, d.terms = terms →
      complete d =
        let result := sumTrace terms d.next d.accumulator
        ⟨result.next, result.output, d.gates ++ result.gates, []⟩ from this d.terms d rfl
  intro terms
  induction terms using List.reverseRecOn with
  | nil =>
    intro d hd
    cases d
    simp_all [complete, sumTrace]
  | append_singleton terms term ih =>
    intro d hd
    have hn : d.terms ≠ [] := by simp [hd]
    rw [← complete_step d hn]
    have ht : (step d).terms = terms := by simp [step, hd]
    rw [ih (step d) ht, sumTrace_append]
    simp [sumTrace, step, hd, List.append_assoc]

structure Represents (width : ℕ) (stored : RowSum.Data) (logical : Data) : Prop where
  next : addressValue stored.next = logical.next
  accumulator : addressValue stored.accumulator = logical.accumulator
  terms : stored.terms.map addressValue = logical.terms
  gates : traceBytes width logical.gates = some stored.gates

theorem represents_step {width count : ℕ} (stored : RowSum.Data) (logical : Data)
    (valid : RowSum.Valid width (count+1) stored)
    (represented : Represents width stored logical) :
    Represents width (RowSum.step stored) (step logical) := by
  have last := RowSum.last_word valid
  have term : addressValue (stored.terms.getLastD []) = logical.terms.getLastD 0 := by
    rw [← represented.terms]
    exact (List.getLastD_map (a := [])).symm
  have termWord : fixedWidth width (logical.terms.getLastD 0) = stored.terms.getLastD [] :=
    (fixedWidth_eq last.2.1 term).symm
  have acc : fixedWidth width logical.accumulator = stored.accumulator :=
    (fixedWidth_eq valid.accumulatorLength represented.accumulator).symm
  refine ⟨?_, represented.next, ?_, ?_⟩
  · change addressValue (Increment.bits stored.next) = logical.next + 1
    rw [Increment.bits_value, represented.next]
  · change stored.terms.dropLast.map addressValue = logical.terms.dropLast
    rw [List.map_dropLast, represented.terms]
  · have suffix : traceBytes width [.add (logical.terms.getLastD 0) logical.accumulator] =
        some (additionTag ++ stored.terms.getLastD [] ++ stored.accumulator) := by
      simp [traceBytes, gateBytes, acc]
      simpa only [List.getLastD_eq_getLast?] using termWord
    simpa [RowSum.step, step, List.append_assoc] using
      traceBytes_append width logical.gates _ represented.gates suffix

theorem represents_iterate {width : ℕ} (count : ℕ) (stored : RowSum.Data) (logical : Data)
    (valid : RowSum.Valid width count stored) (represented : Represents width stored logical) :
    Represents width ((RowSum.step^[count]) stored) ((step^[count]) logical) ∧
      RowSum.Valid width 0 ((RowSum.step^[count]) stored) := by
  induction count generalizing stored logical with
  | zero => exact ⟨represented, valid⟩
  | succ count ih =>
    simpa only [Function.iterate_succ_apply] using
      ih (RowSum.step stored) (step logical) (RowSum.valid_step valid)
        (represents_step stored logical valid represented)

theorem stored_complete_correct {width : ℕ} (stored : RowSum.Data) (logical : Data)
    (valid : RowSum.Valid width stored.terms.length stored)
    (represented : Represents width stored logical) :
    let result := sumTrace logical.terms logical.next logical.accumulator
    addressValue (RowSum.complete stored).next = result.next ∧
      addressValue (RowSum.complete stored).accumulator = result.output ∧
      (RowSum.complete stored).terms = [] ∧
      traceBytes width (logical.gates ++ result.gates) = some (RowSum.complete stored).gates ∧
      RowSum.Valid width 0 (RowSum.complete stored) := by
  obtain ⟨hr, hv⟩ := represents_iterate stored.terms.length stored logical valid represented
  have count : stored.terms.length = logical.terms.length := by
    simpa using congrArg List.length represented.terms
  change Represents width (RowSum.complete stored) ((step^[stored.terms.length]) logical) at hr
  change RowSum.Valid width 0 (RowSum.complete stored) at hv
  rw [count, ← complete, complete_compiles] at hr
  refine ⟨hr.next, hr.accumulator, ?_, hr.gates, hv⟩
  simpa using hv.termsCount

structure Terms where
  next : ℕ
  outputs : List ℕ
  gates : List GateRecord

def compileTerms {v : ℕ} : List (Expression v) → ℕ → (Fin v → ℕ) → Terms
  | [], start, _ => ⟨start, [], []⟩
  | term :: terms, start, ids =>
      let head := HornerTrace.compile term start ids
      let tail := compileTerms terms head.next ids
      ⟨tail.next, head.output :: tail.outputs, head.gates ++ tail.gates⟩

def sumExpression {v : ℕ} : List (Expression v) → Expression v
  | [] => .zero
  | term :: terms => .add term (sumExpression terms)

/-- All term arithmetic precedes the terminal zero; additions then consume
term outputs in reverse order, exactly as in the right-associated tree. -/
theorem compile_sumExpression {v : ℕ} (terms : List (Expression v)) (start : ℕ) (ids : Fin v → ℕ) :
    HornerTrace.compile (sumExpression terms) start ids =
      let compiled := compileTerms terms start ids
      let sum := sumTrace compiled.outputs (compiled.next+1) compiled.next
      ⟨sum.next, sum.output, compiled.gates ++ [.zero] ++ sum.gates⟩ := by
  induction terms generalizing start with
  | nil => simp [sumExpression, HornerTrace.compile, compileTerms, sumTrace]
  | cons term terms ih =>
    simp [sumExpression, HornerTrace.compile, compileTerms, sumTrace, ih, List.append_assoc]

theorem sumExpression_terms {v : ℕ} (terms : List (DyadicTerm v)) :
    sumExpression (terms.map DyadicTerm.expression) = rowExpression terms := by
  induction terms with
  | nil => rfl
  | cons term terms ih => simp [sumExpression, rowExpression, ih]

theorem rowExpression_trace {v n d : ℕ} (terms : List (DyadicTerm v))
    (prior : Circuit n d) (ids : Fin v → Fin d) :
    let compiled := compileTerms (terms.map DyadicTerm.expression) d (fun i => (ids i).val)
    let sum := sumTrace compiled.outputs (compiled.next+1) compiled.next
    (compileExpression (rowExpression terms) prior ids).size = sum.next ∧
      (compileExpression (rowExpression terms) prior ids).output.val = sum.output ∧
      expressionTrace (rowExpression terms) prior ids = compiled.gates ++ [.zero] ++ sum.gates := by
  have h := compile_sumExpression (terms.map DyadicTerm.expression) d (fun i => (ids i).val)
  rw [sumExpression_terms, HornerTrace.compile_correct (rowExpression terms) prior ids] at h
  exact ⟨congrArg HornerTrace.Result.next h, congrArg HornerTrace.Result.output h,
    congrArg HornerTrace.Result.gates h⟩

end Maxwell.Cost.SourceCircuit.RowSumTrace
