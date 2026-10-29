import Maxwell.Logical.RationalSparse

/-! Chronological gate records of the exact rational compiler. This is a
specification of the emitted stream, independent of the machine executing
the compiler. Gate identifiers are their positions after the input block. -/

namespace Maxwell.Logical

set_option backward.isDefEq.respectTransparency false

inductive GateRecord where
  | zero
  | scale (parent : ℕ) (weight : ℚ)
  | add (left right : ℕ)
  deriving DecidableEq

def RationalCode.trace {n d : ℕ} : RationalCode n d → List GateRecord
  | .input => []
  | .zero c => c.trace ++ [.zero]
  | .scale c p w => c.trace ++ [.scale p.val w]
  | .add c l r => c.trace ++ [.add l.val r.val]

theorem RationalCode.trace_length {n d : ℕ} (c : RationalCode n d) :
    n + c.trace.length = d := by
  induction c <;> simp_all [trace] <;> omega

def GateRecord.entries (id : ℕ) : GateRecord → List RationalCode.Entry
  | .zero => [⟨id,id,1⟩]
  | .scale p w => [⟨id,id,1⟩,⟨id,p,-w⟩]
  | .add l r => [⟨id,id,1⟩,⟨id,l,-1⟩,⟨id,r,-1⟩]

/-- Later gates precede earlier gates in the sparse coefficient stream. -/
def traceEntries (start : ℕ) : List GateRecord → List RationalCode.Entry
  | [] => []
  | gate :: rest => traceEntries (start+1) rest ++ gate.entries start

theorem traceEntries_append (start : ℕ) (a b : List GateRecord) :
    traceEntries start (a ++ b) = traceEntries (start+a.length) b ++ traceEntries start a := by
  induction a generalizing start with
  | nil => simp [traceEntries]
  | cons g a ih => simp [traceEntries,ih,List.append_assoc,Nat.add_left_comm,Nat.add_comm]

theorem RationalCode.entries_trace {n d : ℕ} (c : RationalCode n d) :
    c.entries = traceEntries n c.trace ++ (RationalCode.input (n := n)).entries := by
  induction c with
  | input => rfl
  | zero c ih =>
    simp [entries,trace,traceEntries_append,trace_length,traceEntries,GateRecord.entries,ih]
  | scale c p w ih =>
    simp [entries,trace,traceEntries_append,trace_length,traceEntries,GateRecord.entries,ih]
  | add c l r ih =>
    simp [entries,trace,traceEntries_append,trace_length,traceEntries,GateRecord.entries,ih]

def CopyBank.trace {n : ℕ} (bank : CopyBank n) : List (Fin n) → List GateRecord
  | [] => []
  | i :: rest => [.scale (bank.root i).val 1,.scale (bank.root i).val 1] ++
      (bank.splitRoot i).trace rest

theorem CopyBank.split_trace {n : ℕ} (bank : CopyBank n)
    (r : RationalRealization bank.circuit) (i : Fin n) :
    (bank.splitRoot_rational r i).code.trace = r.code.trace ++
      [.scale (bank.root i).val 1,.scale (bank.root i).val 1] := by
  simp [splitRoot_rational,RationalRealization.copy,RationalCode.trace,
    List.append_assoc]

theorem CopyBank.allocate_trace {n : ℕ} (bank : CopyBank n)
    (r : RationalRealization bank.circuit) (requests : List (Fin n)) :
    (bank.allocate_rational requests r).code.trace = r.code.trace ++ bank.trace requests := by
  induction requests generalizing bank with
  | nil => simp [allocate_rational,trace]
  | cons i rest ih =>
    simpa [allocate_rational,trace,split_trace,List.append_assoc] using
      ih (bank.splitRoot i) (bank.splitRoot_rational r i)

def expressionTrace {n d v : ℕ} (e : Expression v) (prior : Circuit n d)
    (ids : Fin v → Fin d) : List GateRecord :=
  match e with
  | .var _ => []
  | .zero => [.zero]
  | .scale w child => expressionTrace child prior ids ++
      [.scale (compileExpression child prior ids).output.val w]
  | .add left right =>
      let l := compileExpression left prior ids
      let r := compileExpression right l.circuit (fun i => Fin.castLE l.size_le (ids i))
      expressionTrace left prior ids ++
        expressionTrace right l.circuit (fun i => Fin.castLE l.size_le (ids i)) ++
        [.add l.output.val r.output.val]

theorem compileExpression_trace {n d v : ℕ} (e : Expression v) (prior : Circuit n d)
    (ids : Fin v → Fin d) (r : RationalRealization prior) :
    (compileExpression_rational e prior ids r).code.trace = r.code.trace ++ expressionTrace e prior ids := by
  induction e generalizing d with
  | var i => simp [compileExpression_rational,expressionTrace]
  | zero => rfl
  | scale w child ih =>
    simp [compileExpression_rational,expressionTrace,RationalRealization.scale,RationalCode.trace,
      ih,List.append_assoc]
  | add left right ihl ihr =>
    simp [compileExpression_rational,expressionTrace,RationalRealization.add,RationalCode.trace,
      ihl,ihr,List.append_assoc]

def forestTrace {n d v : ℕ} (es : List (Expression v)) (prior : Circuit n d)
    (ids : Fin v → Fin d) : List GateRecord :=
  match es with
  | [] => []
  | e :: rest =>
      let h := compileExpression e prior ids
      expressionTrace e prior ids ++
        forestTrace rest h.circuit (fun i => Fin.castLE h.size_le (ids i))

theorem compileForest_trace {n d v : ℕ} (es : List (Expression v)) (prior : Circuit n d)
    (ids : Fin v → Fin d) (r : RationalRealization prior) :
    (compileForest_rational es prior ids r).code.trace = r.code.trace ++ forestTrace es prior ids := by
  induction es generalizing d with
  | nil => simp [compileForest_rational,forestTrace]
  | cons e rest ih =>
    simp [compileForest_rational,forestTrace,ih,compileExpression_trace,List.append_assoc]

theorem compileCopiedForest_trace {n : ℕ} (rows : List (Expression n)) :
    (compileCopiedForest_rational rows).code.trace =
      (CopyBank.initial n).trace (List.ofFn (forestSources rows)) ++
        forestTrace (linearizedRows rows) (forestCopies rows).bank.circuit (copiedForestInputs rows) := by
  simp [compileCopiedForest_rational,compileForest_trace,CopyBank.allocate_trace,
    RationalRealization.input,RationalCode.trace]

end Maxwell.Logical
