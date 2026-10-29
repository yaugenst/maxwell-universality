import Maxwell.Cost.SourceCircuit.TraceBinding
import Maxwell.Cost.SourceCircuit.HornerData

/-! Numeric gate traces expose the exact chronology and output identifier
of the logical compiler without equating its dependent circuit records. -/

namespace Maxwell.Cost.SourceCircuit.HornerTrace
open Logical

set_option backward.isDefEq.respectTransparency false

structure Result where
  next : ℕ
  output : ℕ
  gates : List GateRecord
  deriving DecidableEq

def compile {v : ℕ} (e : Expression v) (start : ℕ) (ids : Fin v → ℕ) : Result :=
  match e with
  | .var i => ⟨start, ids i, []⟩
  | .zero => ⟨start + 1, start, [.zero]⟩
  | .scale w child =>
      let r := compile child start ids
      ⟨r.next + 1, r.next, r.gates ++ [.scale r.output w]⟩
  | .add left right =>
      let l := compile left start ids
      let r := compile right l.next ids
      ⟨r.next + 1, r.next, l.gates ++ r.gates ++ [.add l.output r.output]⟩

theorem compile_correct {v n d : ℕ} (e : Expression v) (prior : Circuit n d)
    (ids : Fin v → Fin d) :
    compile e d (fun i => (ids i).val) =
      ⟨(compileExpression e prior ids).size, (compileExpression e prior ids).output.val,
        expressionTrace e prior ids⟩ := by
  induction e generalizing d with
  | var i => rfl
  | zero => rfl
  | scale w child ih =>
    rw [compile, ih prior ids]
    rfl
  | add left right ihl ihr =>
    let l := compileExpression left prior ids
    have right := ihr l.circuit (fun i => Fin.castLE l.size_le (ids i))
    simp only [Fin.val_castLE] at right
    rw [compile, ihl prior ids]
    dsimp only
    rw [right]
    rfl

theorem compile_rename {v w : ℕ} (f : Fin v → Fin w) (e : Expression v)
    (start : ℕ) (ids : Fin w → ℕ) :
    compile (e.rename f) start ids = compile e start (fun i => ids (f i)) := by
  induction e generalizing start with
  | var i => rfl
  | zero => rfl
  | scale w child ih => simp [Expression.rename, compile, ih]
  | add left right ihl ihr => simp [Expression.rename, compile, ihl, ihr]

structure OccurrenceResult where
  result : Result
  remaining : List ℕ
  deriving DecidableEq

def compileOccurrences {v : ℕ} (e : Expression v) (start : ℕ) (leaves : List ℕ) : OccurrenceResult :=
  match e with
  | .var _ => ⟨⟨start, leaves.headD 0, []⟩, leaves.tail⟩
  | .zero => ⟨⟨start + 1, start, [.zero]⟩, leaves⟩
  | .scale w child =>
      let r := compileOccurrences child start leaves
      ⟨⟨r.result.next + 1, r.result.next,
        r.result.gates ++ [.scale r.result.output w]⟩, r.remaining⟩
  | .add left right =>
      let l := compileOccurrences left start leaves
      let r := compileOccurrences right l.result.next l.remaining
      ⟨⟨r.result.next + 1, r.result.next,
        l.result.gates ++ r.result.gates ++ [.add l.result.output r.result.output]⟩, r.remaining⟩

theorem ofFn_split {a b : ℕ} (ids : Fin (a+b) → ℕ) :
    List.ofFn ids = List.ofFn (fun i => ids (Fin.castAdd b i)) ++
      List.ofFn (fun i => ids (Fin.natAdd a i)) := by
  rw [← List.ofFn_fin_append]
  congr 1
  funext i
  exact Fin.addCases (fun j => by simp) (fun j => by simp) i

theorem compileOccurrences_linearized {v : ℕ} (e : Expression v)
    (start : ℕ) (ids : Fin e.leafCount → ℕ) (following : List ℕ) :
    compileOccurrences e start (List.ofFn ids ++ following) =
      ⟨compile e.linearized start ids, following⟩ := by
  induction e generalizing start following with
  | var i =>
    simp [compileOccurrences, Expression.linearized, Expression.leafCount, compile, List.ofFn_succ]
  | zero => rfl
  | scale w child ih =>
    simp [compileOccurrences, Expression.linearized, compile, ih]
  | add left right ihl ihr =>
    have leaves := ofFn_split ids
    rw [leaves, List.append_assoc]
    simp [compileOccurrences, Expression.linearized, compile, compile_rename, ihl, ihr]

theorem compileOccurrences_correct {v n d : ℕ} (e : Expression v)
    (prior : Circuit n d) (ids : Fin e.leafCount → Fin d) (following : List ℕ) :
    compileOccurrences e d ((List.ofFn ids).map Fin.val ++ following) =
      ⟨⟨(compileExpression e.linearized prior ids).size,
          (compileExpression e.linearized prior ids).output.val,
          expressionTrace e.linearized prior ids⟩, following⟩ := by
  rw [List.map_ofFn, compileOccurrences_linearized]
  exact congrArg (fun r => OccurrenceResult.mk r following) (compile_correct e.linearized prior ids)

structure Data where
  next : ℕ
  accumulator : ℕ
  gates : List GateRecord
  leaves : List ℕ
  deriving DecidableEq

def step (bit : Bool) (d : Data) : Data :=
  if bit then {
    next := d.next + 2
    accumulator := d.next + 1
    gates := d.gates ++ [.add (d.leaves.getLastD 0) d.accumulator, .scale d.next (1/2)]
    leaves := d.leaves.dropLast }
  else {
    next := d.next + 1
    accumulator := d.next
    gates := d.gates ++ [.scale d.accumulator (1/2)]
    leaves := d.leaves }

def initial (start : ℕ) (gates : List GateRecord) (leaves : List ℕ) : Data :=
  ⟨start+1, start, gates ++ [.zero], leaves⟩

theorem horner_fold {v : ℕ} (input : Fin v) (bits : List Bool)
    (start : ℕ) (gates : List GateRecord) (lower leaves : List ℕ)
    (hlen : leaves.length = bits.count true) :
    bits.foldr step (initial start gates (lower ++ leaves)) =
      let result := (compileOccurrences (Horner.expression input bits) start leaves).result
      ⟨result.next, result.output, gates ++ result.gates, lower⟩ := by
  induction bits generalizing lower leaves with
  | nil =>
    have hl : leaves = [] := by simpa using hlen
    subst leaves
    simp [initial, Horner.expression, compileOccurrences]
  | cons bit bits ih =>
    cases bit with
    | false =>
      have hl : leaves.length = bits.count true := by simpa using hlen
      simp [List.foldr_cons, ih lower leaves hl, step, Horner.expression,
        compileOccurrences, List.append_assoc]
    | true =>
      cases leaves with
      | nil => simp at hlen
      | cons leaf leaves =>
        have hl : leaves.length = bits.count true := by simpa using hlen
        have hh := ih (lower ++ [leaf]) leaves hl
        have hi : initial start gates (lower ++ leaf :: leaves) =
            initial start gates ((lower ++ [leaf]) ++ leaves) := by simp [List.append_assoc]
        rw [List.foldr_cons, hi, hh]
        simp [step, Horner.expression, compileOccurrences, List.append_assoc, Nat.add_assoc]

theorem horner_fold_correct {v n d : ℕ} (input : Fin v) (bits : List Bool)
    (prior : Circuit n d) (ids : Fin (Horner.expression input bits).leafCount → Fin d)
    (gates : List GateRecord) (lower : List ℕ)
    (count : (Horner.expression input bits).leafCount = bits.count true) :
    bits.foldr step (initial d gates (lower ++ (List.ofFn ids).map Fin.val)) =
      ⟨(compileExpression (Horner.expression input bits).linearized prior ids).size,
        (compileExpression (Horner.expression input bits).linearized prior ids).output.val,
        gates ++ expressionTrace (Horner.expression input bits).linearized prior ids, lower⟩ := by
  rw [horner_fold input bits d gates lower _ (by simp [count])]
  have h := compileOccurrences_correct (Horner.expression input bits) prior ids []
  simp only [List.append_nil] at h
  rw [h]

theorem horner_leafCount {v : ℕ} (input : Fin v) (bits : List Bool) :
    (Horner.expression input bits).leafCount = bits.count true := by
  induction bits with
  | nil => rfl
  | cons bit bits ih =>
    cases bit <;> simp [Horner.expression, Expression.leafCount, ih, Nat.add_comm]

structure Represents (width : ℕ) (stored : HornerLoop.Data) (logical : Data) : Prop where
  next : addressValue stored.next = logical.next
  accumulator : addressValue stored.accumulator = logical.accumulator
  leaves : stored.leaves.map addressValue = logical.leaves
  gates : traceBytes width logical.gates = some stored.gates

theorem represents_initial (width start : ℕ) (gates : List GateRecord)
    (archive : List Bool) (leaves : List ℕ) (stored : HornerLoop.Data)
    (hn : addressValue stored.next = start + 1)
    (ha : addressValue stored.accumulator = start)
    (hl : stored.leaves.map addressValue = leaves)
    (hg : stored.gates = archive ++ zeroTag)
    (ht : traceBytes width gates = some archive) :
    Represents width stored (initial start gates leaves) := by
  refine ⟨hn, ha, hl, ?_⟩
  rw [hg]
  exact traceBytes_append width gates [.zero] ht (by simp [traceBytes, gateBytes])

theorem represents_step {width : ℕ} (remaining : List Bool) (bit : Bool)
    (stored : HornerLoop.Data) (logical : Data)
    (valid : HornerLoop.Valid width (remaining ++ [bit]) stored)
    (represented : Represents width stored logical) :
    Represents width (HornerLoop.step bit stored) (step bit logical) := by
  have acc : fixedWidth width logical.accumulator = stored.accumulator :=
    (fixedWidth_eq valid.accumulatorLength represented.accumulator).symm
  have next : fixedWidth width logical.next = stored.next :=
    (fixedWidth_eq valid.nextLength represented.next).symm
  cases bit with
  | false =>
    refine ⟨?_, represented.next, represented.leaves, ?_⟩
    · simpa [HornerLoop.step, step, Increment.bits_value] using represented.next
    · have suffix : traceBytes width [.scale logical.accumulator (1/2)] =
          some (halfTag ++ stored.accumulator) := by
        norm_num [traceBytes, gateBytes, acc]
      simpa [HornerLoop.step, step, List.append_assoc] using
        traceBytes_append width logical.gates _ represented.gates suffix
  | true =>
    have last := HornerLoop.last_word valid
    have leaf : addressValue (stored.leaves.getLastD []) = logical.leaves.getLastD 0 := by
      rw [← represented.leaves]
      exact (List.getLastD_map (a := [])).symm
    have leafWord : fixedWidth width (logical.leaves.getLastD 0) = stored.leaves.getLastD [] :=
      (fixedWidth_eq last.2.1 leaf).symm
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [HornerLoop.step, step, Increment.bits_value, represented.next, Nat.add_assoc]
    · simp [HornerLoop.step, step, Increment.bits_value, represented.next]
    · change stored.leaves.dropLast.map addressValue = logical.leaves.dropLast
      rw [List.map_dropLast, represented.leaves]
    · have suffix : traceBytes width
          [.add (logical.leaves.getLastD 0) logical.accumulator, .scale logical.next (1/2)] =
          some (additionTag ++ stored.leaves.getLastD [] ++ stored.accumulator ++ halfTag ++ stored.next) := by
        norm_num [traceBytes, gateBytes, leafWord, acc, next, List.append_assoc]
        simpa only [List.getLastD_eq_getLast?] using leafWord
      simpa [HornerLoop.step, step, List.append_assoc] using
        traceBytes_append width logical.gates _ represented.gates suffix

theorem represents_fold {width : ℕ} (bits : List Bool) (stored : HornerLoop.Data) (logical : Data)
    (valid : HornerLoop.Valid width bits stored)
    (represented : Represents width stored logical) :
    Represents width (bits.foldr HornerLoop.step stored) (bits.foldr step logical) ∧
      HornerLoop.Valid width [] (bits.foldr HornerLoop.step stored) := by
  induction bits using List.reverseRecOn generalizing stored logical with
  | nil => exact ⟨represented, valid⟩
  | append_singleton bits bit ih =>
    simpa only [List.foldr_append, List.foldr_cons, List.foldr_nil] using
      ih (HornerLoop.step bit stored) (step bit logical)
        (HornerLoop.valid_step width bits bit stored valid)
        (represents_step bits bit stored logical valid represented)

theorem stored_fold_correct {width v n d : ℕ} (input : Fin v) (bits : List Bool)
    (prior : Circuit n d) (ids : Fin (Horner.expression input bits).leafCount → Fin d)
    (realization : RationalRealization prior) (stored : HornerLoop.Data)
    (valid : HornerLoop.Valid width bits stored)
    (represented : Represents width stored
      (initial d realization.code.trace ((List.ofFn ids).map Fin.val))) :
    let result := bits.foldr HornerLoop.step stored
    let compiled := compileExpression (Horner.expression input bits).linearized prior ids
    addressValue result.next = compiled.size ∧
      addressValue result.accumulator = compiled.output.val ∧ result.leaves = [] ∧
      traceBytes width
        (compileExpression_rational (Horner.expression input bits).linearized prior ids realization).code.trace =
          some result.gates ∧ HornerLoop.Valid width [] result := by
  obtain ⟨hr, hv⟩ := represents_fold bits stored _ valid represented
  have pure := horner_fold_correct input bits prior ids realization.code.trace []
    (horner_leafCount input bits)
  simp only [List.nil_append] at pure
  rw [pure] at hr
  refine ⟨hr.next, hr.accumulator, ?_, ?_, hv⟩
  · have hl := hv.leavesCount
    simpa using hl
  · rw [compileExpression_trace]
    exact hr.gates

end Maxwell.Cost.SourceCircuit.HornerTrace
