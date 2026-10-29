import Maxwell.Cost.SourceCircuit.ArithmeticData
import Maxwell.Cost.SourceCircuit.RowSumTrace

namespace Maxwell.Cost.SourceCircuit.ArithmeticTrace
open Logical

set_option backward.isDefEq.respectTransparency false

def expression {n : ℕ} (r : AllocationPass.Record n) : Expression n :=
  (DyadicTerm.mk r.bits r.negative r.column).expression

theorem expression_leafCount {n : ℕ} (r : AllocationPass.Record n) :
    (expression r).leafCount = r.bits.count true := by
  cases hn : r.negative <;>
    simp [expression,DyadicTerm.expression,hn,Expression.leafCount,HornerTrace.horner_leafCount]

theorem occurrences_append {v : ℕ} (e : Expression v) (start : ℕ) (leaves following : List ℕ)
    (hlen : leaves.length = e.leafCount) :
    HornerTrace.compileOccurrences e start (leaves ++ following) =
      ⟨(HornerTrace.compileOccurrences e start leaves).result,following⟩ := by
  obtain ⟨ids,hids⟩ : ∃ ids : Fin e.leafCount → ℕ, List.ofFn ids = leaves := by
    rw [← hlen]
    exact ⟨leaves.get,List.ofFn_get leaves⟩
  have h := HornerTrace.compileOccurrences_linearized e start ids following
  have hzero := HornerTrace.compileOccurrences_linearized e start ids []
  simp only [hids,List.append_nil] at h hzero
  rw [h,hzero]

theorem occurrences_take {v : ℕ} (e : Expression v) (start : ℕ) (leaves : List ℕ)
    (hlen : e.leafCount ≤ leaves.length) :
    HornerTrace.compileOccurrences e start leaves =
      ⟨(HornerTrace.compileOccurrences e start (leaves.take e.leafCount)).result,
        leaves.drop e.leafCount⟩ := by
  simpa only [List.take_append_drop] using occurrences_append e start
    (leaves.take e.leafCount) (leaves.drop e.leafCount) (by simp [List.length_take,Nat.min_eq_left hlen])

def signed (negative : Bool) (d : HornerTrace.Data) : HornerTrace.Data :=
  if negative then ⟨d.next+1,d.next,d.gates ++ [.scale d.accumulator (-1)],d.leaves⟩ else d

theorem represents_signed {width : ℕ} (negative : Bool) (stored : HornerLoop.Data)
    (logical : HornerTrace.Data) (valid : HornerLoop.Valid width [] stored)
    (represented : HornerTrace.Represents width stored logical) :
    HornerTrace.Represents width (HornerTerm.signed negative stored) (signed negative logical) := by
  cases negative with
  | false => exact represented
  | true =>
    have acc : fixedWidth width logical.accumulator = stored.accumulator :=
      (fixedWidth_eq valid.accumulatorLength represented.accumulator).symm
    refine ⟨?_,represented.next,represented.leaves,?_⟩
    · change addressValue (Increment.bits stored.next) = logical.next+1
      rw [Increment.bits_value,represented.next]
    · have suffix : traceBytes width [.scale logical.accumulator (-1)] =
          some (negativeTag ++ stored.accumulator) := by norm_num [traceBytes,gateBytes,acc]
      simpa [HornerTerm.signed,signed,List.append_assoc] using
        traceBytes_append width logical.gates _ represented.gates suffix

theorem term_result_represents {n width : ℕ} (r : AllocationPass.Record n) (d : ArithmeticPass.Data)
    (shape : ArithmeticPass.Shape width d) (enough : r.bits.count true ≤ d.leaves.length)
    (room : addressValue d.next + ArithmeticPass.termGateCost r < 2^width)
    (gates : List GateRecord) (archive : traceBytes width gates = some d.gates) :
    let compiled := HornerTrace.compileOccurrences (expression r) (addressValue d.next)
      (d.leaves.map addressValue)
    HornerTrace.Represents width
      (TermStore.result r.negative r.bits d.next d.gates (d.leaves.take (r.bits.count true)))
      ⟨compiled.result.next,compiled.result.output,gates ++ compiled.result.gates,[]⟩ := by
  let used := d.leaves.take (r.bits.count true)
  have usedCount : used.length = r.bits.count true := by simp [used,List.length_take,Nat.min_eq_left enough]
  have initial := HornerTerm.initial_valid width r.bits d.next d.gates used shape.nextLength usedCount
    (fun word hw => shape.leafLength word (List.mem_of_mem_take hw))
    (by unfold ArithmeticPass.termGateCost at room; omega)
  have initialRep : HornerTrace.Represents width (HornerTerm.initial d.next d.gates used)
      (HornerTrace.initial (addressValue d.next) gates (used.map addressValue)) :=
    HornerTrace.represents_initial width (addressValue d.next) gates d.gates (used.map addressValue)
      _ (Increment.bits_value d.next) rfl rfl rfl archive
  obtain ⟨rep,valid⟩ := HornerTrace.represents_fold r.bits _ _ initial initialRep
  have fold := HornerTrace.horner_fold r.column r.bits (addressValue d.next) gates []
    (used.map addressValue) (by simpa using usedCount)
  simp only [List.nil_append] at fold
  rw [fold] at rep
  have signedRep := represents_signed r.negative _ _ valid rep
  have take := occurrences_take (expression r) (addressValue d.next) (d.leaves.map addressValue)
    (by simpa [expression_leafCount] using enough)
  rw [take]
  simp only [expression_leafCount,← List.map_take]
  cases hn : r.negative <;>
    simpa [TermStore.result,expression,DyadicTerm.expression,hn,HornerTrace.compileOccurrences,
      signed,List.append_assoc,used] using signedRep

structure Data where
  next : ℕ
  gates : List GateRecord
  leaves : List ℕ
  terms : List ℕ
  outputs : List ℕ
  deriving DecidableEq

def term {n : ℕ} (r : AllocationPass.Record n) (d : Data) : Data :=
  let result := HornerTrace.compileOccurrences (expression r) d.next d.leaves
  ⟨result.result.next,d.gates ++ result.result.gates,result.remaining,
    d.terms ++ [result.result.output],d.outputs⟩

def finish (d : Data) : Data :=
  let result := RowSumTrace.sumTrace d.terms (d.next+1) d.next
  ⟨result.next,d.gates ++ [.zero] ++ result.gates,d.leaves,[],d.outputs ++ [result.output]⟩

def body {n : ℕ} (boundary : Bool) (r : AllocationPass.Record n) (d : Data) : Data :=
  term r (if boundary then finish d else d)

def loop {n : ℕ} : List (AllocationPass.Record n) → List Bool → Data → Data
  | r::records,boundary::flags,d => loop records flags (body boundary r d)
  | _,_,d => finish d

structure Represents (width : ℕ) (stored : ArithmeticPass.Data) (logical : Data) : Prop where
  next : addressValue stored.next = logical.next
  gates : traceBytes width logical.gates = some stored.gates
  leaves : stored.leaves.map addressValue = logical.leaves
  terms : stored.terms.map addressValue = logical.terms
  outputs : stored.outputs = logical.outputs.flatMap (fixedWidth width)

theorem represents_term {n width : ℕ} (r : AllocationPass.Record n)
    (stored : ArithmeticPass.Data) (logical : Data)
    (shape : ArithmeticPass.Shape width stored) (enough : r.bits.count true ≤ stored.leaves.length)
    (room : addressValue stored.next + ArithmeticPass.termGateCost r < 2^width)
    (represented : Represents width stored logical) :
    Represents width (ArithmeticPass.term r stored) (term r logical) := by
  have compiled := term_result_represents r stored shape enough room logical.gates represented.gates
  dsimp only at compiled
  rw [represented.next,represented.leaves] at compiled
  have take := occurrences_take (expression r) logical.next logical.leaves (by
    rw [← represented.leaves,List.length_map,expression_leafCount]
    exact enough)
  refine ⟨compiled.next,compiled.gates,?_,?_,represented.outputs⟩
  · simp only [ArithmeticPass.term,term]
    rw [take]
    simp only [expression_leafCount,List.map_drop,represented.leaves]
  · simp only [ArithmeticPass.term,term,List.map_append,List.map_cons,List.map_nil,
      represented.terms,compiled.accumulator]

theorem represents_finish {width : ℕ} (stored : ArithmeticPass.Data) (logical : Data)
    (shape : ArithmeticPass.Shape width stored)
    (room : addressValue stored.next+1+stored.terms.length < 2^width)
    (represented : Represents width stored logical) :
    Represents width (ArithmeticPass.finish stored) (finish logical) := by
  let initial := FinalizeRow.initial stored.next stored.gates stored.terms
  let logicalInitial : RowSumTrace.Data :=
    ⟨logical.next+1,logical.next,logical.gates ++ [.zero],logical.terms⟩
  have valid : RowSum.Valid width stored.terms.length initial := by
    refine ⟨?_,shape.nextLength,rfl,shape.termLength,?_⟩
    · change (Increment.bits stored.next).length = width
      rw [increment_length stored.next (by rw [shape.nextLength]; omega),shape.nextLength]
    · simpa [initial,FinalizeRow.initial,Increment.bits_value] using room
  have rep : RowSumTrace.Represents width initial logicalInitial := by
    refine ⟨?_,represented.next,represented.terms,?_⟩
    · change addressValue (Increment.bits stored.next) = logical.next+1
      rw [Increment.bits_value,represented.next]
    · exact traceBytes_append width logical.gates [.zero] represented.gates (by simp [traceBytes,gateBytes])
  obtain ⟨next,output,_,gates,validFinal⟩ := RowSumTrace.stored_complete_correct initial logicalInitial valid rep
  have word := fixedWidth_eq validFinal.accumulatorLength output
  refine ⟨next,gates,represented.leaves,rfl,?_⟩
  change stored.outputs ++ (RowSum.complete initial).accumulator =
    (logical.outputs ++ [(RowSumTrace.sumTrace logical.terms (logical.next+1) logical.next).output]).flatMap _
  rw [represented.outputs,word]
  simp [logicalInitial]



theorem represents_body {n width : ℕ} (boundary : Bool) (r : AllocationPass.Record n)
    (records : List (AllocationPass.Record n)) (flags : List Bool)
    (stored : ArithmeticPass.Data) (logical : Data)
    (valid : ArithmeticPass.Valid width (r::records) (boundary::flags) stored)
    (represented : Represents width stored logical) :
    Represents width (ArithmeticPass.body boundary r stored) (body boundary r logical) := by
  have room := valid.room
  simp only [ArithmeticPass.reserve,List.map_cons,List.sum_cons,List.length_cons] at room
  have enough : r.bits.count true ≤ stored.leaves.length := by
    have hc := valid.leavesCount
    simp only [AllocationPass.occurrences,List.map_cons,List.sum_cons] at hc
    omega
  cases boundary with
  | false =>
    exact represents_term r stored logical valid.shape enough (by omega) represented
  | true =>
    have finishRoom : addressValue stored.next+1+stored.terms.length < 2^width := by omega
    apply represents_term r (ArithmeticPass.finish stored) (finish logical)
      (ArithmeticPass.finish_shape stored valid.shape finishRoom) enough
    · rw [ArithmeticPass.finish_next]
      simp only [List.count_cons_self] at room
      omega
    · exact represents_finish stored logical valid.shape finishRoom represented

theorem represents_loop {n width : ℕ} (records : List (AllocationPass.Record n)) (flags : List Bool)
    (stored : ArithmeticPass.Data) (logical : Data) (valid : ArithmeticPass.Valid width records flags stored)
    (represented : Represents width stored logical) :
    Represents width (ArithmeticPass.loop records flags stored) (loop records flags logical) := by
  induction records generalizing flags stored logical with
  | nil =>
    have hf : flags = [] := by simpa using valid.flagsLength
    subst flags
    apply represents_finish stored logical valid.shape _ represented
    have hr := valid.room
    simp only [ArithmeticPass.reserve,List.map_nil,List.sum_nil,List.length_nil,List.count_nil,
      Nat.zero_add,Nat.add_zero] at hr
    omega
  | cons r records ih =>
    cases flags with
    | nil => have hf := valid.flagsLength; simp at hf
    | cons boundary flags =>
      exact ih flags (ArithmeticPass.body boundary r stored) (body boundary r logical)
        (ArithmeticPass.valid_body boundary r records flags stored valid)
        (represents_body boundary r records flags stored logical valid represented)

structure ForestResult where
  next : ℕ
  outputs : List ℕ
  gates : List GateRecord
  remaining : List ℕ
  deriving DecidableEq

def compileForestOccurrences {v : ℕ} : List (Expression v) → ℕ → List ℕ → ForestResult
  | [],start,leaves => ⟨start,[],[],leaves⟩
  | e::es,start,leaves =>
      let head := HornerTrace.compileOccurrences e start leaves
      let tail := compileForestOccurrences es head.result.next head.remaining
      ⟨tail.next,head.result.output::tail.outputs,head.result.gates++tail.gates,tail.remaining⟩

def terms {n : ℕ} : List (AllocationPass.Record n) → Data → Data
  | [],d => d
  | r::records,d => terms records (term r d)

def row {n : ℕ} (records : List (AllocationPass.Record n)) (d : Data) : Data := finish (terms records d)

def rowExpression {n : ℕ} (records : List (AllocationPass.Record n)) : Expression n :=
  Logical.rowExpression (records.map fun r => DyadicTerm.mk r.bits r.negative r.column)

theorem rowExpression_eq_sum {n : ℕ} (records : List (AllocationPass.Record n)) :
    rowExpression records = RowSumTrace.sumExpression (records.map expression) := by
  rw [rowExpression,← RowSumTrace.sumExpression_terms,List.map_map]
  rfl

theorem terms_compiles {n : ℕ} (records : List (AllocationPass.Record n)) (d : Data) :
    terms records d =
      let compiled := compileForestOccurrences (records.map expression) d.next d.leaves
      ⟨compiled.next,d.gates++compiled.gates,compiled.remaining,d.terms++compiled.outputs,d.outputs⟩ := by
  induction records generalizing d with
  | nil => simp [terms,compileForestOccurrences]
  | cons r records ih => simp [terms,ih,term,compileForestOccurrences,List.append_assoc]

theorem compile_sumExpression_occurrences {v : ℕ} (es : List (Expression v))
    (start : ℕ) (leaves : List ℕ) :
    HornerTrace.compileOccurrences (RowSumTrace.sumExpression es) start leaves =
      let compiled := compileForestOccurrences es start leaves
      let sum := RowSumTrace.sumTrace compiled.outputs (compiled.next+1) compiled.next
      ⟨⟨sum.next,sum.output,compiled.gates++[.zero]++sum.gates⟩,compiled.remaining⟩ := by
  induction es generalizing start leaves with
  | nil => simp [RowSumTrace.sumExpression,HornerTrace.compileOccurrences,compileForestOccurrences,
      RowSumTrace.sumTrace]
  | cons e es ih =>
    simp [RowSumTrace.sumExpression,HornerTrace.compileOccurrences,compileForestOccurrences,
      RowSumTrace.sumTrace,ih,List.append_assoc]

theorem row_compiles {n : ℕ} (records : List (AllocationPass.Record n)) (d : Data)
    (empty : d.terms = []) :
    row records d =
      let compiled := HornerTrace.compileOccurrences (rowExpression records) d.next d.leaves
      ⟨compiled.result.next,d.gates++compiled.result.gates,compiled.remaining,[],d.outputs++[compiled.result.output]⟩ := by
  rw [row,terms_compiles,rowExpression_eq_sum,compile_sumExpression_occurrences]
  simp [finish,empty,List.append_assoc]

def rows {n : ℕ} : List (List (AllocationPass.Record n)) → Data → Data
  | [],d => d
  | records::rest,d => rows rest (row records d)

theorem rows_compiles {n : ℕ} (records : List (List (AllocationPass.Record n))) (d : Data)
    (empty : d.terms = []) :
    rows records d =
      let compiled := compileForestOccurrences (records.map rowExpression) d.next d.leaves
      ⟨compiled.next,d.gates++compiled.gates,compiled.remaining,[],d.outputs++compiled.outputs⟩ := by
  induction records generalizing d with
  | nil => cases d; simp_all [rows,compileForestOccurrences]
  | cons records rest ih =>
    rw [rows,ih (row records d) (by simp [row,finish]),row_compiles records d empty]
    simp [compileForestOccurrences,List.append_assoc]

/-- Markers before later nonempty rows; the first row is handled separately. -/
def blockFlags {n : ℕ} : List (AllocationPass.Record n) → List Bool
  | [] => []
  | _::rest => true::List.replicate rest.length false

def followingFlags {n : ℕ} (rows : List (List (AllocationPass.Record n))) : List Bool :=
  rows.flatMap blockFlags

theorem loop_false_prefix {n : ℕ} (first rest : List (AllocationPass.Record n))
    (flags : List Bool) (d : Data) :
    loop (first++rest) (List.replicate first.length false++flags) d = loop rest flags (terms first d) := by
  induction first generalizing d with
  | nil => rfl
  | cons r records ih =>
    simpa [List.replicate_succ,loop,body,terms] using ih (term r d)

theorem loop_following {n : ℕ} (records : List (List (AllocationPass.Record n)))
    (d : Data) (nonempty : ∀ row ∈ records, row ≠ []) :
    loop records.flatten (followingFlags records) d = rows records (finish d) := by
  induction records generalizing d with
  | nil => rfl
  | cons records rest ih =>
    cases records with
    | nil => exact False.elim (nonempty [] (by simp) rfl)
    | cons r records =>
      change loop ((r::records)++rest.flatten)
        ((true::List.replicate records.length false)++followingFlags rest) d = _
      simp only [List.cons_append,loop,body,ite_true]
      rw [loop_false_prefix,ih _ (fun row hr => nonempty row (by simp [hr]))]
      rfl

theorem loop_rows {n : ℕ} (first : List (AllocationPass.Record n))
    (rest : List (List (AllocationPass.Record n))) (d : Data)
    (nonempty : ∀ row ∈ rest, row ≠ []) :
    loop (first++rest.flatten) (List.replicate first.length false++followingFlags rest) d =
      rows (first::rest) d := by
  rw [loop_false_prefix,loop_following rest _ nonempty]
  rfl



theorem loop_after_first_rows {n : ℕ} (first : AllocationPass.Record n)
    (firstTail : List (AllocationPass.Record n)) (rest : List (List (AllocationPass.Record n)))
    (d : Data) (nonempty : ∀ row ∈ rest, row ≠ []) :
    loop (firstTail++rest.flatten) (List.replicate firstTail.length false++followingFlags rest)
      (term first d) = rows ((first::firstTail)::rest) d := by
  rw [loop_false_prefix,loop_following rest _ nonempty]
  rfl

theorem compileTerms_rename {v w : ℕ} (f : Fin v → Fin w) (es : List (Expression v))
    (start : ℕ) (ids : Fin w → ℕ) :
    RowSumTrace.compileTerms (es.map (Expression.rename f)) start ids =
      RowSumTrace.compileTerms es start (fun i => ids (f i)) := by
  induction es generalizing start with
  | nil => rfl
  | cons e es ih => simp [RowSumTrace.compileTerms,HornerTrace.compile_rename,ih]

theorem compileTerms_correct {v n d : ℕ} (es : List (Expression v)) (prior : Circuit n d)
    (ids : Fin v → Fin d) :
    RowSumTrace.compileTerms es d (fun i => (ids i).val) =
      ⟨(compileForest es prior ids).size,(compileForest es prior ids).outputs.map Fin.val,
        forestTrace es prior ids⟩ := by
  induction es generalizing d with
  | nil => rfl
  | cons e es ih =>
    have tail := ih (compileExpression e prior ids).circuit
      (fun i => Fin.castLE (compileExpression e prior ids).size_le (ids i))
    simp only [Fin.val_castLE] at tail
    rw [RowSumTrace.compileTerms,HornerTrace.compile_correct]
    dsimp only
    rw [tail]
    rfl

theorem forestOccurrences_linearized {v : ℕ} (es : List (Expression v)) (start : ℕ)
    (ids : Fin (forestLeafCount es) → ℕ) (following : List ℕ) :
    compileForestOccurrences es start (List.ofFn ids ++ following) =
      let compiled := RowSumTrace.compileTerms (linearizedRows es) start ids
      ⟨compiled.next,compiled.outputs,compiled.gates,following⟩ := by
  induction es generalizing start following with
  | nil => rfl
  | cons e es ih =>
    have split := HornerTrace.ofFn_split ids
    rw [split,List.append_assoc]
    simp only [compileForestOccurrences]
    rw [HornerTrace.compileOccurrences_linearized]
    dsimp only
    rw [ih]
    simp only [linearizedRows,RowSumTrace.compileTerms,HornerTrace.compile_rename,compileTerms_rename]

theorem forestOccurrences_correct {v n d : ℕ} (es : List (Expression v)) (prior : Circuit n d)
    (ids : Fin (forestLeafCount es) → Fin d) (following : List ℕ) :
    compileForestOccurrences es d ((List.ofFn ids).map Fin.val ++ following) =
      ⟨(compileForest (linearizedRows es) prior ids).size,
        (compileForest (linearizedRows es) prior ids).outputs.map Fin.val,
        forestTrace (linearizedRows es) prior ids,following⟩ := by
  rw [List.map_ofFn,forestOccurrences_linearized]
  simp only [Function.comp_def]
  rw [compileTerms_correct]



/-- The actual byte-level arithmetic pass compiles an entire row list, with
preorder occurrence leaves and the exact chronological logical forest trace. -/
theorem stored_rows_correct {v n d width : ℕ}
    (first : List (AllocationPass.Record v)) (rest : List (List (AllocationPass.Record v)))
    (prior : Circuit n d)
    (ids : Fin (forestLeafCount ((first::rest).map rowExpression)) → Fin d)
    (initialGates : List GateRecord) (beforeOutputs : List ℕ) (stored : ArithmeticPass.Data)
    (valid : ArithmeticPass.Valid width (first++rest.flatten)
      (List.replicate first.length false++followingFlags rest) stored)
    (nonempty : ∀ row ∈ rest, row ≠ [])
    (next : addressValue stored.next = d)
    (gates : traceBytes width initialGates = some stored.gates)
    (leaves : stored.leaves.map addressValue = (List.ofFn ids).map Fin.val)
    (terms : stored.terms = [])
    (outputs : stored.outputs = beforeOutputs.flatMap (fixedWidth width)) :
    let final := ArithmeticPass.loop (first++rest.flatten)
      (List.replicate first.length false++followingFlags rest) stored
    let compiled := compileForest (linearizedRows ((first::rest).map rowExpression)) prior ids
    addressValue final.next = compiled.size ∧
      traceBytes width (initialGates++forestTrace (linearizedRows ((first::rest).map rowExpression)) prior ids) =
        some final.gates ∧
      final.outputs = (beforeOutputs++compiled.outputs.map Fin.val).flatMap (fixedWidth width) ∧
      final.leaves = [] ∧ final.terms = [] := by
  let initial : Data := ⟨d,initialGates,(List.ofFn ids).map Fin.val,[],beforeOutputs⟩
  have represented : Represents width stored initial :=
    ⟨next,gates,leaves,by simp [initial,terms],outputs⟩
  have hr := represents_loop (first++rest.flatten)
    (List.replicate first.length false++followingFlags rest) stored initial valid represented
  rw [loop_rows first rest initial nonempty,rows_compiles (first::rest) initial rfl] at hr
  dsimp only [initial] at hr
  have compiled := forestOccurrences_correct ((first::rest).map rowExpression) prior ids []
  simp only [List.append_nil] at compiled
  rw [compiled] at hr
  exact ⟨hr.next,hr.gates,hr.outputs,by simpa using hr.leaves,by simpa using hr.terms⟩

/-- Specialization after the logical copy bank: the retained archive is the
entire copied-forest rational trace, and retained output words are its IDs. -/
theorem stored_copied_rows_correct {n width : ℕ}
    (first : List (AllocationPass.Record n)) (rest : List (List (AllocationPass.Record n)))
    (stored : ArithmeticPass.Data)
    (valid : ArithmeticPass.Valid width (first++rest.flatten)
      (List.replicate first.length false++followingFlags rest) stored)
    (nonempty : ∀ row ∈ rest, row ≠ [])
    (next : addressValue stored.next = (forestCopies ((first::rest).map rowExpression)).bank.size)
    (gates : traceBytes width ((CopyBank.initial n).trace
      (List.ofFn (forestSources ((first::rest).map rowExpression)))) = some stored.gates)
    (leaves : stored.leaves.map addressValue =
      (List.ofFn (copiedForestInputs ((first::rest).map rowExpression))).map Fin.val)
    (terms : stored.terms = []) (outputs : stored.outputs = []) :
    let final := ArithmeticPass.loop (first++rest.flatten)
      (List.replicate first.length false++followingFlags rest) stored
    let compiled := compileCopiedForest ((first::rest).map rowExpression)
    addressValue final.next = compiled.size ∧
      traceBytes width (compileCopiedForest_rational ((first::rest).map rowExpression)).code.trace =
        some final.gates ∧
      final.outputs = (compiled.outputs.map Fin.val).flatMap (fixedWidth width) ∧
      final.leaves = [] ∧ final.terms = [] := by
  have h := stored_rows_correct first rest (forestCopies ((first::rest).map rowExpression)).bank.circuit
    (copiedForestInputs ((first::rest).map rowExpression)) _ [] stored valid nonempty next gates leaves terms
    (by simpa using outputs)
  simpa only [compileCopiedForest_trace,compileCopiedForest,List.nil_append] using h

end Maxwell.Cost.SourceCircuit.ArithmeticTrace
