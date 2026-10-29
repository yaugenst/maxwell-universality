import Maxwell.Cost.SourceCircuit.AllocationPassData
import Maxwell.Cost.SourceCircuit.TermStore
import Maxwell.Cost.SourceCircuit.FinalizeRow

namespace Maxwell.Cost.SourceCircuit.ArithmeticPass

structure Data where
  next : List Bool
  gates : List Bool
  leaves : List (List Bool)
  terms : List (List Bool)
  outputs : List Bool
  counter : List Bool

def termGateCost {n : ℕ} (r : AllocationPass.Record n) : ℕ :=
  1 + r.bits.length + r.bits.count true + r.negative.toNat

def term {n : ℕ} (r : AllocationPass.Record n) (d : Data) : Data :=
  let result := TermStore.result r.negative r.bits d.next d.gates (d.leaves.take (r.bits.count true))
  ⟨result.next,result.gates,d.leaves.drop (r.bits.count true),
    d.terms ++ [result.accumulator],d.outputs,Increment.bits d.counter⟩

def finish (d : Data) : Data :=
  let result := FinalizeRow.result d.next d.gates d.terms
  ⟨result.next,result.gates,d.leaves,[],d.outputs ++ result.accumulator,[]⟩

def body {n : ℕ} (boundary : Bool) (r : AllocationPass.Record n) (d : Data) : Data :=
  term r (if boundary then finish d else d)

def loop {n : ℕ} : List (AllocationPass.Record n) → List Bool → Data → Data
  | r :: records, boundary :: flags, d => loop records flags (body boundary r d)
  | _, _, d => finish d

def reserve {n : ℕ} (records : List (AllocationPass.Record n)) (flags : List Bool) (d : Data) : ℕ :=
  (records.map termGateCost).sum + records.length + flags.count true + d.terms.length + 1

structure Shape (width : ℕ) (d : Data) : Prop where
  nextLength : d.next.length = width
  leafLength : ∀ word ∈ d.leaves, word.length = width
  termLength : ∀ word ∈ d.terms, word.length = width
  counterValue : addressValue d.counter = d.terms.length
  counterLength : d.counter.length ≤ width

structure Valid {n : ℕ} (width : ℕ) (records : List (AllocationPass.Record n))
    (flags : List Bool) (d : Data) : Prop where
  shape : Shape width d
  flagsLength : flags.length = records.length
  leavesCount : d.leaves.length = AllocationPass.occurrences records
  room : addressValue d.next + reserve records flags d < 2^width

theorem horner_valid {width : ℕ} (bits : List Bool) (d : HornerLoop.Data)
    (h : HornerLoop.Valid width bits d) :
    HornerLoop.Valid width [] (bits.foldr HornerLoop.step d) := by
  induction bits using List.reverseRecOn generalizing d with
  | nil => exact h
  | append_singleton bits bit ih =>
    simpa only [List.foldr_append,List.foldr_cons,List.foldr_nil] using
      ih (HornerLoop.step bit d) (HornerLoop.valid_step width bits bit d h)

theorem term_result_next {n : ℕ} (r : AllocationPass.Record n) (d : Data) :
    addressValue (TermStore.result r.negative r.bits d.next d.gates
      (d.leaves.take (r.bits.count true))).next = addressValue d.next + termGateCost r := by
  unfold TermStore.result HornerTerm.signed
  split <;> simp only [HornerTerm.fold_next,HornerTerm.initial,Increment.bits_value]
  · have hn : r.negative = true := by assumption
    simp only [termGateCost,hn,Bool.toNat_true]
    omega
  · have hn : r.negative = false := by simpa using (show r.negative ≠ true by assumption)
    simp only [termGateCost,hn,Bool.toNat_false]
    omega

theorem term_next {n : ℕ} (r : AllocationPass.Record n) (d : Data) :
    addressValue (term r d).next = addressValue d.next + termGateCost r := term_result_next r d

theorem term_result_valid {n width : ℕ} (r : AllocationPass.Record n) (d : Data)
    (h : Shape width d) (hleaves : r.bits.count true ≤ d.leaves.length)
    (hroom : addressValue d.next + termGateCost r < 2^width) :
    HornerLoop.Valid width [] (TermStore.result r.negative r.bits d.next d.gates
      (d.leaves.take (r.bits.count true))) := by
  have initial := HornerTerm.initial_valid width r.bits d.next d.gates
    (d.leaves.take (r.bits.count true)) h.nextLength
    (by simp [List.length_take,Nat.min_eq_left hleaves])
    (fun word hw => h.leafLength word (List.mem_of_mem_take hw))
    (by unfold termGateCost at hroom; omega)
  have hv := horner_valid r.bits _ initial
  apply HornerTerm.signed_valid width r.negative _ hv
  simpa only [HornerTerm.fold_next,HornerTerm.initial,Increment.bits_value,termGateCost,
    Nat.add_assoc] using hroom

theorem term_shape {n width : ℕ} (r : AllocationPass.Record n) (d : Data)
    (h : Shape width d) (hleaves : r.bits.count true ≤ d.leaves.length)
    (hroom : addressValue d.next + termGateCost r < 2^width)
    (hcounter : d.terms.length+1 < 2^width) : Shape width (term r d) := by
  have hv := term_result_valid r d h hleaves hroom
  refine ⟨hv.nextLength,?_,?_,?_,?_⟩
  · intro word hw
    exact h.leafLength word (List.mem_of_mem_drop hw)
  · intro word hw
    simp only [term,List.mem_append,List.mem_singleton] at hw
    rcases hw with hw | rfl
    · exact h.termLength word hw
    · exact hv.accumulatorLength
  · simp [term,Increment.bits_value,h.counterValue]
  · exact BankArray.increment_length_bound d.counter width h.counterLength (by
      rw [h.counterValue]
      exact hcounter)

theorem row_valid {width : ℕ} (count : ℕ) (d : RowSum.Data) (h : RowSum.Valid width count d) :
    RowSum.Valid width 0 ((RowSum.step^[count]) d) := by
  induction count generalizing d with
  | zero => exact h
  | succ count ih =>
    simpa only [Function.iterate_succ_apply] using ih (RowSum.step d) (RowSum.valid_step h)

theorem row_next (count : ℕ) (d : RowSum.Data) :
    addressValue ((RowSum.step^[count]) d).next = addressValue d.next + count := by
  induction count generalizing d with
  | zero => simp
  | succ count ih =>
    rw [Function.iterate_succ_apply,ih]
    simp [RowSum.step,Increment.bits_value,Nat.add_assoc,Nat.add_comm]

theorem finish_next (d : Data) :
    addressValue (finish d).next = addressValue d.next + 1 + d.terms.length := by
  simpa only [finish,FinalizeRow.result,RowSum.complete,FinalizeRow.initial,Increment.bits_value]
    using row_next d.terms.length (FinalizeRow.initial d.next d.gates d.terms)

theorem finish_result_valid {width : ℕ} (d : Data) (h : Shape width d)
    (hroom : addressValue d.next + 1 + d.terms.length < 2^width) :
    RowSum.Valid width 0 (FinalizeRow.result d.next d.gates d.terms) := by
  apply row_valid d.terms.length
  refine ⟨?_,h.nextLength,rfl,h.termLength,?_⟩
  · change (Increment.bits d.next).length = width
    rw [increment_length d.next (by rw [h.nextLength]; omega),h.nextLength]
  · simpa [FinalizeRow.initial,Increment.bits_value] using hroom

theorem finish_shape {width : ℕ} (d : Data) (h : Shape width d)
    (hroom : addressValue d.next + 1 + d.terms.length < 2^width) : Shape width (finish d) := by
  have hv := finish_result_valid d h hroom
  exact ⟨hv.nextLength,h.leafLength,by simp [finish],by simp [finish,addressValue],by simp [finish]⟩



theorem body_budget {n : ℕ} (boundary : Bool) (r : AllocationPass.Record n)
    (records : List (AllocationPass.Record n)) (flags : List Bool) (d : Data) :
    addressValue (body boundary r d).next + reserve records flags (body boundary r d) =
      addressValue d.next + reserve (r::records) (boundary::flags) d := by
  cases boundary <;> simp only [body,Bool.false_eq_true,ite_false,ite_true]
  · rw [term_next]
    simp [reserve,term]
    omega
  · rw [term_next,finish_next]
    simp [reserve,term,finish]
    omega

theorem valid_body {n width : ℕ} (boundary : Bool) (r : AllocationPass.Record n)
    (records : List (AllocationPass.Record n)) (flags : List Bool) (d : Data)
    (h : Valid width (r::records) (boundary::flags) d) :
    Valid width records flags (body boundary r d) := by
  have count : d.leaves.length = r.bits.count true + AllocationPass.occurrences records := by
    simpa only [AllocationPass.occurrences,List.map_cons,List.sum_cons] using h.leavesCount
  have enough : r.bits.count true ≤ d.leaves.length := by omega
  have room := h.room
  simp only [reserve,List.map_cons,List.sum_cons,List.length_cons] at room
  refine ⟨?_,by simpa using h.flagsLength,?_,?_⟩
  · cases boundary with
    | false =>
      change Shape width (term r d)
      apply term_shape r d h.shape enough
      · simp only [List.count_cons_of_ne (by decide : false ≠ true)] at room
        omega
      · simp only [List.count_cons_of_ne (by decide : false ≠ true)] at room
        omega
    | true =>
      change Shape width (term r (finish d))
      simp only [List.count_cons_self] at room
      have hf := finish_shape d h.shape (by omega)
      apply term_shape r (finish d) hf enough
      · rw [finish_next]
        omega
      · simp only [finish,List.length_nil]
        omega
  · cases boundary <;> simp only [body,Bool.false_eq_true,ite_false,ite_true,term,finish,List.length_drop]
    all_goals omega
  · rw [body_budget]
    exact h.room

structure Finished (width : ℕ) (d : Data) : Prop where
  shape : Shape width d
  leaves : d.leaves = []
  terms : d.terms = []
  counter : d.counter = []
  room : addressValue d.next < 2^width

theorem valid_finish {n width : ℕ} (d : Data) (h : Valid (n := n) width [] [] d) :
    Finished width (finish d) := by
  have room : addressValue d.next + 1 + d.terms.length < 2^width := by
    have hr := h.room
    simp only [reserve,List.map_nil,List.sum_nil,List.length_nil,List.count_nil,
      Nat.zero_add,Nat.add_zero] at hr
    omega
  refine ⟨finish_shape d h.shape room,?_,rfl,rfl,?_⟩
  · change d.leaves = []
    have hc := h.leavesCount
    simpa [AllocationPass.occurrences] using hc
  · rw [finish_next]
    exact room

theorem valid_loop {n width : ℕ} (records : List (AllocationPass.Record n))
    (flags : List Bool) (d : Data) (h : Valid width records flags d) :
    Finished width (loop records flags d) := by
  induction records generalizing flags d with
  | nil =>
    have hf : flags = [] := by simpa using h.flagsLength
    subst flags
    exact valid_finish d h
  | cons r records ih =>
    cases flags with
    | nil => have hf := h.flagsLength; simp at hf
    | cons boundary flags =>
      exact ih flags (body boundary r d) (valid_body boundary r records flags d h)

theorem loop_next {n : ℕ} (records : List (AllocationPass.Record n)) (flags : List Bool)
    (d : Data) (hlen : flags.length = records.length) :
    addressValue (loop records flags d).next = addressValue d.next + reserve records flags d := by
  induction records generalizing flags d with
  | nil =>
    have hf : flags = [] := by simpa using hlen
    subst flags
    simpa [loop,reserve,Nat.add_assoc,Nat.add_comm] using finish_next d
  | cons r records ih =>
    cases flags with
    | nil => simp at hlen
    | cons boundary flags =>
      rw [loop,ih flags (body boundary r d) (by simpa using hlen),body_budget]

theorem finish_outputs_length {width : ℕ} (d : Data) (h : Shape width d)
    (hroom : addressValue d.next + 1 + d.terms.length < 2^width) :
    (finish d).outputs.length = d.outputs.length + width := by
  have hv := finish_result_valid d h hroom
  simpa [finish] using congrArg (fun k => d.outputs.length+k) hv.accumulatorLength

theorem body_outputs_length {n width : ℕ} (boundary : Bool) (r : AllocationPass.Record n)
    (records : List (AllocationPass.Record n)) (flags : List Bool) (d : Data)
    (h : Valid width (r::records) (boundary::flags) d) :
    (body boundary r d).outputs.length = d.outputs.length + boundary.toNat*width := by
  cases boundary with
  | false => simp [body,term]
  | true =>
    have room := h.room
    simp only [reserve,List.map_cons,List.sum_cons,List.length_cons,List.count_cons_self] at room
    simpa [body,term] using finish_outputs_length d h.shape (by omega)

theorem loop_outputs_length {n width : ℕ} (records : List (AllocationPass.Record n))
    (flags : List Bool) (d : Data) (h : Valid width records flags d) :
    (loop records flags d).outputs.length = d.outputs.length + (flags.count true+1)*width := by
  induction records generalizing flags d with
  | nil =>
    have hf : flags = [] := by simpa using h.flagsLength
    subst flags
    have hr := h.room
    simp only [reserve,List.map_nil,List.sum_nil,List.length_nil,List.count_nil,
      Nat.zero_add,Nat.add_zero] at hr
    simpa [loop] using finish_outputs_length d h.shape (by omega)
  | cons r records ih =>
    cases flags with
    | nil => have hf := h.flagsLength; simp at hf
    | cons boundary flags =>
      rw [loop,ih flags (body boundary r d) (valid_body boundary r records flags d h),
        body_outputs_length boundary r records flags d h]
      cases boundary with
      | false => simp
      | true => simp [Nat.add_mul,Nat.add_assoc]; omega

/-- Number of additions spent by all row finalizers, including the last row. -/
def rowAdditions {n : ℕ} : List (AllocationPass.Record n) → List Bool → Data → ℕ
  | r::records, boundary::flags, d =>
      (if boundary then d.terms.length else 0) + rowAdditions records flags (body boundary r d)
  | _, _, d => d.terms.length

theorem rowAdditions_eq {n : ℕ} (records : List (AllocationPass.Record n)) (flags : List Bool)
    (d : Data) (hlen : flags.length = records.length) :
    rowAdditions records flags d = d.terms.length + records.length := by
  induction records generalizing flags d with
  | nil =>
    have hf : flags = [] := by simpa using hlen
    subst flags
    simp [rowAdditions]
  | cons r records ih =>
    cases flags with
    | nil => simp at hlen
    | cons boundary flags =>
      rw [rowAdditions,ih flags (body boundary r d) (by simpa using hlen)]
      cases boundary <;> simp [body,term,finish,Nat.add_assoc] <;> omega



theorem finish_cost_bound {width : ℕ} (d : Data) (h : Shape width d) :
    FinalizeRow.costBound d.terms.length width d.counter.length ≤
      d.terms.length*(101*width+119)+(75*width+103) := by
  have hc := h.counterLength
  unfold FinalizeRow.costBound RowSum.costBound
  nlinarith

/-- Sum of the row-finalizer bounds at their actual term and counter sizes. -/
def rowCost {n : ℕ} (width : ℕ) : List (AllocationPass.Record n) → List Bool → Data → ℕ
  | r::records, boundary::flags, d =>
      (if boundary then FinalizeRow.costBound d.terms.length width d.counter.length else 0) +
        rowCost width records flags (body boundary r d)
  | _, _, d => FinalizeRow.costBound d.terms.length width d.counter.length

theorem rowCost_bound {n width : ℕ} (records : List (AllocationPass.Record n)) (flags : List Bool)
    (d : Data) (h : Valid width records flags d) :
    rowCost width records flags d ≤
      (d.terms.length+records.length)*(101*width+119)+(flags.count true+1)*(75*width+103) := by
  induction records generalizing flags d with
  | nil =>
    have hf : flags = [] := by simpa using h.flagsLength
    subst flags
    simpa [rowCost] using finish_cost_bound d h.shape
  | cons r records ih =>
    cases flags with
    | nil => have hf := h.flagsLength; simp at hf
    | cons boundary flags =>
      have ht := ih flags (body boundary r d) (valid_body boundary r records flags d h)
      have hf := finish_cost_bound d h.shape
      cases boundary with
      | false =>
        simp only [rowCost,Bool.false_eq_true,ite_false,Nat.zero_add]
        simpa [body,term,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ht
      | true =>
        simp only [rowCost,ite_true]
        have hterms : (body true r d).terms.length = 1 := by simp [body,term,finish]
        rw [hterms] at ht
        have bound := Nat.add_le_add hf ht
        convert bound using 1
        simp only [List.length_cons,List.count_cons_self]
        ring

end Maxwell.Cost.SourceCircuit.ArithmeticPass
