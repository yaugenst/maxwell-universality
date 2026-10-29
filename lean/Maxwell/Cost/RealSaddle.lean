import Maxwell.Cost.RealSparse

/-! Actual finite-code sparse saddle emission. Real coefficients and natural
coordinates have separate charged output instructions. The emitted lists
below are correctness specifications, not executable host instructions. -/

namespace Maxwell.Cost.RealSaddle

open RealSparse (execute execute_sound execute_add entryAt)

set_option maxRecDepth 20000

noncomputable def input (entries : List SparseEntry) (rows columns padding : ℕ) : RAMInput where
  words a := (entryAt entries a).value
  indices a := if a = 0 then entries.length else if a = 1 then rows else
    if a = 2 then columns else if a = 3 then padding else
    if (a - 4) % 2 = 0 then (entryAt entries ((a - 4) / 2)).row
    else (entryAt entries ((a - 4) / 2)).column

@[simp] theorem input_count (es : List SparseEntry) (r c p : ℕ) : (input es r c p).indices 0 = es.length := by simp [input]
@[simp] theorem input_rows (es : List SparseEntry) (r c p : ℕ) : (input es r c p).indices 1 = r := by simp [input]
@[simp] theorem input_columns (es : List SparseEntry) (r c p : ℕ) : (input es r c p).indices 2 = c := by simp [input]
@[simp] theorem input_padding (es : List SparseEntry) (r c p : ℕ) : (input es r c p).indices 3 = p := by simp [input]
@[simp] theorem input_value (es : List SparseEntry) (r c p k : ℕ) : (input es r c p).words k = (entryAt es k).value := rfl

theorem input_row (es : List SparseEntry) (r c p k : ℕ) :
    (input es r c p).indices (4 + 2 * k) = (entryAt es k).row := by
  have h : 4 + 2 * k ≠ 0 ∧ 4 + 2 * k ≠ 1 ∧ 4 + 2 * k ≠ 2 ∧ 4 + 2 * k ≠ 3 := by omega
  simp [input, h]

theorem input_column (es : List SparseEntry) (r c p k : ℕ) :
    (input es r c p).indices (5 + 2 * k) = (entryAt es k).column := by
  have h : 5 + 2 * k ≠ 0 ∧ 5 + 2 * k ≠ 1 ∧ 5 + 2 * k ≠ 2 ∧ 5 + 2 * k ≠ 3 := by omega
  have hs : 5 + 2 * k - 4 = 2 * k + 1 := by omega
  simp [input, h, hs, Nat.add_div, Nat.add_mod]

noncomputable def valueStack (es : List SparseEntry) (out : List ℝ) : List ℝ :=
  (es.map SparseEntry.value).reverse ++ out

def indexStack (es : List SparseEntry) (out : List ℕ) : List ℕ :=
  (es.flatMap fun e => [e.row, e.column]).reverse ++ out

@[simp] theorem valueStack_nil (o : List ℝ) : valueStack [] o = o := rfl
@[simp] theorem indexStack_nil (o : List ℕ) : indexStack [] o = o := rfl
@[simp] theorem valueStack_cons (e : SparseEntry) (es : List SparseEntry) (o : List ℝ) :
    valueStack (e :: es) o = valueStack es (e.value :: o) := by simp [valueStack, List.append_assoc]
@[simp] theorem indexStack_cons (e : SparseEntry) (es : List SparseEntry) (o : List ℕ) :
    indexStack (e :: es) o = indexStack es (e.column :: e.row :: o) := by simp [indexStack, List.append_assoc]

theorem valueStack_append (a b : List SparseEntry) (o : List ℝ) :
    valueStack (a ++ b) o = valueStack b (valueStack a o) := by simp [valueStack, List.append_assoc]
theorem indexStack_append (a b : List SparseEntry) (o : List ℕ) :
    indexStack (a ++ b) o = indexStack b (indexStack a o) := by simp [indexStack, List.append_assoc]

noncomputable def diagonal (start : ℕ) : ℕ → List SparseEntry
  | 0 => []
  | n + 1 => ⟨start, start, 1⟩ :: diagonal (start + 1) n

noncomputable def pairs (rows : ℕ) (es : List SparseEntry) (start : ℕ) : ℕ → List SparseEntry
  | 0 => []
  | n + 1 =>
      let e := entryAt es start
      ⟨e.row, rows + e.column, e.value⟩ :: ⟨rows + e.column, e.row, e.value⟩ :: pairs rows es (start + 1) n

noncomputable def entries (rows columns padding : ℕ) (es : List SparseEntry) : List SparseEntry :=
  diagonal 0 rows ++ pairs rows es 0 es.length ++ diagonal (rows + columns) padding

/-- Forty-four instructions, independent of every dimension and count. -/
def program : Machine := ⟨[
  .indexLiteral 0 0, .indexLiteral 1 1, .inputIndex 2 0, .inputIndex 3 1,
  .indexLiteral 7 2, .inputIndex 4 7, .indexLiteral 7 3, .inputIndex 5 7,
  .indexLiteral 6 0, .literal 0 1,
  .branchIndexLE 3 6 16 11, .outputIndex 6, .outputIndex 6, .output 0,
  .indexAdd 6 6 1, .jump 10,
  .indexLiteral 6 0, .indexLiteral 7 4,
  .branchIndexLE 2 6 33 19,
  .inputIndex 8 7, .indexAdd 7 7 1, .inputIndex 9 7, .indexAdd 9 3 9,
  .input 0 6, .outputIndex 8, .outputIndex 9, .output 0,
  .outputIndex 9, .outputIndex 8, .output 0,
  .indexAdd 6 6 1, .indexAdd 7 7 1, .jump 18,
  .indexLiteral 6 0, .indexAdd 7 3 4, .literal 0 1,
  .branchIndexLE 5 6 43 37,
  .indexAdd 8 7 6, .outputIndex 8, .outputIndex 8, .output 0,
  .indexAdd 6 6 1, .jump 36, .halt]⟩

def Common (s : RAMState) (m r c p : ℕ) : Prop :=
  s.indices 1 = 1 ∧ s.indices 2 = m ∧ s.indices 3 = r ∧ s.indices 4 = c ∧ s.indices 5 = p

def DiagonalReady (s : RAMState) (m r c p k : ℕ) : Prop :=
  Common s m r c p ∧ s.pc = 10 ∧ s.indices 6 = k ∧ s.words 0 = 1

noncomputable def initialized (m r c p : ℕ) : RAMState :=
  let s := RAMState.initial.setIndex 0 0
  let s := s.setIndex 1 1
  let s := s.setIndex 2 m
  let s := s.setIndex 3 r
  let s := s.setIndex 7 2
  let s := s.setIndex 4 c
  let s := s.setIndex 7 3
  let s := s.setIndex 5 p
  let s := s.setIndex 6 0
  s.setWord 0 1

theorem initialize_steps (es : List SparseEntry) (r c p : ℕ) (tape : ℕ → Bool) :
    execute (program.next (input es r c p) tape) 10 RAMState.initial = some (initialized es.length r c p) := by
  simp [execute, program, Machine.next, initialized, RAMState.initial, RAMState.setIndex, RAMState.setWord]

theorem initialized_ready (m r c p : ℕ) : DiagonalReady (initialized m r c p) m r c p 0 := by
  simp [DiagonalReady, Common, initialized, RAMState.initial, RAMState.setIndex, RAMState.setWord]

noncomputable def diagonalAdvanced (s : RAMState) : RAMState :=
  {s with pc := 10, indices := Function.update s.indices 6 (s.indices 6 + 1), output := 1 :: s.output, indexOutput := s.indices 6 :: s.indices 6 :: s.indexOutput}

theorem diagonal_cycle (es : List SparseEntry) (r c p : ℕ) (tape : ℕ → Bool)
    (s : RAMState) (k : ℕ) (h : DiagonalReady s es.length r c p k) (hk : k < r) :
    execute (program.next (input es r c p) tape) 6 s = some (diagonalAdvanced s) := by
  rcases h with ⟨⟨h1, _, hr, _, _⟩, hpc, hi, hw⟩
  have hn : ¬ r ≤ k := by omega
  simp [execute, program, Machine.next, hpc, h1, hr, hi, hw, hn, diagonalAdvanced, RAMState.setIndex]

theorem diagonalAdvanced_ready (s : RAMState) (m r c p k : ℕ) (h : DiagonalReady s m r c p k) :
    DiagonalReady (diagonalAdvanced s) m r c p (k + 1) := by
  rcases h with ⟨⟨h1, hm, hr, hc, hp⟩, _, hi, hw⟩
  simp [DiagonalReady, Common, diagonalAdvanced, h1, hm, hr, hc, hp, hi, hw]

theorem diagonal_scan (es : List SparseEntry) (r c p : ℕ) (tape : ℕ → Bool)
    (remaining : ℕ) (s : RAMState) (k : ℕ) (h : DiagonalReady s es.length r c p k)
    (hcount : k + remaining = r) :
    ∃ final : RAMState,
      Steps (program.next (input es r c p) tape) (6 * remaining) s final ∧
      DiagonalReady final es.length r c p r ∧
      final.output = valueStack (diagonal k remaining) s.output ∧
      final.indexOutput = indexStack (diagonal k remaining) s.indexOutput ∧
      final.randomCursor = s.randomCursor := by
  induction remaining generalizing s k with
  | zero =>
    have hk : k = r := by omega
    subst k
    exact ⟨s, Steps.refl s, h, rfl, rfl, rfl⟩
  | succ remaining ih =>
    have hk : k < r := by omega
    obtain ⟨f, hf, hfr, hfo, hfi, hfc⟩ := ih (diagonalAdvanced s) (k + 1)
      (diagonalAdvanced_ready s _ r c p k h) (by omega)
    refine ⟨f, ?_, hfr, ?_, ?_, hfc⟩
    · convert (execute_sound _ (diagonal_cycle es r c p tape s k h hk)).trans hf using 1
      omega
    · simpa [diagonal, diagonalAdvanced] using hfo
    · simpa [diagonal, diagonalAdvanced, h.2.2.1] using hfi

def PairReady (s : RAMState) (m r c p k : ℕ) : Prop :=
  Common s m r c p ∧ s.pc = 18 ∧ s.indices 6 = k ∧ s.indices 7 = 4 + 2 * k

noncomputable def pairInitialized (s : RAMState) : RAMState :=
  (({s with pc := 16}).setIndex 6 0).setIndex 7 4

theorem pair_initialize (es : List SparseEntry) (r c p : ℕ) (tape : ℕ → Bool)
    (s : RAMState) (h : DiagonalReady s es.length r c p r) :
    execute (program.next (input es r c p) tape) 3 s = some (pairInitialized s) := by
  rcases h with ⟨⟨_, _, hr, _, _⟩, hpc, hi, _⟩
  simp [execute, program, Machine.next, hpc, hr, hi, pairInitialized, RAMState.setIndex]

theorem pairInitialized_ready (s : RAMState) (m r c p : ℕ) (h : Common s m r c p) :
    PairReady (pairInitialized s) m r c p 0 := by
  rcases h with ⟨h1, hm, hr, hc, hp⟩
  simp [PairReady, Common, pairInitialized, RAMState.setIndex, h1, hm, hr, hc, hp]

noncomputable def pairMiddle (s : RAMState) (e : SparseEntry) : RAMState :=
  let t := {s with pc := 19}
  let t := t.setIndex 8 e.row
  let t := t.setIndex 7 (s.indices 7 + 1)
  let t := t.setIndex 9 e.column
  let t := t.setIndex 9 (s.indices 3 + e.column)
  let t := t.setWord 0 e.value
  {t with pc := 25, indexOutput := e.row :: s.indexOutput}

noncomputable def pairAdvanced (s : RAMState) (e : SparseEntry) : RAMState :=
  let t := pairMiddle s e
  let t := t.setIndex 6 (s.indices 6 + 1)
  let t := t.setIndex 7 (s.indices 7 + 2)
  {t with pc := 18, output := e.value :: e.value :: s.output, indexOutput := e.row :: (s.indices 3 + e.column) :: (s.indices 3 + e.column) :: e.row :: s.indexOutput}

set_option maxHeartbeats 1400000 in
theorem pair_cycle (es : List SparseEntry) (r c p : ℕ) (tape : ℕ → Bool)
    (s : RAMState) (k : ℕ) (h : PairReady s es.length r c p k) (hk : k < es.length) :
    execute (program.next (input es r c p) tape) 15 s = some (pairAdvanced s (entryAt es k)) := by
  rcases h with ⟨⟨h1, hm, hr, _, _⟩, hpc, hi, ha⟩
  have hn : ¬ es.length ≤ k := by omega
  have haddr : 4 + 2 * k + 1 = 5 + 2 * k := by omega
  have hf : execute (program.next (input es r c p) tape) 7 s = some (pairMiddle s (entryAt es k)) := by
    simp (config := { maxSteps := 100000 }) [execute, program, Machine.next, hpc, h1, hm, hr, hi, ha,
      hn, haddr, input_row, input_column, pairMiddle, RAMState.setIndex, RAMState.setWord]
  rw [show 15 = 7 + 8 from rfl, execute_add, hf, Option.bind_some]
  simp (config := { maxSteps := 100000 }) [execute, program, Machine.next, h1, hr, hi, ha,
    pairMiddle, pairAdvanced, RAMState.setIndex, RAMState.setWord, Nat.add_assoc]

theorem pairAdvanced_ready (s : RAMState) (m r c p k : ℕ) (h : PairReady s m r c p k) (e : SparseEntry) :
    PairReady (pairAdvanced s e) m r c p (k + 1) := by
  rcases h with ⟨⟨h1, hm, hr, hc, hp⟩, _, hi, ha⟩
  simp [PairReady, Common, pairAdvanced, pairMiddle, RAMState.setIndex, RAMState.setWord,
    h1, hm, hr, hc, hp, hi, ha]
  omega

theorem pair_scan (es : List SparseEntry) (r c p : ℕ) (tape : ℕ → Bool)
    (remaining : ℕ) (s : RAMState) (k : ℕ) (h : PairReady s es.length r c p k)
    (hcount : k + remaining = es.length) :
    ∃ final : RAMState,
      Steps (program.next (input es r c p) tape) (15 * remaining) s final ∧
      PairReady final es.length r c p es.length ∧
      final.output = valueStack (pairs r es k remaining) s.output ∧
      final.indexOutput = indexStack (pairs r es k remaining) s.indexOutput ∧
      final.randomCursor = s.randomCursor := by
  induction remaining generalizing s k with
  | zero =>
    have hk : k = es.length := by omega
    subst k
    exact ⟨s, Steps.refl s, h, rfl, rfl, rfl⟩
  | succ remaining ih =>
    have hk : k < es.length := by omega
    obtain ⟨f, hf, hfr, hfo, hfi, hfc⟩ := ih (pairAdvanced s (entryAt es k)) (k + 1)
      (pairAdvanced_ready s _ r c p k h _) (by omega)
    refine ⟨f, ?_, hfr, ?_, ?_, hfc⟩
    · convert (execute_sound _ (pair_cycle es r c p tape s k h hk)).trans hf using 1
      omega
    · simpa [pairs, pairAdvanced] using hfo
    · simpa [pairs, pairAdvanced, h.1.2.2.1] using hfi

def PaddingReady (s : RAMState) (m r c p k : ℕ) : Prop :=
  Common s m r c p ∧ s.pc = 36 ∧ s.indices 6 = k ∧ s.indices 7 = r + c ∧ s.words 0 = 1

noncomputable def paddingInitialized (s : RAMState) : RAMState :=
  ((({s with pc := 33}).setIndex 6 0).setIndex 7 (s.indices 3 + s.indices 4)).setWord 0 1

theorem padding_initialize (es : List SparseEntry) (r c p : ℕ) (tape : ℕ → Bool)
    (s : RAMState) (h : PairReady s es.length r c p es.length) :
    execute (program.next (input es r c p) tape) 4 s = some (paddingInitialized s) := by
  rcases h with ⟨⟨_, hm, _, _, _⟩, hpc, hi, _⟩
  simp [execute, program, Machine.next, hpc, hm, hi, paddingInitialized, RAMState.setIndex, RAMState.setWord]

theorem paddingInitialized_ready (s : RAMState) (m r c p : ℕ) (h : Common s m r c p) :
    PaddingReady (paddingInitialized s) m r c p 0 := by
  rcases h with ⟨h1, hm, hr, hc, hp⟩
  simp [PaddingReady, Common, paddingInitialized, RAMState.setIndex, RAMState.setWord, h1, hm, hr, hc, hp]

noncomputable def paddingAdvanced (s : RAMState) : RAMState :=
  let t := s.setIndex 8 (s.indices 7 + s.indices 6)
  let t := t.setIndex 6 (s.indices 6 + 1)
  {t with pc := 36, output := 1 :: s.output, indexOutput := (s.indices 7 + s.indices 6) :: (s.indices 7 + s.indices 6) :: s.indexOutput}

theorem padding_cycle (es : List SparseEntry) (r c p : ℕ) (tape : ℕ → Bool)
    (s : RAMState) (k : ℕ) (h : PaddingReady s es.length r c p k) (hk : k < p) :
    execute (program.next (input es r c p) tape) 7 s = some (paddingAdvanced s) := by
  rcases h with ⟨⟨h1, _, _, _, hp⟩, hpc, hi, ha, hw⟩
  have hn : ¬ p ≤ k := by omega
  simp [execute, program, Machine.next, hpc, h1, hp, hi, ha, hw, hn, paddingAdvanced, RAMState.setIndex]

theorem paddingAdvanced_ready (s : RAMState) (m r c p k : ℕ) (h : PaddingReady s m r c p k) :
    PaddingReady (paddingAdvanced s) m r c p (k + 1) := by
  rcases h with ⟨⟨h1, hm, hr, hc, hp⟩, _, hi, ha, hw⟩
  simp [PaddingReady, Common, paddingAdvanced, RAMState.setIndex, h1, hm, hr, hc, hp, hi, ha, hw]

theorem padding_scan (es : List SparseEntry) (r c p : ℕ) (tape : ℕ → Bool)
    (remaining : ℕ) (s : RAMState) (k : ℕ) (h : PaddingReady s es.length r c p k)
    (hcount : k + remaining = p) :
    ∃ final : RAMState,
      Steps (program.next (input es r c p) tape) (7 * remaining) s final ∧
      PaddingReady final es.length r c p p ∧
      final.output = valueStack (diagonal (r + c + k) remaining) s.output ∧
      final.indexOutput = indexStack (diagonal (r + c + k) remaining) s.indexOutput ∧
      final.randomCursor = s.randomCursor := by
  induction remaining generalizing s k with
  | zero =>
    have hk : k = p := by omega
    subst k
    exact ⟨s, Steps.refl s, h, rfl, rfl, rfl⟩
  | succ remaining ih =>
    have hk : k < p := by omega
    obtain ⟨f, hf, hfr, hfo, hfi, hfc⟩ := ih (paddingAdvanced s) (k + 1)
      (paddingAdvanced_ready s _ r c p k h) (by omega)
    refine ⟨f, ?_, hfr, ?_, ?_, hfc⟩
    · convert (execute_sound _ (padding_cycle es r c p tape s k h hk)).trans hf using 1
      omega
    · simpa [diagonal, paddingAdvanced, Nat.add_assoc] using hfo
    · simpa [diagonal, paddingAdvanced, h.2.2.1, h.2.2.2.1, Nat.add_assoc] using hfi

theorem finish (es : List SparseEntry) (r c p : ℕ) (tape : ℕ → Bool)
    (s : RAMState) (h : PaddingReady s es.length r c p p) :
    Terminates (program.next (input es r c p) tape) 1 s {s with pc := 43} := by
  rcases h with ⟨⟨_, _, _, _, hp⟩, hpc, hi, _, _⟩
  apply Terminates.step (t := {s with pc := 43})
  · simp [program, Machine.next, hpc, hp, hi]
  · exact Terminates.halt _ (by simp [program, Machine.next])

/-- The output is the chronological list of saddle records, with both
coordinates and coefficient explicitly emitted for every record. -/
theorem terminates (es : List SparseEntry) (r c p : ℕ) (tape : ℕ → Bool) :
    ∃ final : RAMState,
      Terminates (program.next (input es r c p) tape) (15 * es.length + 6 * r + 7 * p + 18)
        RAMState.initial final ∧
      final.output.reverse = (entries r c p es).map SparseEntry.value ∧
      final.indexOutput.reverse = (entries r c p es).flatMap (fun e => [e.row, e.column]) ∧
      final.randomCursor = 0 := by
  have hi := execute_sound _ (initialize_steps es r c p tape)
  obtain ⟨d, hd, hdr, hdo, hdi, hdc⟩ := diagonal_scan es r c p tape r
    (initialized es.length r c p) 0 (initialized_ready _ r c p) (by omega)
  have hp := execute_sound _ (pair_initialize es r c p tape d hdr)
  obtain ⟨b, hb, hbr, hbo, hbi, hbc⟩ := pair_scan es r c p tape es.length
    (pairInitialized d) 0 (pairInitialized_ready d _ r c p hdr.1) (by omega)
  have hq := execute_sound _ (padding_initialize es r c p tape b hbr)
  obtain ⟨q, hqq, hqr, hqo, hqi, hqc⟩ := padding_scan es r c p tape p
    (paddingInitialized b) 0 (paddingInitialized_ready b _ r c p hbr.1) (by omega)
  refine ⟨{q with pc := 43}, ?_, ?_, ?_, hqc.trans (hbc.trans hdc)⟩
  · convert ((((hi.trans hd).trans hp).trans hb).trans hq).trans hqq |>.terminates
      (finish es r c p tape q hqr) using 1
    omega
  · change q.output.reverse = _
    rw [hqo]
    change (valueStack (diagonal (r + c + 0) p) b.output).reverse = _
    rw [hbo]
    change (valueStack (diagonal (r + c + 0) p) (valueStack (pairs r es 0 es.length) d.output)).reverse = _
    rw [hdo]
    change (valueStack (diagonal (r + c + 0) p) (valueStack (pairs r es 0 es.length)
      (valueStack (diagonal 0 r) []))).reverse = _
    simp [entries, valueStack, List.append_assoc]
  · change q.indexOutput.reverse = _
    rw [hqi]
    change (indexStack (diagonal (r + c + 0) p) b.indexOutput).reverse = _
    rw [hbi]
    change (indexStack (diagonal (r + c + 0) p) (indexStack (pairs r es 0 es.length) d.indexOutput)).reverse = _
    rw [hdi]
    change (indexStack (diagonal (r + c + 0) p) (indexStack (pairs r es 0 es.length)
      (indexStack (diagonal 0 r) []))).reverse = _
    simp [entries, indexStack, List.append_assoc]

theorem run (es : List SparseEntry) (r c p : ℕ) (tape : ℕ → Bool) :
    ∃ final : RAMState,
      (program.run (input es r c p) tape (15 * es.length + 6 * r + 7 * p + 19)).finished = some final ∧
      (program.run (input es r c p) tape (15 * es.length + 6 * r + 7 * p + 19)).instructions =
        15 * es.length + 6 * r + 7 * p + 18 ∧
      final.output.reverse = (entries r c p es).map SparseEntry.value ∧
      final.indexOutput.reverse = (entries r c p es).flatMap (fun e => [e.row, e.column]) := by
  obtain ⟨final, ht, ho, hi, _⟩ := terminates es r c p tape
  obtain ⟨hf, hc⟩ := runCapped_of_terminates _ ht
  exact ⟨final, hf, hc, ho, hi⟩

@[simp] theorem diagonal_length (start n : ℕ) : (diagonal start n).length = n := by
  induction n generalizing start with
  | zero => rfl
  | succ n ih => simp [diagonal, ih]

@[simp] theorem pairs_length (r : ℕ) (es : List SparseEntry) (start n : ℕ) :
    (pairs r es start n).length = 2 * n := by
  induction n generalizing start with
  | zero => rfl
  | succ n ih => simp [pairs, ih]; omega

theorem entries_length (r c p : ℕ) (es : List SparseEntry) :
    (entries r c p es).length = r + 2 * es.length + p := by simp [entries, Nat.add_assoc]

theorem linear_cost (es : List SparseEntry) (r : ℕ) (hr : r ≤ es.length) :
    15 * es.length + 6 * r + 7 * es.length + 18 ≤ 28 * es.length + 18 := by omega

/-- Sparse coordinate summation, used only to identify the emitted matrix. -/
noncomputable def coefficient (es : List SparseEntry) (i j : ℕ) : ℝ :=
  (es.map (fun e => if e.row = i ∧ e.column = j then e.value else 0)).sum

@[simp] theorem coefficient_nil (i j : ℕ) : coefficient [] i j = 0 := rfl
@[simp] theorem coefficient_cons (e : SparseEntry) (es : List SparseEntry) (i j : ℕ) :
    coefficient (e :: es) i j = (if e.row = i ∧ e.column = j then e.value else 0) + coefficient es i j := rfl

theorem coefficient_append (a b : List SparseEntry) (i j : ℕ) :
    coefficient (a ++ b) i j = coefficient a i j + coefficient b i j := by simp [coefficient]

theorem diagonal_symmetric (start n i j : ℕ) :
    coefficient (diagonal start n) i j = coefficient (diagonal start n) j i := by
  induction n generalizing start with
  | zero => rfl
  | succ n ih =>
    simp only [diagonal, coefficient_cons]
    rw [ih]
    congr 1
    simp only [and_comm]

theorem pairs_symmetric (r : ℕ) (es : List SparseEntry) (start n i j : ℕ) :
    coefficient (pairs r es start n) i j = coefficient (pairs r es start n) j i := by
  induction n generalizing start with
  | zero => rfl
  | succ n ih =>
    simp only [pairs, coefficient_cons]
    rw [ih]
    have h1 : ((entryAt es start).row = i ∧ r + (entryAt es start).column = j) ↔
        (r + (entryAt es start).column = j ∧ (entryAt es start).row = i) := and_comm
    have h2 : (r + (entryAt es start).column = i ∧ (entryAt es start).row = j) ↔
        ((entryAt es start).row = j ∧ r + (entryAt es start).column = i) := and_comm
    simp only [h1, h2]
    ring

theorem entries_symmetric (r c p : ℕ) (es : List SparseEntry) (i j : ℕ) :
    coefficient (entries r c p es) i j = coefficient (entries r c p es) j i := by
  simp only [entries, coefficient_append]
  rw [diagonal_symmetric 0 r i j, pairs_symmetric r es 0 es.length i j,
    diagonal_symmetric (r + c) p i j]

/-- The emitted list and the sparse verifier use the same matrix semantics. -/
theorem rectangularMatrix_eq_coefficient (rows columns : ℕ) (es : List SparseEntry)
    (i : Fin rows) (j : Fin columns) :
    RealSparse.rectangularMatrix rows columns es i j = coefficient es i.val j.val := by
  unfold RealSparse.rectangularMatrix coefficient
  rw [← List.ofFn_getElem_eq_map es (fun e => if e.row = i.val ∧ e.column = j.val then e.value else 0)]
  rw [List.sum_ofFn, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k _
  simp [entryAt, k.isLt]

theorem matrix_symmetric (r c p : ℕ) (es : List SparseEntry) :
    (RealSparse.rectangularMatrix (r + c + p) (r + c + p) (entries r c p es)).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  simp only [rectangularMatrix_eq_coefficient]
  exact entries_symmetric r c p es j.val i.val

theorem mem_diagonal (start n : ℕ) (e : SparseEntry) (he : e ∈ diagonal start n) :
    start ≤ e.row ∧ e.row < start + n ∧ e.column = e.row ∧ e.value = 1 := by
  induction n generalizing start with
  | zero => simp [diagonal] at he
  | succ n ih =>
    simp only [diagonal, List.mem_cons] at he
    rcases he with rfl | he
    · simp
    · obtain ⟨hl, hu, hc, hv⟩ := ih (start + 1) he
      exact ⟨by omega, by omega, hc, hv⟩

theorem mem_pairs (r : ℕ) (es : List SparseEntry) (start n : ℕ) (e : SparseEntry)
    (he : e ∈ pairs r es start n) :
    ∃ k, start ≤ k ∧ k < start + n ∧
      (e = ⟨(entryAt es k).row, r + (entryAt es k).column, (entryAt es k).value⟩ ∨
       e = ⟨r + (entryAt es k).column, (entryAt es k).row, (entryAt es k).value⟩) := by
  induction n generalizing start with
  | zero => simp [pairs] at he
  | succ n ih =>
    simp only [pairs, List.mem_cons] at he
    rcases he with he | he | he
    · exact ⟨start, le_refl _, by omega, Or.inl he⟩
    · exact ⟨start, le_refl _, by omega, Or.inr he⟩
    · obtain ⟨k, hl, hu, hk⟩ := ih (start + 1) he
      exact ⟨k, by omega, by omega, hk⟩

/-- Valid rectangular coordinates remain valid in the explicitly padded
square saddle output, without needing distinct-coordinate storage. -/
theorem entries_bounds (r c p : ℕ) (es : List SparseEntry)
    (hrow : ∀ k < es.length, (entryAt es k).row < r)
    (hcol : ∀ k < es.length, (entryAt es k).column < c)
    (e : SparseEntry) (he : e ∈ entries r c p es) :
    e.row < r + c + p ∧ e.column < r + c + p := by
  simp only [entries, List.mem_append] at he
  rcases he with (he | he) | he
  · obtain ⟨_, hu, hc, _⟩ := mem_diagonal 0 r e he
    omega
  · obtain ⟨k, _, hk, he | he⟩ := mem_pairs r es 0 es.length e he
    · have hr := hrow k (by omega)
      have hc := hcol k (by omega)
      subst e
      simp only
      omega
    · have hr := hrow k (by omega)
      have hc := hcol k (by omega)
      subst e
      simp only
      omega
  · obtain ⟨_, hu, hc, _⟩ := mem_diagonal (r + c) p e he
    omega

theorem entryAt_bounds (r c p : ℕ) (es : List SparseEntry)
    (hrow : ∀ k < es.length, (entryAt es k).row < r)
    (hcol : ∀ k < es.length, (entryAt es k).column < c)
    (k : ℕ) (hk : k < (entries r c p es).length) :
    (entryAt (entries r c p es) k).row < r + c + p ∧
      (entryAt (entries r c p es) k).column < r + c + p := by
  apply entries_bounds r c p es hrow hcol
  simp [entryAt, hk]

/-- Padding by the input record count makes output length comparable to
that count. Every padded diagonal entry was emitted by the finite loop. -/
theorem padded_count_bounds (es : List SparseEntry) (r c : ℕ) (hr : r ≤ es.length) :
    es.length ≤ (entries r c es.length es).length ∧
      (entries r c es.length es).length ≤ 4 * es.length := by
  rw [entries_length]
  omega

end Maxwell.Cost.RealSaddle
