import Maxwell.Cost.RealSparseOrder.Order
import Mathlib.Data.List.Induction
import Mathlib.Data.Nat.Size

namespace Maxwell.Cost.RealSparseOrder

/-- One bottom-up pass merges adjacent runs, retaining an unpaired last run. -/
def mergePass : List (List SparseEntry) → List (List SparseEntry)
  | [] => []
  | [a] => [a]
  | a :: b :: rest => merge a b :: mergePass rest

/-- A unit charge for each record visited and each emitted run. -/
def mergePassWork : List (List SparseEntry) → ℕ
  | [] => 0
  | [a] => a.length+1
  | a :: b :: rest => a.length+b.length+1+mergePassWork rest

@[simp] theorem mergePass_nil : mergePass [] = [] := rfl
@[simp] theorem mergePass_singleton (a : List SparseEntry) : mergePass [a] = [a] := rfl
@[simp] theorem mergePass_pair (a b : List SparseEntry) (rest : List (List SparseEntry)) :
    mergePass (a::b::rest) = merge a b :: mergePass rest := rfl

theorem mergePass_flatten_perm (runs : List (List SparseEntry)) :
    (mergePass runs).flatten.Perm runs.flatten := by
  induction runs using List.twoStepInduction with
  | nil => simp
  | singleton a => simp
  | cons_cons a b rest ih _ =>
    simpa only [mergePass_pair, List.flatten_cons, List.append_assoc] using (merge_perm a b).append ih

@[simp] theorem mergePass_mass (runs : List (List SparseEntry)) :
    (mergePass runs).flatten.length = runs.flatten.length := (mergePass_flatten_perm runs).length_eq

theorem mergePass_length (runs : List (List SparseEntry)) :
    (mergePass runs).length = (runs.length+1)/2 := by
  induction runs using List.twoStepInduction with
  | nil => rfl
  | singleton a => simp
  | cons_cons a b rest ih _ =>
    simp only [mergePass_pair, List.length_cons, ih]
    omega

theorem mergePass_length_le (runs : List (List SparseEntry)) :
    (mergePass runs).length ≤ runs.length := by rw [mergePass_length]; omega

theorem mergePass_length_half (runs : List (List SparseEntry)) :
    2*(mergePass runs).length ≤ runs.length+1 := by rw [mergePass_length]; omega

theorem mergePass_sorted (runs : List (List SparseEntry))
    (h : ∀ a ∈ runs, a.Pairwise KeyLE) :
    ∀ a ∈ mergePass runs, a.Pairwise KeyLE := by
  induction runs using List.twoStepInduction with
  | nil => simp
  | singleton a => simpa using h
  | cons_cons a b rest ih _ =>
    intro c hc
    rcases List.mem_cons.mp hc with hc | hc
    · subst c
      exact merge_sorted a b (h a (by simp)) (h b (by simp))
    · exact ih (fun d hd => h d (by simp [hd])) c hc

theorem mergePass_width (runs : List (List SparseEntry)) (width : ℕ)
    (h : ∀ a ∈ runs, a.length ≤ width) :
    ∀ a ∈ mergePass runs, a.length ≤ 2*width := by
  induction runs using List.twoStepInduction with
  | nil => simp
  | singleton a =>
    intro b hb
    have he : b=a := by simpa using hb
    subst b
    have hh := h a (by simp)
    omega
  | cons_cons a b rest ih _ =>
    intro c hc
    rcases List.mem_cons.mp hc with hc | hc
    · subst c
      rw [merge_length]
      have ha := h a (by simp)
      have hb := h b (by simp)
      omega
    · exact ih (fun d hd => h d (by simp [hd])) c hc

theorem mergePass_work (runs : List (List SparseEntry)) :
    mergePassWork runs = runs.flatten.length + (mergePass runs).length := by
  induction runs using List.twoStepInduction with
  | nil => rfl
  | singleton a => simp [mergePassWork]
  | cons_cons a b rest ih _ =>
    simp only [mergePassWork, mergePass_pair, List.flatten_cons, List.length_append,
      List.length_cons, ih]
    omega

theorem mergePass_work_le (runs : List (List SparseEntry)) :
    mergePassWork runs ≤ runs.flatten.length + runs.length := by
  rw [mergePass_work]
  exact Nat.add_le_add_left (mergePass_length_le runs) _

/-- The original records at one row-column key, retaining their coefficient
values and their input order. Equality of this list expresses stability. -/
def keyFilter (row column : ℕ) (entries : List SparseEntry) : List SparseEntry :=
  entries.filter (fun e => decide (e.row=row ∧ e.column=column))

@[simp] theorem keyFilter_nil (row column : ℕ) : keyFilter row column [] = [] := rfl

theorem keyFilter_cons (row column : ℕ) (a : SparseEntry) (entries : List SparseEntry) :
    keyFilter row column (a::entries) =
      if a.row=row ∧ a.column=column then a::keyFilter row column entries
      else keyFilter row column entries := by simp only [keyFilter, List.filter_cons, decide_eq_true_eq]

@[simp] theorem keyFilter_append (row column : ℕ) (a b : List SparseEntry) :
    keyFilter row column (a++b) = keyFilter row column a ++ keyFilter row column b :=
  List.filter_append a b

private theorem keyFilter_empty_of_head (row column : ℕ) (a b : SparseEntry)
    (left : List SparseEntry) (hl : (a::left).Pairwise KeyLE) (hab : ¬KeyLE a b)
    (hb : b.row=row ∧ b.column=column) : keyFilter row column (a::left) = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro e he
  simp only [decide_eq_true_eq]
  intro hk
  have hae : KeyLE a e := by
    rcases List.mem_cons.mp he with he | he
    · subst e; exact keyLE_refl a
    · exact (List.pairwise_cons.mp hl).1 e he
  have heb : KeyLE e b := Or.inr ⟨hk.1.trans hb.1.symm, by omega⟩
  exact hab (keyLE_trans a e b hae heb)

theorem merge_keyFilter (row column : ℕ) : ∀ (left right : List SparseEntry),
    left.Pairwise KeyLE → right.Pairwise KeyLE →
      keyFilter row column (merge left right) =
        keyFilter row column left ++ keyFilter row column right
  | [], right, _, _ => by simp [merge]
  | left, [], _, _ => by simp [merge]
  | a::left, b::right, hl, hr => by
    by_cases hab : KeyLE a b
    · have hm : merge (a::left) (b::right) = a::merge left (b::right) := by
        simp only [merge, List.cons_merge_cons, decide_eq_true_eq, ite_eq_left hab]
      rw [hm, keyFilter_cons, merge_keyFilter row column left (b::right)
        (List.pairwise_cons.mp hl).2 hr, keyFilter_cons row column a left]
      split_ifs <;> rfl
    · have hm : merge (a::left) (b::right) = b::merge (a::left) right := by
        simp only [merge, List.cons_merge_cons, decide_eq_true_eq, ite_eq_right hab]
      have ih := merge_keyFilter row column (a::left) right hl (List.pairwise_cons.mp hr).2
      rw [hm, keyFilter_cons, ih, keyFilter_cons row column b]
      by_cases hb : b.row=row ∧ b.column=column
      · rw [ite_eq_left hb, ite_eq_left hb,
          keyFilter_empty_of_head row column a b left hl hab hb]
        rfl
      · rw [ite_eq_right hb, ite_eq_right hb]
termination_by left right => left.length+right.length

theorem mergePass_keyFilter (row column : ℕ) (runs : List (List SparseEntry))
    (h : ∀ a ∈ runs, a.Pairwise KeyLE) :
    keyFilter row column (mergePass runs).flatten = keyFilter row column runs.flatten := by
  induction runs using List.twoStepInduction with
  | nil => rfl
  | singleton a => rfl
  | cons_cons a b rest ih _ =>
    simp only [mergePass_pair, List.flatten_cons, keyFilter_append]
    rw [merge_keyFilter row column a b (h a (by simp)) (h b (by simp)),
      ih (fun c hc => h c (by simp [hc])), List.append_assoc]

/-- Every nonfinal run fills the pass width; the last run may be shorter. -/
def PackedRuns (width : ℕ) : List (List SparseEntry) → Prop
  | [] => True
  | a::rest => a.length ≤ width ∧ (rest ≠ [] → a.length = width) ∧ PackedRuns width rest

theorem mergePass_packed (width : ℕ) (runs : List (List SparseEntry))
    (h : PackedRuns width runs) : PackedRuns (2*width) (mergePass runs) := by
  induction runs using List.twoStepInduction with
  | nil => trivial
  | singleton a =>
    change a.length ≤ 2*width ∧ ([] ≠ [] → a.length=2*width) ∧ True
    exact ⟨by have hh := h.1; omega, by simp, trivial⟩
  | cons_cons a b rest ih _ =>
    obtain ⟨ha, hafull, hb, hbfull, hrest⟩ := h
    change (merge a b).length ≤ 2*width ∧
      (mergePass rest ≠ [] → (merge a b).length=2*width) ∧ PackedRuns (2*width) (mergePass rest)
    refine ⟨by rw [merge_length]; omega, ?_, ih hrest⟩
    intro hnonempty
    have hr : rest ≠ [] := by intro he; simp [he] at hnonempty
    rw [merge_length, hafull (by simp), hbfull hr]
    omega

theorem packed_take_head (width : ℕ) (a : List SparseEntry) (rest : List (List SparseEntry))
    (h : PackedRuns width (a::rest)) : (a::rest).flatten.take width = a := by
  cases rest with
  | nil => simpa using List.take_of_length_le h.1
  | cons b rest =>
    have hh := h.2.1 (by simp)
    simp only [List.flatten_cons, ← hh, List.take_append_length]

theorem packed_drop_head (width : ℕ) (a : List SparseEntry) (rest : List (List SparseEntry))
    (h : PackedRuns width (a::rest)) : (a::rest).flatten.drop width = rest.flatten := by
  cases rest with
  | nil => simpa using List.drop_of_length_le h.1
  | cons b rest =>
    have hh := h.2.1 (by simp)
    simp only [List.flatten_cons, ← hh, List.drop_append_length]

/-- The two physical reads in a fixed-width pass select precisely its next
two logical runs, including a short final right run. -/
theorem packed_pair_slices (width : ℕ) (a b : List SparseEntry) (rest : List (List SparseEntry))
    (h : PackedRuns width (a::b::rest)) :
    (a::b::rest).flatten.take width = a ∧
      ((a::b::rest).flatten.drop width).take width = b ∧
      (a::b::rest).flatten.drop (2*width) = rest.flatten := by
  refine ⟨packed_take_head width a (b::rest) h, ?_, ?_⟩
  · rw [packed_drop_head width a (b::rest) h]
    exact packed_take_head width b rest h.2.2
  · rw [show 2*width=width+width by omega, ← List.drop_drop,
      packed_drop_head width a (b::rest) h]
    exact packed_drop_head width b rest h.2.2

theorem mergePass_contiguous_step (width : ℕ) (a b : List SparseEntry)
    (rest : List (List SparseEntry)) (h : PackedRuns width (a::b::rest)) :
    (mergePass (a::b::rest)).flatten =
      merge ((a::b::rest).flatten.take width) (((a::b::rest).flatten.drop width).take width) ++
        (mergePass rest).flatten := by
  rw [(packed_pair_slices width a b rest h).1, (packed_pair_slices width a b rest h).2.1]
  rfl

end Maxwell.Cost.RealSparseOrder
