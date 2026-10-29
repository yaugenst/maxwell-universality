import Maxwell.Cost.RealSparseOrder.MergePass

namespace Maxwell.Cost.RealSparseOrder

def mergePasses : ℕ → List (List SparseEntry) → List (List SparseEntry)
  | 0, runs => runs
  | k+1, runs => mergePasses k (mergePass runs)

def mergeWork : ℕ → List (List SparseEntry) → ℕ
  | 0, _ => 0
  | k+1, runs => mergePassWork runs + mergeWork k (mergePass runs)

theorem mergePasses_perm (k : ℕ) (runs : List (List SparseEntry)) :
    (mergePasses k runs).flatten.Perm runs.flatten := by
  induction k generalizing runs with
  | zero => exact List.Perm.refl _
  | succ k ih => exact (ih (mergePass runs)).trans (mergePass_flatten_perm runs)

theorem mergePasses_length_le (k : ℕ) (runs : List (List SparseEntry)) :
    (mergePasses k runs).length ≤ runs.length := by
  induction k generalizing runs with
  | zero => exact le_rfl
  | succ k ih => exact (ih (mergePass runs)).trans (mergePass_length_le runs)

/-- A capacity of `2^k` runs collapses to at most one run in `k` passes. -/
theorem mergePasses_length_one (k : ℕ) (runs : List (List SparseEntry))
    (h : runs.length ≤ 2^k) : (mergePasses k runs).length ≤ 1 := by
  induction k generalizing runs with
  | zero => simpa only [mergePasses, pow_zero] using h
  | succ k ih =>
    apply ih
    have hh := mergePass_length_half runs
    rw [pow_succ] at h
    omega

theorem mergePasses_sorted (k : ℕ) (runs : List (List SparseEntry))
    (h : ∀ a ∈ runs, a.Pairwise KeyLE) :
    ∀ a ∈ mergePasses k runs, a.Pairwise KeyLE := by
  induction k generalizing runs with
  | zero => exact h
  | succ k ih => exact ih (mergePass runs) (mergePass_sorted runs h)

theorem mergePasses_keyFilter (row column k : ℕ) (runs : List (List SparseEntry))
    (h : ∀ a ∈ runs, a.Pairwise KeyLE) :
    keyFilter row column (mergePasses k runs).flatten = keyFilter row column runs.flatten := by
  induction k generalizing runs with
  | zero => rfl
  | succ k ih =>
    exact (ih (mergePass runs) (mergePass_sorted runs h)).trans (mergePass_keyFilter row column runs h)

theorem mergePasses_width (k width : ℕ) (runs : List (List SparseEntry))
    (h : ∀ a ∈ runs, a.length ≤ width) :
    ∀ a ∈ mergePasses k runs, a.length ≤ 2^k*width := by
  induction k generalizing runs width with
  | zero => simpa only [mergePasses, pow_zero, one_mul] using h
  | succ k ih =>
    have hh := ih (2*width) (mergePass runs) (mergePass_width runs width h)
    simpa only [mergePasses, pow_succ, Nat.mul_assoc] using hh

/-- Each pass charges each record once and at most one control unit per
input run. Neither count can increase between passes. -/
theorem mergeWork_le (k : ℕ) (runs : List (List SparseEntry)) :
    mergeWork k runs ≤ k*(runs.flatten.length+runs.length) := by
  induction k generalizing runs with
  | zero => simp [mergeWork]
  | succ k ih =>
    have hi := ih (mergePass runs)
    rw [mergePass_mass] at hi
    have hp := mergePass_work_le runs
    have hl := mergePass_length_le runs
    simp only [mergeWork]
    nlinarith

def singletonRuns (entries : List SparseEntry) : List (List SparseEntry) :=
  entries.map (fun e => [e])

@[simp] theorem singletonRuns_length (entries : List SparseEntry) :
    (singletonRuns entries).length = entries.length := List.length_map _

@[simp] theorem singletonRuns_flatten (entries : List SparseEntry) :
    (singletonRuns entries).flatten = entries := by
  induction entries with
  | nil => rfl
  | cons e entries ih => simpa only [singletonRuns, List.map_cons, List.flatten_cons,
      List.singleton_append] using congrArg (List.cons e) ih

theorem singletonRuns_sorted (entries : List SparseEntry) :
    ∀ a ∈ singletonRuns entries, a.Pairwise KeyLE := by
  intro a ha
  obtain ⟨e, _, rfl⟩ := List.mem_map.mp ha
  simp

theorem singletonRuns_packed (entries : List SparseEntry) : PackedRuns 1 (singletonRuns entries) := by
  induction entries with
  | nil => trivial
  | cons e entries ih => exact ⟨by simp, by simp, ih⟩

theorem mergePasses_packed (k width : ℕ) (runs : List (List SparseEntry))
    (h : PackedRuns width runs) : PackedRuns (2^k*width) (mergePasses k runs) := by
  induction k generalizing runs width with
  | zero => simpa only [mergePasses, pow_zero, one_mul] using h
  | succ k ih =>
    simpa only [mergePasses, pow_succ, Nat.mul_assoc] using
      ih (2*width) (mergePass runs) (mergePass_packed width runs h)

theorem singleton_passes_packed (k : ℕ) (entries : List SparseEntry) :
    PackedRuns (2^k) (mergePasses k (singletonRuns entries)) := by
  simpa only [mul_one] using mergePasses_packed k 1 (singletonRuns entries) (singletonRuns_packed entries)

private theorem flatten_sorted_of_one (runs : List (List SparseEntry))
    (hsize : runs.length ≤ 1) (h : ∀ a ∈ runs, a.Pairwise KeyLE) : runs.flatten.Pairwise KeyLE := by
  cases runs with
  | nil => simp
  | cons a rest =>
    cases rest with
    | nil => simpa using h a (by simp)
    | cons b rest => simp only [List.length_cons] at hsize; omega

/-- Stable row-column ordering by adjacent bottom-up merges, with the
number of passes chosen from the input length's binary size. -/
def bottomUpSort (entries : List SparseEntry) : List SparseEntry :=
  (mergePasses entries.length.size (singletonRuns entries)).flatten

def bottomUpWork (entries : List SparseEntry) : ℕ :=
  mergeWork entries.length.size (singletonRuns entries)

theorem bottomUpSort_perm (entries : List SparseEntry) : (bottomUpSort entries).Perm entries := by
  simpa only [bottomUpSort, singletonRuns_flatten] using
    mergePasses_perm entries.length.size (singletonRuns entries)

@[simp] theorem bottomUpSort_length (entries : List SparseEntry) :
    (bottomUpSort entries).length = entries.length := (bottomUpSort_perm entries).length_eq

theorem bottomUpSort_sorted (entries : List SparseEntry) : (bottomUpSort entries).Pairwise KeyLE := by
  apply flatten_sorted_of_one
  · apply mergePasses_length_one
    rw [singletonRuns_length]
    exact (Nat.lt_size_self _).le
  · exact mergePasses_sorted _ _ (singletonRuns_sorted entries)

/-- Full record order within each equal-key class is unchanged, including
duplicates carrying different real coefficients. -/
theorem bottomUpSort_stable (entries : List SparseEntry) (row column : ℕ) :
    keyFilter row column (bottomUpSort entries) = keyFilter row column entries := by
  simpa only [bottomUpSort, singletonRuns_flatten] using
    mergePasses_keyFilter row column entries.length.size (singletonRuns entries)
      (singletonRuns_sorted entries)

/-- The pure merge and pass-control work is `O(m log m)`, with a fully
explicit bound and no charge for arithmetic on real coefficients. -/
theorem bottomUpWork_le (entries : List SparseEntry) :
    bottomUpWork entries ≤ 2*entries.length*entries.length.size := by
  have h := mergeWork_le entries.length.size (singletonRuns entries)
  simp only [singletonRuns_flatten, singletonRuns_length] at h
  unfold bottomUpWork
  nlinarith

end Maxwell.Cost.RealSparseOrder
