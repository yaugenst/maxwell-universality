import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Tactic

/-! Binary odd-even sorting in prefix-zero-count coordinates. A comparator
between positions `p-1,p` replaces the prefix count at `p` by the minimum
of the left prefix plus one and the right prefix.  The two parity updates
below are simultaneous on disjoint prefix coordinates. -/

namespace Maxwell.Logical.Routing.BinaryDepth

/-- Valid cumulative counts of zeros on a binary word of length `q`. -/
structure Shape (q : ℕ) (profile : ℕ → ℤ) : Prop where
  start : profile 0 = 0
  step : ∀ p < q, profile p ≤ profile (p + 1) ∧ profile (p + 1) ≤ profile p + 1

/-- One parity layer of adjacent binary comparators in prefix coordinates. -/
def layer (q parity : ℕ) (profile : ℕ → ℤ) (p : ℕ) : ℤ :=
  if 0 < p ∧ p < q ∧ p % 2 = parity % 2 then
    min (profile (p - 1) + 1) (profile (p + 1)) else profile p

/-- One even-index then odd-index comparator round (two layers). -/
def round (q : ℕ) (profile : ℕ → ℤ) : ℕ → ℤ := layer q 0 (layer q 1 profile)

@[simp] theorem layer_zero (q parity : ℕ) (profile : ℕ → ℤ) :
    layer q parity profile 0 = profile 0 := by simp [layer]

@[simp] theorem layer_end (q parity : ℕ) (profile : ℕ → ℤ) :
    layer q parity profile q = profile q := by simp [layer]

theorem layer_increases (q parity : ℕ) (profile : ℕ → ℤ) (h : Shape q profile) (p : ℕ) :
    profile p ≤ layer q parity profile p := by
  unfold layer
  split_ifs with hp
  · have hl := h.step (p - 1) (by omega)
    have hr := h.step p hp.2.1
    have he : p - 1 + 1 = p := by omega
    rw [he] at hl
    omega
  · rfl

theorem layer_shape (q parity : ℕ) (profile : ℕ → ℤ) (h : Shape q profile) :
    Shape q (layer q parity profile) := by
  refine ⟨by simpa using h.start, ?_⟩
  intro p hp
  have hm := h.step p hp
  have hl : p = 0 ∨ (profile (p - 1) ≤ profile p ∧ profile p ≤ profile (p - 1) + 1) := by
    by_cases hz : p = 0
    · exact Or.inl hz
    · have hh := h.step (p - 1) (by omega)
      have he : p - 1 + 1 = p := by omega
      rw [he] at hh
      exact Or.inr hh
  have hr : p + 1 = q ∨ (profile (p + 1) ≤ profile (p + 2) ∧
      profile (p + 2) ≤ profile (p + 1) + 1) := by
    by_cases he : p + 1 = q
    · exact Or.inl he
    · exact Or.inr (h.step (p + 1) (by omega))
  simp only [layer, Nat.add_sub_cancel, Nat.add_assoc, Nat.reduceAdd]
  split_ifs <;> omega

theorem round_shape (q : ℕ) (profile : ℕ → ℤ) (h : Shape q profile) :
    Shape q (round q profile) :=
  layer_shape q 0 (layer q 1 profile) (layer_shape q 1 profile h)

/-- Two parity layers dominate one simultaneous nearest-neighbor relaxation. -/
theorem round_lower (q : ℕ) (profile : ℕ → ℤ) (h : Shape q profile)
    (p : ℕ) (hp : 0 < p) (hpq : p < q) :
    min (profile (p - 1) + 1) (profile (p + 1)) ≤ round q profile p := by
  have hl := layer_increases q 1 profile h (p - 1)
  have hr := layer_increases q 1 profile h (p + 1)
  by_cases heven : p % 2 = 0
  · change _ ≤ layer q 0 (layer q 1 profile) p
    rw [layer]
    simp only [hp, hpq, heven, Nat.zero_mod, and_self, ↓reduceIte]
    exact min_le_min (by omega) hr
  · have hodd : p % 2 = 1 := by omega
    simp [round, layer, hp, hpq, hodd]

/-- Adjacent-step bounds telescope over arbitrary prefix intervals. -/
theorem interval_bounds (q : ℕ) (profile : ℕ → ℤ) (h : Shape q profile)
    (start distance : ℕ) (hbound : start + distance ≤ q) :
    profile start ≤ profile (start + distance) ∧
      profile (start + distance) ≤ profile start + distance := by
  induction distance with
  | zero => simp
  | succ distance ih =>
    have hi := ih (by omega)
    have hs := h.step (start + distance) (by omega)
    push_cast
    have he : start + (distance + 1) = start + distance + 1 := by omega
    rw [he]
    omega

/-- Initial binary prefixes satisfy the barrier used by the depth proof. -/
theorem initial_barrier (q : ℕ) (profile : ℕ → ℤ) (h : Shape q profile) :
    ∀ p ≤ q, min (2 * (p : ℤ)) (min (2 * profile q) ((p : ℤ) + profile q - q)) ≤ 2 * profile p := by
  intro p hp
  have hleft := interval_bounds q profile h 0 p (by omega)
  have hright := interval_bounds q profile h p (q - p) (by omega)
  simp only [zero_add, h.start] at hleft
  have he : p + (q - p) = q := by omega
  rw [he] at hright
  omega

/-- One two-layer round advances the all-input barrier by one. -/
theorem barrier_step (q t : ℕ) (profile : ℕ → ℤ) (h : Shape q profile)
    (barrier : ∀ p ≤ q,
      min (2 * (p : ℤ)) (min (2 * profile q) ((p : ℤ) + profile q + t - q)) ≤ 2 * profile p) :
    ∀ p ≤ q,
      min (2 * (p : ℤ)) (min (2 * profile q) ((p : ℤ) + profile q + (t + 1 : ℕ) - q)) ≤
        2 * round q profile p := by
  intro p hpq
  by_cases hp0 : p = 0
  · subst p
    simp only [round, layer_zero, h.start]
    omega
  · by_cases hpend : p = q
    · subst p
      simp only [round, layer_end]
      omega
    · have hl := barrier (p - 1) (by omega)
      have hr := barrier (p + 1) (by omega)
      have hh := round_lower q profile h p (by omega) (by omega)
      push_cast at *
      omega

/-- Execute `rounds` complete odd/even rounds. -/
def run (q : ℕ) : ℕ → (ℕ → ℤ) → (ℕ → ℤ)
  | 0, profile => profile
  | t + 1, profile => round q (run q t profile)

theorem run_shape (q t : ℕ) (profile : ℕ → ℤ) (h : Shape q profile) :
    Shape q (run q t profile) := by
  induction t with
  | zero => exact h
  | succ t ih => exact round_shape q (run q t profile) ih

@[simp] theorem run_end (q t : ℕ) (profile : ℕ → ℤ) : run q t profile q = profile q := by
  induction t with
  | zero => rfl
  | succ t ih => simpa only [run, round, layer_end] using ih

theorem run_barrier (q t : ℕ) (profile : ℕ → ℤ) (h : Shape q profile) :
    ∀ p ≤ q,
      min (2 * (p : ℤ)) (min (2 * profile q) ((p : ℤ) + profile q + t - q)) ≤
        2 * run q t profile p := by
  induction t with
  | zero => simpa only [Nat.cast_zero, add_zero, run] using initial_barrier q profile h
  | succ t ih =>
    have hh := barrier_step q t (run q t profile) (run_shape q t profile h)
    simp only [run_end] at hh
    simpa only [run] using hh ih

/-- After exactly `2*q` parity layers, every binary prefix count has its
sorted value.  This theorem holds for every valid binary prefix profile. -/
theorem binary_depth (q : ℕ) (profile : ℕ → ℤ) (h : Shape q profile) (p : ℕ) (hp : p ≤ q) :
    run q q profile p = min (p : ℤ) (profile q) := by
  have hb := run_barrier q q profile h p hp
  have hs := run_shape q q profile h
  have hl := interval_bounds q (run q q profile) hs 0 p (by omega)
  have hr := interval_bounds q (run q q profile) hs p (q - p) (by omega)
  simp only [zero_add, hs.start] at hl
  have he : p + (q - p) = q := by omega
  rw [he, run_end] at hr
  omega

/-- Indicator of a zero bit. -/
def zeroBit (bit : Bool) : ℤ := if bit then 0 else 1

def prefixZeros (word : ℕ → Bool) (p : ℕ) : ℤ := ∑ i ∈ Finset.range p, zeroBit (word i)

@[simp] theorem prefix_zero (word : ℕ → Bool) : prefixZeros word 0 = 0 := by simp [prefixZeros]

theorem prefix_succ (word : ℕ → Bool) (p : ℕ) :
    prefixZeros word (p + 1) = prefixZeros word p + zeroBit (word p) := by
  exact Finset.sum_range_succ _ _

theorem prefix_shape (q : ℕ) (word : ℕ → Bool) : Shape q (prefixZeros word) := by
  refine ⟨prefix_zero word, ?_⟩
  intro p _
  rw [prefix_succ]
  cases word p <;> simp [zeroBit]

/-- The actual adjacent binary comparator (AND on the left, OR on the right). -/
def compareBit (lower : ℕ) (word : ℕ → Bool) (p : ℕ) : Bool :=
  if p = lower then word lower && word (lower + 1)
  else if p = lower + 1 then word lower || word (lower + 1) else word p

theorem prefix_compare_before (i p : ℕ) (word : ℕ → Bool) (hp : p ≤ i) :
    prefixZeros (compareBit i word) p = prefixZeros word p := by
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k < p := Finset.mem_range.mp hk
  have hki : k ≠ i := by omega
  have hki' : k ≠ i + 1 := by omega
  simp only [compareBit, hki, hki', ↓reduceIte]

theorem prefix_compare_center (i : ℕ) (word : ℕ → Bool) :
    prefixZeros (compareBit i word) (i + 1) =
      min (prefixZeros word i + 1) (prefixZeros word (i + 2)) := by
  rw [prefix_succ, prefix_compare_before i i word (by omega)]
  have he : i + 2 = (i + 1) + 1 := by omega
  rw [he, prefix_succ, prefix_succ]
  simp only [compareBit, ↓reduceIte]
  cases word i <;> cases word (i + 1) <;> simp [zeroBit]

theorem prefix_compare_pair_end (i : ℕ) (word : ℕ → Bool) :
    prefixZeros (compareBit i word) (i + 2) = prefixZeros word (i + 2) := by
  have he : i + 2 = (i + 1) + 1 := by omega
  rw [he, prefix_succ, prefix_compare_center, prefix_succ, prefix_succ]
  have hne : i + 1 ≠ i := by omega
  simp only [compareBit, hne, ↓reduceIte]
  cases word i <;> cases word (i + 1) <;> simp [zeroBit]

theorem prefix_compare_after (i p : ℕ) (word : ℕ → Bool) (hp : i + 2 ≤ p) :
    prefixZeros (compareBit i word) p = prefixZeros word p := by
  induction p with
  | zero => omega
  | succ p ih =>
    by_cases he : p + 1 = i + 2
    · rw [he]
      exact prefix_compare_pair_end i word
    · have hp' : i + 2 ≤ p := by omega
      rw [prefix_succ, prefix_succ, ih hp']
      have hne : p ≠ i := by omega
      have hne' : p ≠ i + 1 := by omega
      simp only [compareBit, hne, hne', ↓reduceIte]

/-- Exact representation correspondence for a binary comparator. -/
theorem prefix_compare (i p : ℕ) (word : ℕ → Bool) :
    prefixZeros (compareBit i word) p =
      if p = i + 1 then min (prefixZeros word i + 1) (prefixZeros word (i + 2)) else prefixZeros word p := by
  by_cases he : p = i + 1
  · subst p
    simp only [↓reduceIte]
    exact prefix_compare_center i word
  · simp only [he, ↓reduceIte]
    by_cases hp : p ≤ i
    · exact prefix_compare_before i p word hp
    · exact prefix_compare_after i p word (by omega)

/-- Execute binary comparisons specified by their interior prefix indices. -/
def runBits : List ℕ → (ℕ → Bool) → (ℕ → Bool)
  | [], word => word
  | center :: rest, word => runBits rest (compareBit (center - 1) word)

/-- Same-parity comparators act independently on prefix counts. -/
theorem prefix_runBits (centers : List ℕ) (parity : ℕ)
    (hc : ∀ c ∈ centers, 0 < c ∧ c % 2 = parity % 2) (word : ℕ → Bool) (p : ℕ) :
    prefixZeros (runBits centers word) p =
      if p ∈ centers then min (prefixZeros word (p - 1) + 1) (prefixZeros word (p + 1))
      else prefixZeros word p := by
  induction centers generalizing word with
  | nil => simp [runBits]
  | cons c rest ih =>
    have hc0 := hc c (by simp)
    have hr : ∀ c ∈ rest, 0 < c ∧ c % 2 = parity % 2 := by
      intro c h
      exact hc c (by simp [h])
    have he : c - 1 + 1 = c := by omega
    have he' : c - 1 + 2 = c + 1 := by omega
    change prefixZeros (runBits rest (compareBit (c - 1) word)) p = _
    rw [ih hr]
    by_cases hp : p ∈ rest
    · have hpp := hr p hp
      have hnleft : p - 1 ≠ c := by omega
      have hnright : p + 1 ≠ c := by omega
      simp only [hp, List.mem_cons, or_true, ↓reduceIte,
        prefix_compare, he, hnleft, hnright]
    · simp only [hp, List.mem_cons, or_false, ↓reduceIte, prefix_compare, he, he']
      by_cases heq : p = c
      · subst p
        simp only [↓reduceIte]
      · simp only [heq, ↓reduceIte]

def layerCenters (q parity : ℕ) : List ℕ :=
  (List.range q).filter fun p => 0 < p ∧ p % 2 = parity % 2

theorem mem_layerCenters (q parity p : ℕ) :
    p ∈ layerCenters q parity ↔ 0 < p ∧ p < q ∧ p % 2 = parity % 2 := by
  simp only [layerCenters, List.mem_filter, List.mem_range, decide_eq_true_eq]
  omega

/-- Actual Boolean layer, implemented by its list of adjacent comparators. -/
def bitLayer (q parity : ℕ) (word : ℕ → Bool) : ℕ → Bool := runBits (layerCenters q parity) word

/-- Exact all-input correspondence between Boolean execution and the
prefix-count layer used in the depth proof. -/
theorem prefix_bitLayer (q parity : ℕ) (word : ℕ → Bool) :
    prefixZeros (bitLayer q parity word) = layer q parity (prefixZeros word) := by
  ext p
  have hc : ∀ c ∈ layerCenters q parity, 0 < c ∧ c % 2 = parity % 2 := by
    intro c hc
    have h := (mem_layerCenters q parity c).mp hc
    exact ⟨h.1, h.2.2⟩
  rw [bitLayer, prefix_runBits (layerCenters q parity) parity hc word p]
  simp only [mem_layerCenters, layer]

def bitRound (q : ℕ) (word : ℕ → Bool) : ℕ → Bool := bitLayer q 0 (bitLayer q 1 word)

def bitRun (q : ℕ) : ℕ → (ℕ → Bool) → (ℕ → Bool)
  | 0, word => word
  | t + 1, word => bitRound q (bitRun q t word)

theorem prefix_bitRun (q t : ℕ) (word : ℕ → Bool) :
    prefixZeros (bitRun q t word) = run q t (prefixZeros word) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [bitRun, bitRound, prefix_bitLayer, run, round, ih]

/-- The implemented binary comparator schedule has sorted prefix counts
for every input after exactly `2*q` layers. -/
theorem bitRun_sorted_prefix (q : ℕ) (word : ℕ → Bool) (p : ℕ) (hp : p ≤ q) :
    prefixZeros (bitRun q q word) p = min (p : ℤ) (prefixZeros word q) := by
  rw [prefix_bitRun]
  exact binary_depth q (prefixZeros word) (prefix_shape q word) p hp

/-- The concrete `2*q`-layer Boolean execution is sorted on its first `q`
entries; no sortedness or crossing claim is assumed. -/
theorem bitRun_sorted (q : ℕ) (word : ℕ → Bool) :
    Monotone (fun i : Fin q => bitRun q q word i.val) := by
  intro i j hij
  change bitRun q q word i.val ≤ bitRun q q word j.val
  cases hi : bitRun q q word i.val <;> cases hj : bitRun q q word j.val
  · exact le_rfl
  · decide
  · have hip := bitRun_sorted_prefix q word i.val (by omega)
    have his := bitRun_sorted_prefix q word (i.val + 1) (by omega)
    have hjp := bitRun_sorted_prefix q word j.val (by omega)
    have hjs := bitRun_sorted_prefix q word (j.val + 1) (by omega)
    rw [prefix_succ, hi] at his
    rw [prefix_succ, hj] at hjs
    simp only [zeroBit, ↓reduceIte, add_zero] at his hjs
    push_cast at his hjs
    have hij' : i.val ≤ j.val := hij
    omega
  · exact le_rfl

/-- Adjacent ascending comparator for arbitrary linearly ordered keys. -/
def compareScalar {α : Type*} [LinearOrder α] (lower : ℕ) (word : ℕ → α) (p : ℕ) : α :=
  if p = lower then min (word lower) (word (lower + 1))
  else if p = lower + 1 then max (word lower) (word (lower + 1)) else word p

def scalarRunBits {α : Type*} [LinearOrder α] : List ℕ → (ℕ → α) → (ℕ → α)
  | [], word => word
  | center :: rest, word => scalarRunBits rest (compareScalar (center - 1) word)

def scalarLayer {α : Type*} [LinearOrder α] (q parity : ℕ) (word : ℕ → α) : ℕ → α :=
  scalarRunBits (layerCenters q parity) word

def scalarRound {α : Type*} [LinearOrder α] (q : ℕ) (word : ℕ → α) : ℕ → α :=
  scalarLayer q 0 (scalarLayer q 1 word)

def scalarRun {α : Type*} [LinearOrder α] (q : ℕ) : ℕ → (ℕ → α) → (ℕ → α)
  | 0, word => word
  | t + 1, word => scalarRound q (scalarRun q t word)

def cutAbove {α : Type*} [LinearOrder α] (cut : α) (word : ℕ → α) (p : ℕ) : Bool :=
  decide (cut < word p)

theorem cut_compareScalar {α : Type*} [LinearOrder α] (cut : α) (word : ℕ → α) (i : ℕ) :
    cutAbove cut (compareScalar i word) = compareBit i (cutAbove cut word) := by
  ext p
  by_cases hp : p = i
  · subst p
    simp [cutAbove, compareScalar, compareBit, lt_min_iff]
  · by_cases hp' : p = i + 1
    · subst p
      simp [cutAbove, compareScalar, compareBit, lt_max_iff]
    · simp [cutAbove, compareScalar, compareBit, hp, hp']

theorem cut_scalarRunBits {α : Type*} [LinearOrder α] (cut : α) (word : ℕ → α)
    (centers : List ℕ) :
    cutAbove cut (scalarRunBits centers word) = runBits centers (cutAbove cut word) := by
  induction centers generalizing word with
  | nil => rfl
  | cons c rest ih => simp only [scalarRunBits, runBits, ih, cut_compareScalar]

theorem cut_scalarRun {α : Type*} [LinearOrder α] (q t : ℕ) (cut : α) (word : ℕ → α) :
    cutAbove cut (scalarRun q t word) = bitRun q t (cutAbove cut word) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [scalarRun, scalarRound, scalarLayer, cut_scalarRunBits,
      bitRun, bitRound, bitLayer, ih]

/-- Universal correctness of the actual `2*q`-layer odd-even comparator
schedule, obtained from the proved binary depth and thresholds. -/
theorem scalarRun_sorted {α : Type*} [LinearOrder α] (q : ℕ) (word : ℕ → α) :
    Monotone (fun i : Fin q => scalarRun q q word i.val) := by
  intro i j hij
  change scalarRun q q word i.val ≤ scalarRun q q word j.val
  by_contra h
  have hbad : scalarRun q q word j.val < scalarRun q q word i.val := lt_of_not_ge h
  let cut := scalarRun q q word j.val
  have hb := bitRun_sorted q (cutAbove cut word) hij
  have hc := cut_scalarRun q q cut word
  change bitRun q q (cutAbove cut word) i.val ≤ bitRun q q (cutAbove cut word) j.val at hb
  rw [← hc] at hb
  have hi : cutAbove cut (scalarRun q q word) i.val = true := by simp [cutAbove, cut, hbad]
  have hj : cutAbove cut (scalarRun q q word) j.val = false := by simp [cutAbove, cut]
  rw [hi, hj] at hb
  exact (by decide : ¬ (true ≤ false)) hb

/-- A safe adjacent comparator permutes the first `q` entries exactly. -/
theorem compareScalar_permutation {α : Type*} [LinearOrder α] (q lower : ℕ)
    (hbound : lower + 1 < q) (word : ℕ → α) :
    ∃ permutation : Equiv.Perm (Fin q),
      ∀ p : Fin q, compareScalar lower word p.val = word (permutation p).val := by
  let i : Fin q := ⟨lower, by omega⟩
  let j : Fin q := ⟨lower + 1, hbound⟩
  by_cases h : word lower ≤ word (lower + 1)
  · refine ⟨Equiv.refl _, ?_⟩
    intro p
    simp only [compareScalar, min_eq_left h, max_eq_right h, Equiv.refl_apply]
    split_ifs <;> simp_all
  · refine ⟨Equiv.swap i j, ?_⟩
    intro p
    have h' : word (lower + 1) ≤ word lower := le_of_not_ge h
    by_cases hpi : p = i
    · subst p
      simp [compareScalar, i, j, min_eq_right h']
    · by_cases hpj : p = j
      · subst p
        simp [compareScalar, i, j, max_eq_left h']
      · have hpi' : p.val ≠ lower := fun hh => hpi (Fin.ext hh)
        have hpj' : p.val ≠ lower + 1 := fun hh => hpj (Fin.ext hh)
        simp [compareScalar, hpi', hpj', Equiv.swap_apply_of_ne_of_ne hpi hpj]

theorem scalarRunBits_permutation {α : Type*} [LinearOrder α] (q : ℕ)
    (centers : List ℕ) (hcenters : ∀ c ∈ centers, 0 < c ∧ c < q) (word : ℕ → α) :
    ∃ permutation : Equiv.Perm (Fin q),
      ∀ p : Fin q, scalarRunBits centers word p.val = word (permutation p).val := by
  induction centers generalizing word with
  | nil => exact ⟨Equiv.refl _, fun _ => rfl⟩
  | cons c rest ih =>
    have hc := hcenters c (by simp)
    have hr : ∀ c ∈ rest, 0 < c ∧ c < q := by
      intro c h
      exact hcenters c (by simp [h])
    obtain ⟨first, hf⟩ := compareScalar_permutation q (c - 1) (by omega) word
    obtain ⟨remaining, hr⟩ := ih hr (compareScalar (c - 1) word)
    refine ⟨remaining.trans first, ?_⟩
    intro p
    change scalarRunBits rest (compareScalar (c - 1) word) p.val = _
    rw [hr, hf]
    rfl

theorem scalarLayer_permutation {α : Type*} [LinearOrder α] (q parity : ℕ) (word : ℕ → α) :
    ∃ permutation : Equiv.Perm (Fin q),
      ∀ p : Fin q, scalarLayer q parity word p.val = word (permutation p).val := by
  apply scalarRunBits_permutation q (layerCenters q parity) _ word
  intro c hc
  have hh := (mem_layerCenters q parity c).mp hc
  exact ⟨hh.1, hh.2.1⟩

theorem scalarRun_permutation {α : Type*} [LinearOrder α] (q t : ℕ) (word : ℕ → α) :
    ∃ permutation : Equiv.Perm (Fin q),
      ∀ p : Fin q, scalarRun q t word p.val = word (permutation p).val := by
  induction t with
  | zero => exact ⟨Equiv.refl _, fun _ => rfl⟩
  | succ t ih =>
    obtain ⟨past, hpast⟩ := ih
    obtain ⟨first, hfirst⟩ := scalarLayer_permutation q 1 (scalarRun q t word)
    obtain ⟨second, hsecond⟩ := scalarLayer_permutation q 0 (scalarLayer q 1 (scalarRun q t word))
    refine ⟨(second.trans first).trans past, ?_⟩
    intro p
    change scalarLayer q 0 (scalarLayer q 1 (scalarRun q t word)) p.val = _
    rw [hsecond, hfirst, hpast]
    rfl

/-- Distinct comparators in one implemented layer occupy disjoint adjacent
pairs; the lower endpoints differ by at least two. -/
theorem layerCenters_separation (q parity c d : ℕ)
    (hc : c ∈ layerCenters q parity) (hd : d ∈ layerCenters q parity) (hne : c ≠ d) :
    (c - 1) + 1 < d - 1 ∨ (d - 1) + 1 < c - 1 := by
  have hc' := (mem_layerCenters q parity c).mp hc
  have hd' := (mem_layerCenters q parity d).mp hd
  omega

theorem layerCenters_length_le (q parity : ℕ) : (layerCenters q parity).length ≤ q := by
  exact (List.length_filter_le _ _).trans_eq List.length_range

/-- Actual static number of comparator invocations in the recursive program. -/
def comparisonCount (q : ℕ) : ℕ → ℕ
  | 0 => 0
  | t + 1 => comparisonCount q t + (layerCenters q 1).length + (layerCenters q 0).length

theorem comparisonCount_le (q t : ℕ) : comparisonCount q t ≤ 2 * q * t := by
  have h0 := layerCenters_length_le q 0
  have h1 := layerCenters_length_le q 1
  induction t with
  | zero => simp [comparisonCount]
  | succ t ih =>
    simp only [comparisonCount]
    nlinarith

theorem sorting_comparison_count_le (q : ℕ) : comparisonCount q q ≤ 2 * q ^ 2 := by
  simpa [pow_two, Nat.mul_assoc] using comparisonCount_le q q

/-- Sorting distinct target-position keys puts each key at its prescribed
port, so the concrete network realizes an arbitrary line permutation. -/
theorem line_permutation_routing (q : ℕ) (target : Equiv.Perm (Fin q))
    (word : ℕ → ℕ) (hword : ∀ i : Fin q, word i.val = (target i).val) :
    ∀ i : Fin q, scalarRun q q word i.val = i.val := by
  obtain ⟨permutation, hp⟩ := scalarRun_permutation q q word
  have hout : (fun i : Fin q => scalarRun q q word i.val) =
      Fin.val ∘ (permutation.trans target) := by
    funext i
    rw [hp, hword]
    rfl
  have hs := scalarRun_sorted q word
  rw [hout] at hs
  have hid : Monotone (Fin.val ∘ (Equiv.refl (Fin q))) := by
    intro a b hab
    exact hab
  have heq := Tuple.unique_monotone hs hid
  intro i
  have h := congrFun heq i
  rw [← hout] at h
  exact h

/-- A list of disjoint same-parity adjacent comparators executes exactly
its simultaneous min/max update. -/
theorem scalarRunBits_parallel {α : Type*} [LinearOrder α]
    (centers : List ℕ) (parity : ℕ) (hnodup : centers.Nodup)
    (hc : ∀ c ∈ centers, 0 < c ∧ c % 2 = parity % 2) (word : ℕ → α) (p : ℕ) :
    scalarRunBits centers word p =
      if p + 1 ∈ centers then min (word p) (word (p + 1))
      else if p ∈ centers then max (word (p - 1)) (word p) else word p := by
  induction centers generalizing word with
  | nil => simp [scalarRunBits]
  | cons c rest ih =>
    have hc0 := hc c (by simp)
    have hn := List.nodup_cons.mp hnodup
    have hr : ∀ c ∈ rest, 0 < c ∧ c % 2 = parity % 2 := by
      intro c h
      exact hc c (by simp [h])
    change scalarRunBits rest (compareScalar (c - 1) word) p = _
    rw [ih hn.2 hr]
    have he : c - 1 + 1 = c := by omega
    by_cases hp1 : p + 1 ∈ rest
    · have hpp := hr (p + 1) hp1
      have hne : c ≠ p + 1 := by intro heq; subst c; exact hn.1 hp1
      have h0 : p ≠ c - 1 := by omega
      have h1 : p ≠ c := by omega
      have h2 : p + 1 ≠ c - 1 := by omega
      have h3 : p + 1 ≠ c := by omega
      simp only [hp1, List.mem_cons, or_true, ↓reduceIte, compareScalar, he,
        h0, h1, h2, h3]
    · by_cases hp : p ∈ rest
      · have hpp := hr p hp
        have hne : c ≠ p := by intro heq; subst c; exact hn.1 hp
        have h0 : p - 1 ≠ c - 1 := by omega
        have h1 : p - 1 ≠ c := by omega
        have h2 : p ≠ c - 1 := by omega
        have h3 : p ≠ c := by omega
        have h4 : p + 1 ≠ c := by omega
        simp only [hp1, hp, List.mem_cons, or_false, or_true, h4, ↓reduceIte,
          compareScalar, he, h0, h1, h2, h3]
      · simp only [hp1, hp, List.mem_cons, or_false, ↓reduceIte, compareScalar, he]
        by_cases heq : p + 1 = c
        · have heq' : p = c - 1 := by omega
          simp only [heq', he, ↓reduceIte]
        · by_cases heq' : p = c
          · subst p
            have hne0 : c ≠ c - 1 := by omega
            have hne1 : c + 1 ≠ c := by omega
            simp only [hne0, hne1, ↓reduceIte]
          · have hne : p ≠ c - 1 := by omega
            simp only [heq, heq', hne, ↓reduceIte]

/-- Pointwise simultaneous form of the implemented parity layer. -/
theorem scalarLayer_parallel {α : Type*} [LinearOrder α] (q parity : ℕ) (word : ℕ → α) (p : ℕ) :
    scalarLayer q parity word p =
      if p + 1 ∈ layerCenters q parity then min (word p) (word (p + 1))
      else if p ∈ layerCenters q parity then max (word (p - 1)) (word p) else word p := by
  apply scalarRunBits_parallel (layerCenters q parity) parity
  · exact List.nodup_range.filter _
  · intro c hc
    have h := (mem_layerCenters q parity c).mp hc
    exact ⟨h.1, h.2.2⟩

end Maxwell.Logical.Routing.BinaryDepth
