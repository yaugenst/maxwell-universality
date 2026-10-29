import Maxwell.Logical.Routing

/-! Concrete paths for one selected odd-even row-comparison layer. -/

namespace Maxwell.Logical.Routing.RowLayer

open Maxwell.Logical.Routing

/-- The selected swaps of one row-parity layer.  Bounds and parity are
properties of selected comparisons, rather than a global routing premise. -/
structure Selection (q parity : ℕ) where
  active : ℕ → ℕ → Bool
  valid : ∀ c r, active c r = true → c + 1 < q ∧ r < q ∧ c % 2 = parity % 2

inductive Move where
  | idle
  | exchange (lower : ℕ) (strand : Bool)
  deriving DecidableEq

/-- Classify a port as the lower endpoint, upper endpoint, or stationary. -/
def movement {q parity : ℕ} (selected : Selection q parity) (port : Port q) : Move :=
  if selected.active port.1.val port.2.val then .exchange port.1.val true
  else if 0 < port.1.val ∧ selected.active (port.1.val - 1) port.2.val = true then
    .exchange (port.1.val - 1) false
  else .idle

theorem exchange_info {q parity : ℕ} (selected : Selection q parity)
    (port : Port q) (lower : ℕ) (strand : Bool)
    (h : movement selected port = .exchange lower strand) :
    selected.active lower port.2.val = true ∧
      port.1.val = if strand then lower else lower + 1 := by
  unfold movement at h
  split_ifs at h with ha hb
  · cases h
    exact ⟨ha, rfl⟩
  · cases h
    exact ⟨hb.2, by simp; omega⟩

theorem idle_info {q parity : ℕ} (selected : Selection q parity) (port : Port q)
    (h : movement selected port = .idle) :
    selected.active port.1.val port.2.val ≠ true ∧
      ¬ (0 < port.1.val ∧ selected.active (port.1.val - 1) port.2.val = true) := by
  unfold movement at h
  split_ifs at h with ha hb
  exact ⟨ha, hb⟩

/-- Selected pairs on one row have the geometric gap required by the swap boxes. -/
theorem selected_pair_separation {q parity : ℕ} (selected : Selection q parity)
    (c d r s : ℕ) (hc : selected.active c r = true) (hd : selected.active d s = true)
    (hne : c ≠ d ∨ r ≠ s) : (r : ℤ) ≠ s ∨ (c : ℤ) + 1 < d ∨ (d : ℤ) + 1 < c := by
  have hcp := selected.valid c r hc
  have hdp := selected.valid d s hd
  omega

/-- A stationary port lies outside every selected pair in its row. -/
theorem idle_pair_separation {q parity : ℕ} (selected : Selection q parity)
    (port : Port q) (c r : ℕ) (hc : selected.active c r = true)
    (hidle : movement selected port = .idle) :
    (r : ℤ) ≠ port.2.val ∨ (port.1.val : ℤ) < c ∨ (c : ℤ) + 1 < port.1.val := by
  have hi := idle_info selected port hidle
  by_cases hr : r = port.2.val
  · subst r
    have hne : port.1.val ≠ c := by intro he; rw [he] at hi; exact hi.1 hc
    have hne' : port.1.val ≠ c + 1 := by
      intro he
      apply hi.2
      refine ⟨by omega, ?_⟩
      have he' : port.1.val - 1 = c := by omega
      simpa only [he'] using hc
    omega
  · omega

/-- Clamped extension makes the fixed finite swap a total sample function;
all valid samples have indices at most 40. -/
def swapSample (strand : Bool) (t : ℕ) : Point :=
  swap strand ⟨min t 40, by omega⟩

def pathLength {q parity : ℕ} (selected : Selection q parity) (port : Port q) : ℕ :=
  match movement selected port with
  | .idle => 16
  | .exchange _ _ => 40

def pathPoint {q parity : ℕ} (selected : Selection q parity) (port : Port q) (t : ℕ) : Point :=
  match movement selected port with
  | .idle => (16 * port.1.val, 16 * port.2.val, t)
  | .exchange lower strand => translate (16 * lower, 16 * port.2.val, 0) (swapSample strand t)

lemma swapSample_injective {strand : Bool} {i j : ℕ} (hi : i ≤ 40) (hj : j ≤ 40)
    (he : swapSample strand i = swapSample strand j) : i = j := by
  have hinj : Function.Injective (swap strand) := by
    cases strand
    · exact swap_simple_disjoint.2.1
    · exact swap_simple_disjoint.1
  have hh := congrArg Fin.val (hinj he)
  simpa only [Nat.min_eq_left hi, Nat.min_eq_left hj] using hh

lemma swapSample_distinct_strands (i j : ℕ) : swapSample true i ≠ swapSample false j :=
  swap_simple_disjoint.2.2 _ _

/-- All concrete layer paths are pairwise disjoint and individually simple. -/
theorem pathPoint_injective {q parity : ℕ} (selected : Selection q parity)
    (a b : Port q) (i j : ℕ) (hi : i ≤ pathLength selected a) (hj : j ≤ pathLength selected b)
    (he : pathPoint selected a i = pathPoint selected b j) : a = b ∧ i = j := by
  cases ha : movement selected a with
  | idle =>
    cases hb : movement selected b with
    | idle =>
      simp only [pathPoint, ha, hb, Prod.mk.injEq] at he
      have hp : a = b := by
        apply Prod.ext <;> apply Fin.ext <;> omega
      exact ⟨hp, by omega⟩
    | exchange c strand =>
      have hc := (exchange_info selected b c strand hb).1
      have hsep := idle_pair_separation selected a c b.2.val hc ha
      have hne := row_swap_stationary_disjoint c a.1.val b.2.val a.2.val 0 i hsep
        strand ⟨min j 40, by omega⟩
      apply False.elim
      apply hne
      simpa only [pathPoint, ha, hb, rowSwap, swapSample] using he.symm
  | exchange c strand =>
    cases hb : movement selected b with
    | idle =>
      have hc := (exchange_info selected a c strand ha).1
      have hsep := idle_pair_separation selected b c a.2.val hc hb
      have hne := row_swap_stationary_disjoint c b.1.val a.2.val b.2.val 0 j hsep
        strand ⟨min i 40, by omega⟩
      apply False.elim
      apply hne
      simpa only [pathPoint, ha, hb, rowSwap, swapSample] using he
    | exchange d other =>
      have hca := exchange_info selected a c strand ha
      have hdb := exchange_info selected b d other hb
      by_cases hsame : c = d ∧ a.2.val = b.2.val
      · obtain ⟨hcd, hr⟩ := hsame
        subst d
        have htr : (16 * (c : ℤ), 16 * (a.2.val : ℤ), (0 : ℤ)) =
            (16 * (c : ℤ), 16 * (b.2.val : ℤ), (0 : ℤ)) := by rw [hr]
        simp only [pathPoint, ha, hb, ← htr] at he
        have hs := translate_injective _ he
        have hstrand : strand = other := by
          cases strand <;> cases other
          · rfl
          · exact False.elim (swapSample_distinct_strands j i hs.symm)
          · exact False.elim (swapSample_distinct_strands i j hs)
          · rfl
        subst other
        have hp : a = b := by
          apply Prod.ext
          · apply Fin.ext
            rw [hca.2, hdb.2]
          · exact Fin.ext hr
        have hi' : i ≤ 40 := by simpa only [pathLength, ha] using hi
        have hj' : j ≤ 40 := by simpa only [pathLength, hb] using hj
        exact ⟨hp, swapSample_injective hi' hj' hs⟩
      · have hne : c ≠ d ∨ a.2.val ≠ b.2.val := by omega
        have hsep := selected_pair_separation selected c d a.2.val b.2.val hca.1 hdb.1 hne
        have hdisj := parallel_row_swaps_disjoint c d a.2.val b.2.val 0 hsep strand other
          ⟨min i 40, by omega⟩ ⟨min j 40, by omega⟩
        apply False.elim
        apply hdisj
        simpa only [pathPoint, ha, hb, rowSwap, swapSample] using he

theorem swapSample_steps (strand : Bool) (t : ℕ) (ht : t < 40) :
    UnitAdjacent (swapSample strand t) (swapSample strand (t + 1)) := by
  have ht0 : min t 40 = t := by omega
  have ht1 : min (t + 1) 40 = t + 1 := by omega
  cases strand
  · simpa only [swapSample, swap, Bool.false_eq_true, ↓reduceIte, ht0, ht1, Fin.castSucc, Fin.castAdd, Fin.castLE, Fin.succ]
      using swap_unit_steps.2 ⟨t, ht⟩
  · simpa only [swapSample, swap, ↓reduceIte, ht0, ht1, Fin.castSucc, Fin.castAdd, Fin.castLE, Fin.succ]
      using swap_unit_steps.1 ⟨t, ht⟩

lemma swapSample_z_bounds (strand : Bool) (t : ℕ) :
    0 ≤ (swapSample strand t).2.2 ∧ (swapSample strand t).2.2 ≤ 16 := by
  cases strand
  · exact (swap_bounds ⟨min t 40, by omega⟩).2.2.2.2.2
  · exact (swap_bounds ⟨min t 40, by omega⟩).1.2.2.2.2

lemma swapSample_z_faces (strand : Bool) (t : ℕ) (ht : t ≤ 40) :
    ((swapSample strand t).2.2 = 0 ↔ t = 0) ∧ ((swapSample strand t).2.2 = 16 ↔ t = 40) := by
  have h : ∀ (a : Bool) (i : Fin 41),
      ((swap a i).2.2 = 0 ↔ i.val = 0) ∧ ((swap a i).2.2 = 16 ↔ i.val = 40) := by decide
  simpa only [swapSample, Nat.min_eq_left ht] using h strand ⟨min t 40, by omega⟩

/-- Every emitted row-path segment is a genuine unit lattice edge. -/
theorem pathPoint_steps {q parity : ℕ} (selected : Selection q parity) (port : Port q)
    (t : ℕ) (ht : t < pathLength selected port) :
    UnitAdjacent (pathPoint selected port t) (pathPoint selected port (t + 1)) := by
  cases hm : movement selected port with
  | idle => simp [pathPoint, hm, UnitAdjacent]
  | exchange lower strand =>
    have ht' : t < 40 := by simpa only [pathLength, hm] using ht
    simp only [pathPoint, hm]
    exact (translate_unit_adjacent _ _ _).mpr (swapSample_steps strand t ht')

theorem pathPoint_slab {q parity : ℕ} (selected : Selection q parity) (port : Port q)
    (t : ℕ) (ht : t ≤ pathLength selected port) :
    0 ≤ (pathPoint selected port t).2.2 ∧ (pathPoint selected port t).2.2 ≤ 16 := by
  cases hm : movement selected port with
  | idle =>
    have ht' : t ≤ 16 := by simpa only [pathLength, hm] using ht
    simp only [pathPoint, hm]
    omega
  | exchange lower strand =>
    simpa only [pathPoint, hm, translate, zero_add] using swapSample_z_bounds strand t

theorem pathPoint_faces {q parity : ℕ} (selected : Selection q parity) (port : Port q)
    (t : ℕ) (ht : t ≤ pathLength selected port) :
    ((pathPoint selected port t).2.2 = 0 ↔ t = 0) ∧
      ((pathPoint selected port t).2.2 = 16 ↔ t = pathLength selected port) := by
  cases hm : movement selected port with
  | idle => simp only [pathPoint, pathLength, hm]; norm_cast
  | exchange lower strand =>
    have ht' : t ≤ 40 := by simpa only [pathLength, hm] using ht
    simpa only [pathPoint, pathLength, hm, translate, zero_add] using swapSample_z_faces strand t ht'

/-- Destination column of the local comparison decision. -/
def destinationColumn {q parity : ℕ} (selected : Selection q parity) (port : Port q) : ℕ :=
  match movement selected port with
  | .idle => port.1.val
  | .exchange lower strand => if strand then lower + 1 else lower

theorem destinationColumn_lt {q parity : ℕ} (selected : Selection q parity) (port : Port q) :
    destinationColumn selected port < q := by
  cases hm : movement selected port with
  | idle => simpa only [destinationColumn, hm] using port.1.isLt
  | exchange lower strand =>
    have h := selected.valid lower port.2.val (exchange_info selected port lower strand hm).1
    cases strand <;> simp only [destinationColumn, hm, Bool.false_eq_true, ↓reduceIte] <;> omega

/-- The computed destination port of the local swap/stationary decision. -/
def destination {q parity : ℕ} (selected : Selection q parity) (port : Port q) : Port q :=
  (⟨destinationColumn selected port, destinationColumn_lt selected port⟩, port.2)

theorem pathPoint_first {q parity : ℕ} (selected : Selection q parity) (port : Port q) :
    pathPoint selected port 0 = (16 * (port.1.val : ℤ), 16 * (port.2.val : ℤ), 0) := by
  cases hm : movement selected port with
  | idle => simp [pathPoint, hm]
  | exchange lower strand =>
    have h := (exchange_info selected port lower strand hm).2
    cases strand
    · simp only [Bool.false_eq_true, ↓reduceIte] at h
      simp [pathPoint, hm, swapSample, swap, swapB, translate, h]
      ring
    · simp only [↓reduceIte] at h
      simp [pathPoint, hm, swapSample, swap, swapA, translate, h]

theorem pathPoint_last {q parity : ℕ} (selected : Selection q parity) (port : Port q) :
    pathPoint selected port (pathLength selected port) =
      (16 * ((destination selected port).1.val : ℤ), 16 * ((destination selected port).2.val : ℤ), 16) := by
  cases hm : movement selected port with
  | idle => simp [pathPoint, pathLength, destination, destinationColumn, hm]
  | exchange lower strand =>
    cases strand
    · simp [pathPoint, pathLength, destination, destinationColumn, hm, swapSample, swap, swapB, translate]
    · simp [pathPoint, pathLength, destination, destinationColumn, hm, swapSample, swap, swapA, translate]
      ring

/-- Geometric disjointness proves the computed destination map is injective. -/
theorem destination_injective {q parity : ℕ} (selected : Selection q parity) :
    Function.Injective (destination selected) := by
  intro a b he
  have hpoints : pathPoint selected a (pathLength selected a) =
      pathPoint selected b (pathLength selected b) := by rw [pathPoint_last, pathPoint_last, he]
  exact (pathPoint_injective selected a b _ _ le_rfl le_rfl hpoints).1

/-- Selected adjacent pairs are disjoint, so applying the layer twice restores
every port.  The inverse permutation is the same explicit destination map. -/
theorem destination_involutive {q parity : ℕ} (selected : Selection q parity) :
    Function.Involutive (destination selected) := by
  intro port
  cases hm : movement selected port with
  | idle =>
    have hd : destination selected port = port := by
      apply Prod.ext
      · apply Fin.ext
        simp only [destination, destinationColumn, hm]
      · rfl
    rw [hd, hd]
  | exchange lower strand =>
    have hi := exchange_info selected port lower strand hm
    have hv := selected.valid lower port.2.val hi.1
    cases strand
    · have hd : (destination selected port).1.val = lower := by
        simp only [destination, destinationColumn, hm, Bool.false_eq_true, ↓reduceIte]
      have hn : movement selected (destination selected port) = .exchange lower true := by
        unfold movement
        rw [hd]
        change (if selected.active lower port.2.val = true then _ else _) = _
        simp only [hi.1, ↓reduceIte]
      apply Prod.ext
      · apply Fin.ext
        change destinationColumn selected (destination selected port) = port.1.val
        rw [destinationColumn, hn]
        simpa only [Bool.false_eq_true, ↓reduceIte] using hi.2.symm
      · rfl
    · have ha : selected.active (lower + 1) port.2.val ≠ true := by
        intro hh
        have hh' := selected.valid (lower + 1) port.2.val hh
        omega
      have hd : (destination selected port).1.val = lower + 1 := by
        simp only [destination, destinationColumn, hm, ↓reduceIte]
      have hn : movement selected (destination selected port) = .exchange lower false := by
        have hr : (destination selected port).2 = port.2 := rfl
        simp [movement, hd, hr, ha, hi.1]
      apply Prod.ext
      · apply Fin.ext
        change destinationColumn selected (destination selected port) = port.1.val
        rw [destinationColumn, hn]
        simpa only [Bool.false_eq_true, ↓reduceIte] using hi.2.symm
      · rfl

def destinationPermutation {q parity : ℕ} (selected : Selection q parity) :
    Equiv.Perm (Port q) where
  toFun := destination selected
  invFun := destination selected
  left_inv := destination_involutive selected
  right_inv := destination_involutive selected

theorem destination_preserves_row {q parity : ℕ} (selected : Selection q parity) (port : Port q) :
    (destination selected port).2 = port.2 := by
  rfl

end Maxwell.Logical.Routing.RowLayer
