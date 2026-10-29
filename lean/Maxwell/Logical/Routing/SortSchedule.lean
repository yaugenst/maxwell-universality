import Maxwell.Logical.Routing.BinaryDepth
import Maxwell.Logical.Routing.Schedule

/-! The concrete sorting decisions instantiate the cubic routing layers. -/

namespace Maxwell.Logical.Routing.SortSchedule

open Maxwell.Logical.Routing
open Maxwell.Logical.Routing.BinaryDepth
open Maxwell.Logical.Routing.Schedule

/-- Select exactly the inversions of the implemented parallel comparison layer. -/
def selection {α : Type*} [LinearOrder α] (q parity : ℕ) (word : ℕ → ℕ → α) :
    RowLayer.Selection q (parity + 1) where
  active c r := decide (c + 1 ∈ layerCenters q parity ∧ r < q ∧ word r (c + 1) < word r c)
  valid c r h := by
    have hh := of_decide_eq_true h
    have hc := (mem_layerCenters q parity (c + 1)).mp hh.1
    exact ⟨hc.2.1, hh.2.1, by omega⟩

@[simp] theorem selection_active {α : Type*} [LinearOrder α] (q parity : ℕ)
    (word : ℕ → ℕ → α) (c r : ℕ) :
    (selection q parity word).active c r = true ↔
      c + 1 ∈ layerCenters q parity ∧ r < q ∧ word r (c + 1) < word r c := by
  simp [selection]

/-- The key carried by a geometric path equals the comparator output key
at its computed destination. -/
theorem layer_transports_key {α : Type*} [LinearOrder α] (q parity : ℕ)
    (word : ℕ → ℕ → α) (p : Port q) :
    scalarLayer q parity (word p.2.val)
      (RowLayer.destination (selection q parity word) p).1.val = word p.2.val p.1.val := by
  cases hm : RowLayer.movement (selection q parity word) p with
  | idle =>
    have hi := RowLayer.idle_info (selection q parity word) p hm
    simp only [RowLayer.destination, RowLayer.destinationColumn, hm]
    rw [scalarLayer_parallel]
    by_cases hc : p.1.val + 1 ∈ layerCenters q parity
    · have hn : ¬word p.2.val (p.1.val + 1) < word p.2.val p.1.val := by
        intro hlt
        exact hi.1 ((selection_active _ _ _ _ _).mpr ⟨hc, p.2.isLt, hlt⟩)
      simp only [hc, ↓reduceIte, min_eq_left (le_of_not_gt hn)]
    · by_cases hc' : p.1.val ∈ layerCenters q parity
      · have hpos := ((mem_layerCenters q parity p.1.val).mp hc').1
        have he : p.1.val - 1 + 1 = p.1.val := by omega
        have hn : ¬word p.2.val p.1.val < word p.2.val (p.1.val - 1) := by
          intro hlt
          apply hi.2
          refine ⟨hpos, (selection_active _ _ _ _ _).mpr ?_⟩
          simpa only [he] using And.intro hc' (And.intro p.2.isLt hlt)
        simp only [hc, hc', ↓reduceIte, max_eq_right (le_of_not_gt hn)]
      · simp only [hc, hc', ↓reduceIte]
  | exchange lower strand =>
    have hh := RowLayer.exchange_info (selection q parity word) p lower strand hm
    have hs := (selection_active _ _ _ _ _).mp hh.1
    have hc := (mem_layerCenters q parity (lower + 1)).mp hs.1
    have hn : lower + 2 ∉ layerCenters q parity := by
      intro h
      have h' := (mem_layerCenters q parity (lower + 2)).mp h
      omega
    cases strand
    · simp only [Bool.false_eq_true, ↓reduceIte] at hh
      simp only [RowLayer.destination, RowLayer.destinationColumn, hm, Bool.false_eq_true, ↓reduceIte]
      rw [scalarLayer_parallel]
      simp only [hs.1, ↓reduceIte, min_eq_right (le_of_lt hs.2.2), hh.2]
    · simp only [↓reduceIte] at hh
      simp only [RowLayer.destination, RowLayer.destinationColumn, hm, ↓reduceIte]
      rw [scalarLayer_parallel]
      simp only [Nat.add_assoc, Nat.reduceAdd, hn, hs.1, ↓reduceIte,
        Nat.add_sub_cancel, max_eq_left (le_of_lt hs.2.2), hh.2]

/-- Keys after each actual odd-even layer, separately for every row. -/
def keyState {α : Type*} [LinearOrder α] (q : ℕ) (word : ℕ → ℕ → α) :
    ℕ → ℕ → ℕ → α
  | 0 => word
  | t + 1 => fun r => scalarLayer q ((t + 1) % 2) (keyState q word t r)

/-- Two consecutive geometric layers execute one proved sorting round. -/
theorem keyState_even {α : Type*} [LinearOrder α] (q : ℕ)
    (word : ℕ → ℕ → α) (t r : ℕ) :
    keyState q word (2 * t) r = scalarRun q t (word r) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have he : 2 * (t + 1) = (2 * t + 1) + 1 := by omega
    have h0 : (2 * t + 1 + 1) % 2 = 0 := by omega
    have h1 : (2 * t + 1) % 2 = 1 := by omega
    simp only [he, keyState, h0, h1, ih, scalarRun, scalarRound]

/-- Actual row-sort schedule; every swap decision is computed from the keys. -/
def rowSchedule {α : Type*} [LinearOrder α] (q : ℕ)
    (word : ℕ → ℕ → α) (t : ℕ) : CubicLayer q :=
  rowLayer (selection q ((t + 1) % 2) (keyState q word t))

theorem rowSchedule_preserves_row {α : Type*} [LinearOrder α] (q : ℕ)
    (word : ℕ → ℕ → α) (t : ℕ) (p : Port q) :
    (placement (rowSchedule q word) t p).2 = p.2 := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change (RowLayer.destination _ (placement (rowSchedule q word) t p)).2 = p.2
    exact ih

/-- The keys on all constructed trajectories satisfy the exact sorting
recurrence at every layer, with no endpoint premise. -/
theorem rowSchedule_transports_key {α : Type*} [LinearOrder α] (q : ℕ)
    (word : ℕ → ℕ → α) (t : ℕ) (p : Port q) :
    keyState q word t p.2.val (placement (rowSchedule q word) t p).1.val =
      word p.2.val p.1.val := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hh := layer_transports_key q ((t + 1) % 2) (keyState q word t)
      (placement (rowSchedule q word) t p)
    rw [rowSchedule_preserves_row] at hh
    change scalarLayer q ((t + 1) % 2) (keyState q word t p.2.val)
      (RowLayer.destination _ (placement (rowSchedule q word) t p)).1.val = _
    exact hh.trans ih

/-- The destination-key permutation on one row of a row-preserving target. -/
noncomputable def rowTarget {q : ℕ} (target : Equiv.Perm (Port q))
    (hrow : ∀ p, (target p).2 = p.2) (r : Fin q) : Equiv.Perm (Fin q) :=
  Equiv.ofBijective (fun c => (target (c, r)).1) (by
    apply Finite.injective_iff_bijective.mp
    intro a b hab
    have hh : target (a, r) = target (b, r) := by
      apply Prod.ext hab
      rw [hrow, hrow]
    exact congrArg Prod.fst (target.injective hh))

/-- Total extension of the prescribed destination-column keys. -/
def targetKeys {q : ℕ} (target : Equiv.Perm (Port q)) (r c : ℕ) : ℕ :=
  if hr : r < q then if hc : c < q then (target (⟨c, hc⟩, ⟨r, hr⟩)).1.val else 0 else 0

@[simp] theorem targetKeys_at {q : ℕ} (target : Equiv.Perm (Port q)) (c r : Fin q) :
    targetKeys target r.val c.val = (target (c, r)).1.val := by
  simp [targetKeys, c.isLt, r.isLt]

/-- After exactly 2q computed geometric layers, every token reaches its
prescribed port for an arbitrary row-preserving permutation. -/
theorem rowSchedule_routes_target {q : ℕ} (target : Equiv.Perm (Port q))
    (hrow : ∀ p, (target p).2 = p.2) :
    placement (rowSchedule q (targetKeys target)) (2 * q) = target := by
  apply Equiv.ext
  intro p
  have hh := rowSchedule_transports_key q (targetKeys target) (2 * q) p
  rw [keyState_even] at hh
  have hs := line_permutation_routing q (rowTarget target hrow p.2)
    (targetKeys target p.2.val) (fun i => targetKeys_at target i p.2)
    (placement (rowSchedule q (targetKeys target)) (2 * q) p).1
  rw [hs, targetKeys_at] at hh
  apply Prod.ext
  · exact Fin.ext hh
  · rw [rowSchedule_preserves_row, hrow]

/-- Transpose the prescribed array permutation. -/
def transposedTarget {q : ℕ} (target : Equiv.Perm (Port q)) : Equiv.Perm (Port q) :=
  ((swapPorts q).trans target).trans (swapPorts q)

/-- Concrete transposed sorting layers for a column-preserving target. -/
def columnSchedule {q : ℕ} (target : Equiv.Perm (Port q)) (t : ℕ) : CubicLayer q :=
  columnLayer (selection q ((t + 1) % 2) (keyState q (targetKeys (transposedTarget target)) t))

theorem columnSchedule_placement {q : ℕ} (target : Equiv.Perm (Port q)) (t : ℕ) :
    placement (columnSchedule target) t =
      ((swapPorts q).trans (placement (rowSchedule q (targetKeys (transposedTarget target))) t)).trans
        (swapPorts q) := by
  apply Equiv.ext
  intro p
  induction t with
  | zero => rfl
  | succ t ih =>
    change (swapPorts q) ((rowSchedule q (targetKeys (transposedTarget target)) t).next
      ((swapPorts q) (placement (columnSchedule target) t p))) = _
    rw [ih]
    rfl

/-- Exactly 2q actual column-sort layers realize any column-preserving permutation. -/
theorem columnSchedule_routes_target {q : ℕ} (target : Equiv.Perm (Port q))
    (hcol : ∀ p, (target p).1 = p.1) : placement (columnSchedule target) (2 * q) = target := by
  have hr : ∀ p, (transposedTarget target p).2 = p.2 := by
    intro p
    exact hcol (swapPorts q p)
  rw [columnSchedule_placement, rowSchedule_routes_target _ hr]
  apply Equiv.ext
  intro p
  rfl

/-- Append two concrete schedules at a prescribed slab boundary. -/
def appendSchedule {q : ℕ} (first second : ℕ → CubicLayer q) (cut : ℕ)
    (t : ℕ) : CubicLayer q := if t < cut then first t else second (t - cut)

theorem placement_congr {q : ℕ} (first second : ℕ → CubicLayer q) (t : ℕ)
    (h : ∀ s < t, first s = second s) : placement first t = placement second t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [placement, placement, ih (fun s hs => h s (by omega)), h t (by omega)]

/-- Concatenation composes the actual endpoint permutations. -/
theorem placement_append {q : ℕ} (first second : ℕ → CubicLayer q) (cut t : ℕ) :
    placement (appendSchedule first second cut) (cut + t) =
      (placement first cut).trans (placement second t) := by
  induction t with
  | zero =>
    simpa only [Nat.add_zero, placement, Equiv.trans_refl] using
      placement_congr (appendSchedule first second cut) first cut
        (fun s hs => by simp only [appendSchedule, hs, ↓reduceIte])
  | succ t ih =>
    have he : cut + (t + 1) = (cut + t) + 1 := by omega
    have hn : ¬ cut + t < cut := by omega
    rw [he, placement, ih]
    simp only [appendSchedule, hn, ↓reduceIte, Nat.add_sub_cancel_left, placement,
      Equiv.trans_assoc]

/-- The full computed row-column-row schedule, with exactly 6q slabs. -/
noncomputable def permutationSchedule {q : ℕ} {target : Equiv.Perm (Port q)}
    (colors : RowColoring target) : ℕ → CubicLayer q :=
  appendSchedule (rowSchedule q (targetKeys (firstPermutation colors)))
    (appendSchedule (columnSchedule (columnPhase colors))
      (rowSchedule q (targetKeys (finalRowPhase colors))) (2 * q)) (2 * q)

/-- The actual geometric schedule realizes every target with the supplied
proper row coloring. Sorting and path endpoint correctness are conclusions. -/
theorem permutationSchedule_routes_target {q : ℕ} {target : Equiv.Perm (Port q)}
    (colors : RowColoring target) : placement (permutationSchedule colors) (6 * q) = target := by
  have he : 6 * q = 2 * q + (2 * q + 2 * q) := by omega
  rw [he, permutationSchedule, placement_append, placement_append,
    rowSchedule_routes_target _ (first_phase_preserves_row colors),
    columnSchedule_routes_target _ (column_phase_preserves_column colors),
    rowSchedule_routes_target _ (final_phase_preserves_row colors)]
  apply Equiv.ext
  exact three_phase_routing colors

/-- Every emitted token trajectory in the full permutation network is simple,
and all different token trajectories are disjoint. -/
theorem permutationSchedule_trajectory_injective {q : ℕ} {target : Equiv.Perm (Port q)}
    (colors : RowColoring target) :
    Function.Injective (fun entry : Σ token, Assembly.TrajectoryIndex
        (routes (permutationSchedule colors) (6 * q)) token =>
      Assembly.trajectoryPoint (routes (permutationSchedule colors) (6 * q)) entry.1 entry.2) :=
  schedule_trajectory_injective _ _

/-- The length bound counts the actual concatenated path edges. -/
theorem permutationSchedule_trajectoryLength_le {q : ℕ} {target : Equiv.Perm (Port q)}
    (colors : RowColoring target) (token : Port q) :
    trajectoryLength (permutationSchedule colors) (6 * q) token ≤ 240 * q := by
  simpa only [← Nat.mul_assoc] using trajectoryLength_le (permutationSchedule colors) (6 * q) token

/-- The common horizontal lattice box for both layer orientations. -/
def InHorizontalBox (q : ℕ) (point : Point) : Prop :=
  -4 ≤ point.1 ∧ point.1 ≤ 16 * q + 4 ∧
  -4 ≤ point.2.1 ∧ point.2.1 ≤ 16 * q + 4

theorem rowLayer_horizontal_bounds {q parity : ℕ} (selected : RowLayer.Selection q parity)
    (p : Port q) (t : ℕ) : InHorizontalBox q ((rowLayer selected).point p t) := by
  cases hm : RowLayer.movement selected p with
  | idle =>
    have hc := p.1.isLt
    have hr := p.2.isLt
    change InHorizontalBox q (RowLayer.pathPoint selected p t)
    simp only [RowLayer.pathPoint, hm, InHorizontalBox]
    omega
  | exchange lower strand =>
    have hs := selected.valid lower p.2.val (RowLayer.exchange_info selected p lower strand hm).1
    have hb := swap_xy_bounds strand ⟨min t 40, by omega⟩
    change InHorizontalBox q (RowLayer.pathPoint selected p t)
    simp only [RowLayer.pathPoint, hm, RowLayer.swapSample, translate, InHorizontalBox]
    omega

theorem columnLayer_horizontal_bounds {q parity : ℕ} (selected : RowLayer.Selection q parity)
    (p : Port q) (t : ℕ) : InHorizontalBox q ((columnLayer selected).point p t) := by
  have hh := rowLayer_horizontal_bounds selected (swapPorts q p) t
  exact ⟨hh.2.2.1, hh.2.2.2, hh.1, hh.2.1⟩

theorem permutationSchedule_horizontal_bounds {q : ℕ} {target : Equiv.Perm (Port q)}
    (colors : RowColoring target) (level : ℕ) (p : Port q) (t : ℕ) :
    InHorizontalBox q ((permutationSchedule colors level).point p t) := by
  unfold permutationSchedule appendSchedule
  split_ifs
  · exact rowLayer_horizontal_bounds _ _ _
  · exact columnLayer_horizontal_bounds _ _ _
  · exact rowLayer_horizontal_bounds _ _ _

/-- Every actually stored network vertex lies in the asserted common box. -/
theorem permutationSchedule_box {q : ℕ} {target : Equiv.Perm (Port q)}
    (colors : RowColoring target) (token : Port q)
    (index : Assembly.TrajectoryIndex (routes (permutationSchedule colors) (6 * q)) token) :
    let point := Assembly.trajectoryPoint (routes (permutationSchedule colors) (6 * q)) token index
    InHorizontalBox q point ∧ 0 ≤ point.2.2 ∧ point.2.2 ≤ 96 * q := by
  cases index with
  | inl step =>
    rcases step with ⟨level, step⟩
    have hh := permutationSchedule_horizontal_bounds colors level.val
      (placement (permutationSchedule colors) level.val token) step.val
    have hz := (routes (permutationSchedule colors) (6 * q)).slab level token step.val (by omega)
    have hl := level.isLt
    change InHorizontalBox q (translate (0, 0, 16 * (level.val : ℤ))
        ((permutationSchedule colors level.val).point
          (placement (permutationSchedule colors) level.val token) step.val)) ∧ _
    constructor
    · simpa only [InHorizontalBox, translate, zero_add] using hh
    · simp only [Assembly.trajectoryPoint]
      omega
  | inr terminal =>
    change InHorizontalBox q (gridPort (placement (permutationSchedule colors) (6 * q) token)
      (16 * (6 * q : ℕ))) ∧ _
    have hc := (placement (permutationSchedule colors) (6 * q) token).1.isLt
    have hr := (placement (permutationSchedule colors) (6 * q) token).2.isLt
    simp only [InHorizontalBox, gridPort, Assembly.trajectoryPoint, routes, Fin.val_last]
    push_cast
    omega

end Maxwell.Logical.Routing.SortSchedule
