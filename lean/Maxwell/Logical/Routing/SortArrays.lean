import Maxwell.Logical.Routing.SortSchedule
import Maxwell.Logical.Routing.PhaseArrays
import Mathlib.Logic.Equiv.Fin.Basic

/-! Stored arrays for every odd-even layer. The comparison formula uses
arithmetic parity tests, so each output has constant many saved-array reads. -/

namespace Maxwell.Logical.Routing.SortArrays

open Maxwell.Logical.Routing.BinaryDepth
open Maxwell.Logical.Routing.SortSchedule
open Maxwell.Logical.Routing.Schedule

abbrev Keys (q : ℕ) := Vector ℕ (q * q)

theorem get_ofFn {α : Type*} {n : ℕ} (f : Fin n → α) (i : Fin n) :
    (Vector.ofFn f).get i = f i := by simp [Vector.get, Fin.cast]

def keyAt {q : ℕ} (keys : Keys q) (port : Port q) : ℕ :=
  keys.get (finProdFinEquiv port)

def word {q : ℕ} (keys : Keys q) (row col : ℕ) : ℕ :=
  if hr : row < q then if hc : col < q then keyAt keys (⟨col, hc⟩, ⟨row, hr⟩) else 0 else 0

@[simp] theorem word_at {q : ℕ} (keys : Keys q) (port : Port q) :
    word keys port.2.val port.1.val = keyAt keys port := by simp [word]

/-- Constant-size arithmetic test for a comparison's right endpoint. -/
def center (q parity col : ℕ) : Bool := decide (0 < col ∧ col < q ∧ col % 2 = parity % 2)

@[simp] theorem center_true (q parity col : ℕ) :
    center q parity col = true ↔ col ∈ layerCenters q parity := by
  simp only [center, decide_eq_true_eq, mem_layerCenters]

/-- Materialize the simultaneous min/max output from one saved input array. -/
def step {q : ℕ} (parity : ℕ) (saved : Keys q) : Keys q :=
  Vector.ofFn (fun i =>
    let port : Port q := finProdFinEquiv.symm i
    let w := word saved port.2.val
    if center q parity (port.1.val + 1) then min (w port.1.val) (w (port.1.val + 1))
    else if center q parity port.1.val then max (w (port.1.val - 1)) (w port.1.val)
    else w port.1.val)

theorem step_at {q : ℕ} (parity : ℕ) (saved : Keys q) (port : Port q) :
    keyAt (step parity saved) port = scalarLayer q parity (word saved port.2.val) port.1.val := by
  rw [scalarLayer_parallel]
  simp only [keyAt, step, get_ofFn, Equiv.symm_apply_apply, center_true]

theorem step_word {q : ℕ} (parity : ℕ) (saved : Keys q) (row col : ℕ) :
    word (step parity saved) row col = scalarLayer q parity (word saved row) col := by
  by_cases hr : row < q
  · by_cases hc : col < q
    · simpa only [word, hr, hc, ↓reduceDIte] using step_at parity saved (⟨col, hc⟩, ⟨row, hr⟩)
    · have h0 : col ∉ layerCenters q parity := by
        intro hh
        exact hc (mem_layerCenters q parity col |>.mp hh).2.1
      have h1 : col + 1 ∉ layerCenters q parity := by
        intro hh
        have := (mem_layerCenters q parity (col + 1) |>.mp hh).2.1
        omega
      simp only [scalarLayer_parallel, h0, h1, ↓reduceIte, word, hr, hc, ↓reduceDIte]
  · simp only [word, hr, ↓reduceDIte, scalarLayer_parallel]
    split_ifs <;> rfl

/-- Execute the actual array recurrence with one saved state per round. -/
def run {q : ℕ} (initial : Keys q) : ℕ → Keys q
  | 0 => initial
  | t + 1 => let saved := run initial t; step ((t + 1) % 2) saved

/-- Array execution agrees with the fully proved scalar sorting recurrence. -/
theorem run_word {q : ℕ} (initial : Keys q) (t row col : ℕ) :
    word (run initial t) row col = keyState q (word initial) t row col := by
  induction t generalizing col with
  | zero => rfl
  | succ t ih =>
    simp only [run, keyState, step_word]
    congr 1
    funext i
    exact ih i

/-- Store the history once; later geometry queries read one array at a known layer. -/
def history {q : ℕ} (initial : Keys q) : (steps : ℕ) → Vector (Keys q) (steps + 1)
  | 0 => Vector.replicate 1 initial
  | t + 1 =>
      let saved := history initial t
      saved.push (step ((t + 1) % 2) (saved.get (Fin.last t)))

/-- Every stored layer is exactly the corresponding executed array state. -/
theorem history_get {q : ℕ} (initial : Keys q) (steps : ℕ) (i : Fin (steps + 1)) :
    (history initial steps).get i = run initial i.val := by
  induction steps with
  | zero =>
    simp [history, Vector.get, Fin.cast, run]
  | succ steps ih =>
    change ((history initial steps).push
      (step ((steps + 1) % 2) ((history initial steps).get (Fin.last steps))))[i.val] = _
    by_cases hi : i.val < steps + 1
    · rw [Vector.getElem_push_lt hi]
      exact ih ⟨i.val, hi⟩
    · have he : i.val = steps + 1 := by omega
      simp only [he, Vector.getElem_push_eq]
      rw [ih]
      rfl

/-- Compute each swap bit by arithmetic and two saved-key reads. -/
def arraySelection {q : ℕ} (parity : ℕ) (keys : Keys q) : RowLayer.Selection q (parity + 1) where
  active col row := decide (col + 1 < q ∧ (col + 1) % 2 = parity % 2 ∧ row < q ∧
    word keys row (col + 1) < word keys row col)
  valid col row h := by
    have hh := of_decide_eq_true h
    exact ⟨hh.1, hh.2.2.1, by omega⟩

theorem selection_ext {q parity : ℕ} {a b : RowLayer.Selection q parity}
    (h : a.active = b.active) : a = b := by
  cases a
  cases b
  cases h
  rfl

theorem arraySelection_eq {q : ℕ} (parity : ℕ) (keys : Keys q) :
    arraySelection parity keys = selection q parity (word keys) := by
  apply selection_ext
  funext col row
  simp [arraySelection, selection, mem_layerCenters, and_assoc]

/-- All geometric layers are stored after a single forward history execution. -/
def layers {q : ℕ} (initial : Keys q) (steps : ℕ) : Vector (CubicLayer q) steps :=
  let saved := history initial steps
  Vector.ofFn (fun i => rowLayer (arraySelection ((i.val + 1) % 2)
    (saved.get ⟨i.val, by omega⟩)))

theorem layers_get {q : ℕ} (initial : Keys q) (steps : ℕ) (i : Fin steps) :
    (layers initial steps).get i = rowSchedule q (word initial) i.val := by
  simp only [layers, get_ofFn, history_get, arraySelection_eq]
  have hw : word (run initial i.val) = keyState q (word initial) i.val := by
    funext row col
    exact run_word initial i.val row col
  rw [hw]
  rfl

def idleLayer (q : ℕ) : CubicLayer q := rowLayer
  (show RowLayer.Selection q 0 from ⟨fun _ _ => false, by intros; contradiction⟩)

/-- A total schedule backed by the one stored layer vector. -/
def storedSchedule {q : ℕ} (initial : Keys q) (steps : ℕ) : ℕ → CubicLayer q :=
  let saved := layers initial steps
  fun t => if ht : t < steps then saved.get ⟨t, ht⟩ else idleLayer q

theorem storedSchedule_at {q : ℕ} (initial : Keys q) (steps t : ℕ) (ht : t < steps) :
    storedSchedule initial steps t = rowSchedule q (word initial) t := by
  simp only [storedSchedule, ht, ↓reduceDIte, layers_get]

/-- Initial target keys are themselves materialized, with one target lookup per port. -/
def targetArray {q : ℕ} (target : Equiv.Perm (Port q)) : Keys q :=
  Vector.ofFn (fun i => (target (finProdFinEquiv.symm i)).1.val)

theorem targetArray_word {q : ℕ} (target : Equiv.Perm (Port q)) :
    word (targetArray target) = targetKeys target := by
  funext row col
  simp only [word, targetKeys]
  split_ifs <;> try rfl
  simp only [keyAt, targetArray, get_ofFn, Equiv.symm_apply_apply]

/-- The stored row schedule has exactly the proved sorting endpoint. -/
theorem storedSchedule_routes_target {q : ℕ} (target : Equiv.Perm (Port q))
    (hrow : ∀ p, (target p).2 = p.2) :
    placement (storedSchedule (targetArray target) (2 * q)) (2 * q) = target := by
  rw [placement_congr _ (rowSchedule q (word (targetArray target))) (2 * q)
    (fun t ht => storedSchedule_at _ _ _ ht), targetArray_word]
  exact rowSchedule_routes_target target hrow

/-- The same cached key history supplies actual transposed column layers. -/
def columnLayers {q : ℕ} (initial : Keys q) (steps : ℕ) : Vector (CubicLayer q) steps :=
  let saved := history initial steps
  Vector.ofFn (fun i => columnLayer (arraySelection ((i.val + 1) % 2)
    (saved.get ⟨i.val, by omega⟩)))

def storedColumnSchedule {q : ℕ} (target : Equiv.Perm (Port q)) : ℕ → CubicLayer q :=
  let saved := columnLayers (targetArray (transposedTarget target)) (2 * q)
  fun t => if ht : t < 2 * q then saved.get ⟨t, ht⟩ else idleLayer q

theorem storedColumnSchedule_at {q : ℕ} (target : Equiv.Perm (Port q))
    (t : ℕ) (ht : t < 2 * q) : storedColumnSchedule target t = columnSchedule target t := by
  simp only [storedColumnSchedule, ht, ↓reduceDIte, columnLayers, get_ofFn,
    history_get, arraySelection_eq]
  have hw : word (run (targetArray (transposedTarget target)) t) =
      keyState q (targetKeys (transposedTarget target)) t := by
    funext row col
    rw [run_word, targetArray_word]
  rw [hw]
  rfl

/-- The full executable schedule shares all phase permutations and all three
stored sorting histories. No geometry query reruns a sorting recurrence. -/
def fullSchedule {q : ℕ} {target : Equiv.Perm (Port q)}
    (colors : RowColoring target) : ℕ → CubicLayer q :=
  let phases := PhaseArrays.prepare colors
  let first := storedSchedule (targetArray phases.first) (2 * q)
  let middle := storedColumnSchedule phases.column
  let last := storedSchedule (targetArray phases.finalRow) (2 * q)
  appendSchedule first (appendSchedule middle last (2 * q)) (2 * q)

/-- Every emitted layer equals the corresponding layer in the proved cubic
construction, including its actual paths, lengths, and endpoint permutation. -/
theorem fullSchedule_eq {q : ℕ} {target : Equiv.Perm (Port q)}
    (colors : RowColoring target) (t : ℕ) (ht : t < 6 * q) :
    fullSchedule colors t = permutationSchedule colors t := by
  simp only [fullSchedule, permutationSchedule, appendSchedule]
  by_cases hfirst : t < 2 * q
  · simp only [hfirst, ↓reduceIte]
    rw [storedSchedule_at _ _ _ hfirst, targetArray_word, PhaseArrays.prepare_first]
  · simp only [hfirst, ↓reduceIte]
    by_cases hmiddle : t - 2 * q < 2 * q
    · simp only [hmiddle, ↓reduceIte]
      rw [storedColumnSchedule_at _ _ hmiddle, PhaseArrays.prepare_column]
    · simp only [hmiddle, ↓reduceIte]
      rw [storedSchedule_at _ _ _ (by omega), targetArray_word, PhaseArrays.prepare_finalRow]

/-- Complete executable row-column-row routing for any proper coloring. -/
theorem fullSchedule_routes_target {q : ℕ} {target : Equiv.Perm (Port q)}
    (colors : RowColoring target) : placement (fullSchedule colors) (6 * q) = target := by
  rw [placement_congr _ (permutationSchedule colors) (6 * q)
    (fun t ht => fullSchedule_eq colors t ht)]
  exact permutationSchedule_routes_target colors

end Maxwell.Logical.Routing.SortArrays
