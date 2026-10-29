import Maxwell.Logical.Routing.SortArrays

/-! Cached token positions for geometric output.  Each layer updates one saved
position array.  Geometry reads the stored position at its layer, avoiding a
recursive replay of all earlier permutations for every emitted lattice point. -/

namespace Maxwell.Logical.Routing.PlacementArrays

open Maxwell.Logical.Routing.Schedule

abbrev Positions (q : ℕ) := Vector (Port q) (q * q)

def positionAt {q : ℕ} (positions : Positions q) (token : Port q) : Port q :=
  positions.get (finProdFinEquiv token)

def initial (q : ℕ) : Positions q := Vector.ofFn finProdFinEquiv.symm

@[simp] theorem initial_at {q : ℕ} (token : Port q) : positionAt (initial q) token = token := by
  simp [positionAt, initial, SortArrays.get_ofFn]

/-- One array pass: each token reads its saved position and writes its next one. -/
def advance {q : ℕ} (layer : CubicLayer q) (saved : Positions q) : Positions q :=
  saved.map layer.next

@[simp] theorem advance_at {q : ℕ} (layer : CubicLayer q) (saved : Positions q) (token : Port q) :
    positionAt (advance layer saved) token = layer.next (positionAt saved token) := by
  simp [positionAt, advance, Vector.get, Fin.cast]

def run {q : ℕ} (schedule : ℕ → CubicLayer q) : ℕ → Positions q
  | 0 => initial q
  | level + 1 => let saved := run schedule level; advance (schedule level) saved

theorem run_at {q : ℕ} (schedule : ℕ → CubicLayer q) (level : ℕ) (token : Port q) :
    positionAt (run schedule level) token = placement schedule level token := by
  induction level with
  | zero => exact initial_at token
  | succ level ih => simp only [run, advance_at, ih, placement, Equiv.trans_apply]

/-- Build and retain the complete history once, including the initial positions. -/
def history {q : ℕ} (schedule : ℕ → CubicLayer q) : (layers : ℕ) → Vector (Positions q) (layers + 1)
  | 0 => Vector.replicate 1 (initial q)
  | level + 1 =>
      let saved := history schedule level
      saved.push (advance (schedule level) (saved.get (Fin.last level)))

theorem history_get {q : ℕ} (schedule : ℕ → CubicLayer q) (layers : ℕ) (level : Fin (layers + 1)) :
    (history schedule layers).get level = run schedule level.val := by
  induction layers with
  | zero => simp [history, Vector.get, Fin.cast, run]
  | succ layers ih =>
    change ((history schedule layers).push
      (advance (schedule layers) ((history schedule layers).get (Fin.last layers))))[level.val] = _
    by_cases hl : level.val < layers + 1
    · rw [Vector.getElem_push_lt hl]
      exact ih ⟨level.val, hl⟩
    · have he : level.val = layers + 1 := by omega
      simp only [he, Vector.getElem_push_eq]
      rw [ih]
      rfl

theorem history_at {q : ℕ} (schedule : ℕ → CubicLayer q) (layers : ℕ)
    (level : Fin (layers + 1)) (token : Port q) :
    positionAt ((history schedule layers).get level) token = placement schedule level.val token := by
  rw [history_get, run_at]

/-- Read the cached input position for one slab and emit its translated point. -/
def emittedPoint {q layers : ℕ} (schedule : ℕ → CubicLayer q)
    (saved : Vector (Positions q) (layers + 1)) (level : Fin layers) (token : Port q) (step : ℕ) : Point :=
  let position := positionAt (saved.get level.castSucc) token
  translate (0, 0, 16 * (level.val : ℤ)) ((schedule level.val).point position step)

def emittedLength {q layers : ℕ} (schedule : ℕ → CubicLayer q)
    (saved : Vector (Positions q) (layers + 1)) (level : Fin layers) (token : Port q) : ℕ :=
  (schedule level.val).length (positionAt (saved.get level.castSucc) token)

theorem emittedPoint_eq {q : ℕ} (schedule : ℕ → CubicLayer q) (layers : ℕ)
    (level : Fin layers) (token : Port q) (step : ℕ) :
    emittedPoint schedule (history schedule layers) level token step =
      (routes schedule layers).point level token step := by
  simp only [emittedPoint, history_at, Fin.val_castSucc, routes]

theorem emittedLength_eq {q : ℕ} (schedule : ℕ → CubicLayer q) (layers : ℕ)
    (level : Fin layers) (token : Port q) :
    emittedLength schedule (history schedule layers) level token =
      (routes schedule layers).length level token := by
  simp only [emittedLength, history_at, Fin.val_castSucc, routes]

theorem emittedLength_le {q layers : ℕ} (schedule : ℕ → CubicLayer q)
    (saved : Vector (Positions q) (layers + 1)) (level : Fin layers) (token : Port q) :
    emittedLength schedule saved level token ≤ 40 := (schedule level.val).length_le _

/-- Materialize one slab segment, storing its start and internal points.  Its
final point belongs to the next slab, or to the separate final-port output. -/
def segment {q layers : ℕ} (schedule : ℕ → CubicLayer q)
    (saved : Vector (Positions q) (layers + 1)) (level : Fin layers) (token : Port q) : List Point :=
  let position := positionAt (saved.get level.castSucc) token
  let layer := schedule level.val
  (List.range (layer.length position)).map
    (fun step => translate (0, 0, 16 * (level.val : ℤ)) (layer.point position step))

theorem segment_length {q layers : ℕ} (schedule : ℕ → CubicLayer q)
    (saved : Vector (Positions q) (layers + 1)) (level : Fin layers) (token : Port q) :
    (segment schedule saved level token).length = emittedLength schedule saved level token := by
  simp [segment, emittedLength]

theorem segment_eq {q : ℕ} (schedule : ℕ → CubicLayer q) (layers : ℕ)
    (level : Fin layers) (token : Port q) :
    segment schedule (history schedule layers) level token =
      (List.range ((routes schedule layers).length level token)).map
        ((routes schedule layers).point level token) := by
  simp only [segment, history_at, Fin.val_castSucc, routes]

theorem emittedPoint_unit_step {q : ℕ} (schedule : ℕ → CubicLayer q) (layers : ℕ)
    (level : Fin layers) (token : Port q) (step : ℕ)
    (ht : step < emittedLength schedule (history schedule layers) level token) :
    UnitAdjacent (emittedPoint schedule (history schedule layers) level token step)
      (emittedPoint schedule (history schedule layers) level token (step + 1)) := by
  rw [emittedPoint_eq, emittedPoint_eq]
  apply (routes schedule layers).step
  rwa [emittedLength_eq] at ht

/-- Concrete output loop, sharing the single placement history.  Each token
emits at most forty points per layer. -/
def emitInteriors {q : ℕ} (schedule : ℕ → CubicLayer q) (layers : ℕ) : List Point :=
  let saved := history schedule layers
  (List.finRange layers).flatMap (fun level =>
    (List.finRange (q * q)).flatMap (fun token =>
      segment schedule saved level (finProdFinEquiv.symm token)))

theorem flatMap_length_le {α β : Type*} (xs : List α) (f : α → List β) (bound : ℕ)
    (hf : ∀ x ∈ xs, (f x).length ≤ bound) : (xs.flatMap f).length ≤ xs.length * bound := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have hx := hf x (by simp)
    have ht := ih (fun y hy => hf y (by simp [hy]))
    nlinarith

theorem emitInteriors_length_le {q : ℕ} (schedule : ℕ → CubicLayer q) (layers : ℕ) :
    (emitInteriors schedule layers).length ≤ 40 * layers * (q * q) := by
  have hlevel (level : Fin layers) :
      ((List.finRange (q * q)).flatMap (fun token =>
        segment schedule (history schedule layers) level (finProdFinEquiv.symm token))).length ≤
          (q * q) * 40 := by
    simpa only [List.length_finRange] using flatMap_length_le (List.finRange (q * q))
      (fun token => segment schedule (history schedule layers) level (finProdFinEquiv.symm token)) 40
      (fun token _ => by rw [segment_length]; exact emittedLength_le _ _ _ _)
  have h := flatMap_length_le (List.finRange layers)
    (fun level => (List.finRange (q * q)).flatMap (fun token =>
      segment schedule (history schedule layers) level (finProdFinEquiv.symm token)))
    ((q * q) * 40) (fun level _ => hlevel level)
  simpa only [emitInteriors, List.length_finRange, Nat.mul_assoc, Nat.mul_left_comm,
    Nat.mul_comm] using h

end Maxwell.Logical.Routing.PlacementArrays
