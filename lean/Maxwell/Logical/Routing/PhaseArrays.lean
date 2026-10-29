import Maxwell.Logical.Routing
import Maxwell.Logical.Routing.DummyFill

/-! Stored forward and inverse arrays for the three routing phases.  Inverse
arrays are obtained by one scatter over the forward table; no search or chosen
inverse is evaluated.  All materializations use q² port indices. -/

namespace Maxwell.Logical.Routing.PhaseArrays

open DummyFill

/-- Populate the inverse array by reading each forward entry once and writing
its original index at that entry's address. -/
def inverseArray {n : ℕ} (forward : Vector (Fin n) n) : Vector (Fin n) n :=
  scatter ((List.finRange n).map (fun i => (forward.get i, i)))

theorem inverseArray_apply {n : ℕ} (forward : Vector (Fin n) n)
    (hf : Function.Injective forward.get) (i : Fin n) :
    (inverseArray forward).get (forward.get i) = i := by
  have hn : (((List.finRange n).map (fun i => (forward.get i, i))).map Prod.fst).Nodup := by
    simpa only [List.map_map, Function.comp_def] using
      (List.nodup_finRange n).map hf
  exact scatter_mem _ hn (forward.get i, i) (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)

/-- Materialize an injective finite map and its inverse in linear many reads
and writes.  Fin 0 is supported by the same empty-array construction. -/
def indexedPermutation {n : ℕ} (f : Fin n → Fin n) (hf : Function.Injective f) :
    Equiv.Perm (Fin n) :=
  let forward := Vector.ofFn f
  let backward := inverseArray forward
  have hforward : ∀ i, forward.get i = f i := by
    intro i
    simp [forward, Vector.get, Fin.cast]
  have hinjective : Function.Injective forward.get := by
    intro a b hab
    apply hf
    rw [← hforward a, ← hforward b]
    exact hab
  { toFun := forward.get
    invFun := backward.get
    left_inv := inverseArray_apply forward hinjective
    right_inv := by
      intro i
      obtain ⟨j, rfl⟩ := Finite.surjective_of_injective hinjective i
      rw [inverseArray_apply forward hinjective] }

@[simp] theorem indexedPermutation_apply {n : ℕ} (f : Fin n → Fin n)
    (hf : Function.Injective f) (i : Fin n) : indexedPermutation f hf i = f i := by
  simp [indexedPermutation, Vector.get, Fin.cast]

/-- Explicit mixed-radix coordinates, computable even for an empty grid. -/
def portIndex (q : ℕ) : Port q ≃ Fin (q * q) := finProdFinEquiv

/-- Conjugate through explicit port indices, materialize both directions, and
return to column/row coordinates. -/
def portPermutation {q : ℕ} (f : Port q → Port q) (hf : Function.Injective f) :
    Equiv.Perm (Port q) :=
  let index := portIndex q
  let indexed := fun i => index (f (index.symm i))
  let saved := indexedPermutation indexed (index.injective.comp (hf.comp index.symm.injective))
  index.trans (saved.trans index.symm)

@[simp] theorem portPermutation_apply {q : ℕ} (f : Port q → Port q)
    (hf : Function.Injective f) (p : Port q) : portPermutation f hf p = f p := by
  simp [portPermutation]

def first {q : ℕ} {target : Equiv.Perm (Port q)} (colors : RowColoring target) :
    Equiv.Perm (Port q) :=
  portPermutation (firstPlacement colors) (firstPlacement_injective colors)

def second {q : ℕ} {target : Equiv.Perm (Port q)} (colors : RowColoring target) :
    Equiv.Perm (Port q) :=
  portPermutation (secondPlacement colors) (secondPlacement_injective colors)

theorem first_eq {q : ℕ} {target : Equiv.Perm (Port q)} (colors : RowColoring target) :
    first colors = firstPermutation colors := by
  apply Equiv.ext
  intro p
  exact portPermutation_apply _ _ p

theorem second_eq {q : ℕ} {target : Equiv.Perm (Port q)} (colors : RowColoring target) :
    second colors = secondPermutation colors := by
  apply Equiv.ext
  intro p
  exact portPermutation_apply _ _ p

/-- Four stored permutations, sharing the first and second placement arrays
while constructing the middle and final phase arrays. -/
structure Prepared (q : ℕ) where
  first : Equiv.Perm (Port q)
  second : Equiv.Perm (Port q)
  column : Equiv.Perm (Port q)
  finalRow : Equiv.Perm (Port q)

def prepare {q : ℕ} {target : Equiv.Perm (Port q)} (colors : RowColoring target) : Prepared q :=
  let firstSaved := first colors
  let secondSaved := second colors
  let middle := firstSaved.symm.trans secondSaved
  let last := secondSaved.symm.trans target
  ⟨firstSaved, secondSaved, portPermutation middle middle.injective,
    portPermutation last last.injective⟩

theorem prepare_first {q : ℕ} {target : Equiv.Perm (Port q)} (colors : RowColoring target) :
    (prepare colors).first = firstPermutation colors := first_eq colors

theorem prepare_second {q : ℕ} {target : Equiv.Perm (Port q)} (colors : RowColoring target) :
    (prepare colors).second = secondPermutation colors := second_eq colors

theorem prepare_column {q : ℕ} {target : Equiv.Perm (Port q)} (colors : RowColoring target) :
    (prepare colors).column = columnPhase colors := by
  apply Equiv.ext
  intro p
  simp only [prepare, portPermutation_apply, first_eq, second_eq, columnPhase]

theorem prepare_finalRow {q : ℕ} {target : Equiv.Perm (Port q)} (colors : RowColoring target) :
    (prepare colors).finalRow = finalRowPhase colors := by
  apply Equiv.ext
  intro p
  simp only [prepare, portPermutation_apply, second_eq, finalRowPhase]

/-- The executable phase arrays retain the exact routing semantics. -/
theorem prepare_routes {q : ℕ} {target : Equiv.Perm (Port q)}
    (colors : RowColoring target) (p : Port q) :
    (prepare colors).finalRow ((prepare colors).column ((prepare colors).first p)) = target p := by
  rw [prepare_first, prepare_column, prepare_finalRow]
  exact three_phase_routing colors p

end Maxwell.Logical.Routing.PhaseArrays
