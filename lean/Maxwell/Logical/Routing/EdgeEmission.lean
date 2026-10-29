import Maxwell.Logical.Routing.Executable
import Maxwell.Logical.Routing.Subdivision

/-! Active-edge lattice emission from one shared routing schedule and one
saved placement history. Seams are stored once and no output point searches
chronological prefix lengths or replays preceding permutation layers. -/

namespace Maxwell.Logical.Routing.EdgeEmission

open Maxwell.Logical.Routing.Schedule
open Maxwell.Logical.Routing.SortSchedule
open Maxwell.Logical.Routing.Gluing
open Maxwell.Logical.Routing.Walk
open Maxwell.Logical.Routing.EdgeWalk
open Maxwell.Logical.Routing.Terminals

/-- Walk samples excluding the final endpoint; this prefix omits each seam. -/
def samplesPrefix {a b : Point} (walk : LatticeWalk a b) : List Point :=
  (List.range walk.length).map walk.point

def points {a b : Point} (walk : LatticeWalk a b) : List Point :=
  (List.range (walk.length + 1)).map walk.point

@[simp] theorem prefix_length {a b : Point} (walk : LatticeWalk a b) :
    (samplesPrefix walk).length = walk.length := by simp [samplesPrefix]

@[simp] theorem points_length {a b : Point} (walk : LatticeWalk a b) :
    (points walk).length = walk.length + 1 := by simp [points]

theorem points_eq_prefix {a b : Point} (walk : LatticeWalk a b) :
    points walk = samplesPrefix walk ++ [b] := by
  simp only [points, List.range_succ, List.map_append, List.map_singleton, walk.last, samplesPrefix]

theorem prefix_append {a b c : Point} (left : LatticeWalk a b) (right : LatticeWalk b c) :
    samplesPrefix (append left right) = samplesPrefix left ++ samplesPrefix right := by
  simp only [samplesPrefix, append_length, List.range_add, List.map_append, List.map_map]
  congr 1
  · apply List.map_congr_left
    intro t ht
    have hh := List.mem_range.mp ht
    simp only [append, show t ≤ left.length by omega, ↓reduceIte]
  · apply List.map_congr_left
    intro t _
    by_cases hz : t = 0
    · subst t
      simp only [Function.comp_apply, Nat.add_zero, append, le_refl, ↓reduceIte,
        left.last, right.first]
    · simp only [Function.comp_apply, append, show ¬left.length + t ≤ left.length by omega,
        ↓reduceIte, Nat.add_sub_cancel_left]

theorem points_append {a b c : Point} (left : LatticeWalk a b) (right : LatticeWalk b c) :
    points (append left right) = samplesPrefix left ++ points right := by
  rw [points_eq_prefix, prefix_append, points_eq_prefix, List.append_assoc]

theorem points_reverse {a b : Point} (walk : LatticeWalk a b) :
    points (Walk.reverse walk) = (points walk).reverse := by
  apply List.ext_getElem
  · simp [points, Walk.reverse]
  · intro t ht hu
    simp only [points, Walk.reverse, List.getElem_map, List.getElem_range,
      List.getElem_reverse, List.length_map, List.length_range]
    congr 1

/-- Flatten local slab prefixes; this lemma is proof-only and permits the
executable implementation to look up each slab directly in stored arrays. -/
theorem network_prefix {q : ℕ} (schedule : ℕ → CubicLayer q) (token : Port q)
    (segments : ℕ → List Point) (layers : ℕ)
    (hs : ∀ level < layers, segments level = samplesPrefix (slabWalk schedule level token)) :
    (List.range layers).flatMap segments = samplesPrefix (networkWalk schedule layers token) := by
  induction layers with
  | zero => simp [networkWalk, Walk.singleton, samplesPrefix]
  | succ layers ih =>
    rw [List.range_succ, List.flatMap_append]
    simp only [List.flatMap_singleton, networkWalk, prefix_append]
    rw [ih (fun level hl => hs level (by omega)), hs layers (by omega)]

/-- Saved data shared across every active edge. -/
structure Prepared (q layers : ℕ) where
  schedule : ℕ → CubicLayer q
  positions : Vector (PlacementArrays.Positions q) (layers + 1)

/-- Construct the schedule and placement history once, before the edge loop. -/
def prepare {V E : Type*} {half : ℕ} (data : Data V E half) :
    Prepared (2 * half) (6 * (2 * half)) :=
  let schedule := SortArrays.fullSchedule data.colors
  ⟨schedule, PlacementArrays.history schedule (6 * (2 * half))⟩

/-- Directly emit one saved slab, with at most forty local samples. -/
def savedSegment {q layers : ℕ} (saved : Prepared q layers) (token : Port q) (level : ℕ) : List Point :=
  if hl : level < layers then PlacementArrays.segment saved.schedule saved.positions ⟨level, hl⟩ token
  else []

/-- Traverse the layer array in order; each point reads its local slab only. -/
def networkPrefix {q layers : ℕ} (saved : Prepared q layers) (token : Port q) : List Point :=
  (List.range layers).flatMap (savedSegment saved token)

theorem savedSegment_eq {V E : Type*} {half : ℕ} (data : Data V E half) (i : Incidence E)
    (level : ℕ) (hl : level < 6 * (2 * half)) :
    savedSegment (prepare data) (token data i) level =
      samplesPrefix (slabWalk (permutationSchedule data.colors) level (token data i)) := by
  simp only [savedSegment, hl, ↓reduceDIte, prepare, PlacementArrays.segment,
    PlacementArrays.history_at, Fin.val_castSucc]
  rw [SortArrays.fullSchedule_eq data.colors level hl,
    Executable.full_placement data.colors level (by omega)]
  rfl

theorem networkPrefix_eq {V E : Type*} {half : ℕ} (data : Data V E half) (i : Incidence E) :
    networkPrefix (prepare data) (token data i) = samplesPrefix (routedWalk data i) := by
  exact network_prefix (permutationSchedule data.colors) (token data i)
    (savedSegment (prepare data) (token data i)) _ (savedSegment_eq data i)

/-- Literal bottom-arm arithmetic, excluding its final network port. -/
def bottomPrefix {V E : Type*} {half : ℕ} (data : Data V E half) (i : Incidence E) : List Point :=
  let vertex := data.endpoint i.1 i.2
  let side := data.part vertex
  let arm := data.arm i.1 i.2
  let offset := tileTranslation data vertex
  (List.range (correctedArmLength side arm)).map
    (fun t => translate offset (correctedArmPoint side arm t))

@[simp] theorem bottomPrefix_eq {V E : Type*} {half : ℕ} (data : Data V E half) (i : Incidence E) :
    bottomPrefix data i = samplesPrefix (bottomWalk data i) := rfl

/-- Literal forty-eight-edge top connector, excluding its final joint. -/
def topPrefix {V E : Type*} {half : ℕ} (data : Data V E half) (e : E) : List Point :=
  let pair := data.pair e
  let offset : Point := (32 * pair.1.val, 16 * pair.2.val, 96 * (2 * half))
  (List.range 48).map (fun t => translate offset (topPoint t))

@[simp] theorem topPrefix_eq {V E : Type*} {half : ℕ} (data : Data V E half) (e : E) :
    topPrefix data e = samplesPrefix (topWalk data e) := rfl

/-- Materialize one complete incidence leg from its bottom and cached slabs. -/
def legPoints {V E : Type*} {half : ℕ} (data : Data V E half)
    (saved : Prepared (2 * half) (6 * (2 * half))) (i : Incidence E) : List Point :=
  bottomPrefix data i ++ networkPrefix saved (token data i) ++
    [gridPort (pairPort (data.pair i.1) i.2) (96 * (2 * half))]

theorem legPoints_eq {V E : Type*} {half : ℕ} (data : Data V E half) (i : Incidence E) :
    legPoints data (prepare data) i = points (leg data i) := by
  rw [legPoints, bottomPrefix_eq, networkPrefix_eq, points_eq_prefix]
  rw [leg, prefix_append]

/-- Emit one active edge. The left leg and top connector omit their final
joints; the materialized right leg is reversed once, in linear time. -/
def edge {V E : Type*} {half : ℕ} (data : Data V E half)
    (saved : Prepared (2 * half) (6 * (2 * half))) (e : E) : List Point :=
  bottomPrefix data (e, false) ++ networkPrefix saved (token data (e, false)) ++
    topPrefix data e ++ (legPoints data saved (e, true)).reverse

/-- Exact chronological equality, including both endpoints and every seam. -/
theorem edge_eq {V E : Type*} {half : ℕ} (data : Data V E half) (e : E) :
    edge data (prepare data) e = points (edgeWalk data e) := by
  rw [edge, bottomPrefix_eq, networkPrefix_eq, topPrefix_eq, legPoints_eq,
    edgeWalk, points_append, prefix_append, points_reverse]
  simp only [leg, prefix_append, List.append_assoc]

theorem edge_length {V E : Type*} {half : ℕ} (data : Data V E half) (e : E) :
    (edge data (prepare data) e).length = (edgeWalk data e).length + 1 := by
  rw [edge_eq, points_length]

theorem edge_sample {V E : Type*} {half : ℕ} (data : Data V E half) (e : E)
    (t : ℕ) (ht : t < (edge data (prepare data) e).length) :
    (edge data (prepare data) e)[t] = (edgeWalk data e).point t := by
  simp only [edge_eq, points, List.getElem_map, List.getElem_range]

/-- The emitted chronological sample is the actual selected logical
subdivision vertex, including its shared original endpoints. -/
theorem edge_sample_embedding {V E : Type*} {half : ℕ} (data : Data V E half) (e : E)
    (t : Fin ((edgeWalk data e).length + 1)) :
    (edge data (prepare data) e)[t.val]'(by rw [edge_length]; exact t.isLt) =
      Subdivision.embedding data (Subdivision.edgeVertex data e t) := by
  rw [edge_sample, Subdivision.embedding_edgeVertex]

theorem edge_length_le {V E : Type*} {half : ℕ} (data : Data V E half) (e : E) :
    (edge data (prepare data) e).length ≤ 1024 * (2 * half) + 1 := by
  rw [edge_length]
  have hh := edgeWalk_length_bound data e
  omega

/-- Emit all and only active graph edges, sharing the single prepared network. -/
def all {vertices edges half : ℕ} (data : Data (Fin vertices) (Fin edges) half) : List Point :=
  let saved := prepare data
  (List.finRange edges).flatMap (edge data saved)

theorem all_length_le {vertices edges half : ℕ} (data : Data (Fin vertices) (Fin edges) half) :
    (all data).length ≤ edges * (1024 * (2 * half) + 1) := by
  simpa only [all, List.length_finRange] using
    PlacementArrays.flatMap_length_le (List.finRange edges) (edge data (prepare data))
      (1024 * (2 * half) + 1) (fun e _ => edge_length_le data e)

end Maxwell.Logical.Routing.EdgeEmission
