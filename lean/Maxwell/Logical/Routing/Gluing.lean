import Maxwell.Logical.Routing.Terminals
import Mathlib.Logic.Equiv.Fintype

/-! Global vertex gluing of the concrete cubic routing construction.
Only finite graph incidence labels and the proper row coloring are inputs. -/

namespace Maxwell.Logical.Routing.Gluing

open Maxwell.Logical.Routing
open Maxwell.Logical.Routing.Schedule
open Maxwell.Logical.Routing.SortSchedule
open Maxwell.Logical.Routing.Terminals

/-- The three incidence ports in the 2-by-2 array tile of a graph vertex. -/
def tilePort {half : ℕ} (tile : Port half) (arm : Fin 3) : Port (2 * half) :=
  (⟨2 * tile.1.val + if arm = 1 then 1 else 0, by have := tile.1.isLt; split_ifs <;> omega⟩,
   ⟨2 * tile.2.val + if arm = 2 then 1 else 0, by have := tile.2.isLt; split_ifs <;> omega⟩)

theorem tilePort_injective (half : ℕ) :
    Function.Injective (fun entry : Port half × Fin 3 => tilePort entry.1 entry.2) := by
  rintro ⟨a, i⟩ ⟨b, j⟩ he
  have hx := congrArg (fun p : Port (2 * half) => p.1.val) he
  have hy := congrArg (fun p : Port (2 * half) => p.2.val) he
  change (a, i) = (b, j)
  fin_cases i <;> fin_cases j <;> norm_num [tilePort] at hx hy
  all_goals first
    | omega
    | apply Prod.ext
      · apply Prod.ext <;> apply Fin.ext <;> dsimp only <;> omega
      · rfl

/-- The adjacent paired ports assigned to one original graph edge. -/
def pairPort {half : ℕ} (pair : Fin half × Fin (2 * half)) (side : Bool) : Port (2 * half) :=
  (⟨2 * pair.1.val + if side then 1 else 0, by have := pair.1.isLt; split_ifs <;> omega⟩, pair.2)

/-- Local finite graph data: vertices occupy distinct tiles, incidences use
at most three distinct arms, and the target pairs the two ends of each edge. -/
structure Data (Vertex Edge : Type*) (half : ℕ) where
  tile : Vertex → Port half
  tile_injective : Function.Injective tile
  part : Vertex → Bool
  endpoint : Edge → Bool → Vertex
  endpoint_part : ∀ e side, part (endpoint e side) = side
  arm : Edge → Bool → Fin 3
  incidence_injective : Function.Injective (fun p : Edge × Bool => (endpoint p.1 p.2, arm p.1 p.2))
  pair : Edge → Fin half × Fin (2 * half)
  pair_injective : Function.Injective pair
  target : Equiv.Perm (Port (2 * half))
  target_incidence : ∀ e side,
    target (tilePort (tile (endpoint e side)) (arm e side)) = pairPort (pair e) side
  colors : RowColoring target

abbrev Incidence (Edge : Type*) := Edge × Bool

def token {V E : Type*} {half : ℕ} (data : Data V E half) (i : Incidence E) : Port (2 * half) :=
  tilePort (data.tile (data.endpoint i.1 i.2)) (data.arm i.1 i.2)

theorem token_injective {V E : Type*} {half : ℕ} (data : Data V E half) :
    Function.Injective (token data) := by
  intro a b he
  have hh := @tilePort_injective half
    (data.tile (data.endpoint a.1 a.2), data.arm a.1 a.2)
    (data.tile (data.endpoint b.1 b.2), data.arm b.1 b.2) he
  apply data.incidence_injective
  apply Prod.ext
  · exact data.tile_injective (congrArg Prod.fst hh)
  · exact congrArg (fun x : Port half × Fin 3 => x.2) hh

def tileTranslation {V E : Type*} {half : ℕ} (data : Data V E half) (v : V) : Point :=
  (32 * (data.tile v).1.val, 32 * (data.tile v).2.val, 0)

def vertexPoint {V E : Type*} {half : ℕ} (data : Data V E half) (v : V) : Point :=
  translate (tileTranslation data v) (0, 0, -(bottomDepth (data.part v) : ℤ))

def bottomSample {V E : Type*} {half : ℕ} (data : Data V E half) (v : V) (arm : Fin 3)
    (t : Fin (correctedArmLength (data.part v) arm + 1)) : Point :=
  translate (tileTranslation data v) (correctedArm (data.part v) arm t)

/-- All intersections of placed bottom arms are the prescribed common
original graph vertex, or the same sample of the same arm. -/
theorem bottomSample_intersection {V E : Type*} {half : ℕ} (data : Data V E half)
    (v w : V) (a b : Fin 3) (i : Fin (correctedArmLength (data.part v) a + 1))
    (j : Fin (correctedArmLength (data.part w) b + 1))
    (he : bottomSample data v a i = bottomSample data w b j) :
    v = w ∧ ((a = b ∧ i.val = j.val) ∨ (i.val = 0 ∧ j.val = 0)) := by
  have hvw : v = w := by
    by_contra hn
    have ht : data.tile v ≠ data.tile w := fun h => hn (data.tile_injective h)
    have hs : ((data.tile v).1.val : ℤ) ≠ (data.tile w).1.val ∨
        ((data.tile v).2.val : ℤ) ≠ (data.tile w).2.val := by
      by_contra h
      push Not at h
      apply ht
      apply Prod.ext <;> apply Fin.ext <;> omega
    exact corrected_bottom_stars_disjoint _ _ _ _ hs _ _ a b i j he
  subst w
  refine ⟨rfl, ?_⟩
  have hp := translate_injective (tileTranslation data v) he
  by_cases hab : a = b
  · subst b
    exact Or.inl ⟨rfl, congrArg Fin.val (correctedArm_injective (data.part v) a hp)⟩
  · exact Or.inr (correctedArms_meet_only_at_start (data.part v) a b i j hab hp)

theorem vertexPoint_injective {V E : Type*} {half : ℕ} (data : Data V E half) :
    Function.Injective (vertexPoint data) := by
  intro a b he
  have hx := congrArg (fun p : Point => p.1) he
  have hy := congrArg (fun p : Point => p.2.1) he
  simp only [vertexPoint, translate, tileTranslation, add_zero] at hx hy
  apply data.tile_injective
  apply Prod.ext <;> apply Fin.ext <;> omega

/-- The actual bottom endpoint is the source port of the actual routing path. -/
theorem bottomSample_end {V E : Type*} {half : ℕ} (data : Data V E half) (v : V) (a : Fin 3) :
    bottomSample data v a (Fin.last (correctedArmLength (data.part v) a)) =
      gridPort (tilePort (data.tile v) a) 0 := by
  simp only [bottomSample, correctedArm, Fin.val_last, correctedArm_end]
  fin_cases a <;> simp [tilePort, incidencePort, translate, tileTranslation, gridPort] <;> ring_nf <;> simp

/-- Interior bottom vertices exclude the original vertex and incidence port. -/
def BottomInterior {V E : Type*} {half : ℕ} (data : Data V E half) (i : Incidence E) :=
  Fin (correctedArmLength (data.part (data.endpoint i.1 i.2)) (data.arm i.1 i.2) - 1)

def bottomInteriorPoint {V E : Type*} {half : ℕ} (data : Data V E half)
    (i : Incidence E) (t : BottomInterior data i) : Point :=
  bottomSample data (data.endpoint i.1 i.2) (data.arm i.1 i.2) ⟨t.val + 1, by have := t.isLt; omega⟩

def BottomVertex {V E : Type*} {half : ℕ} (data : Data V E half) :=
  V ⊕ (Σ i : Incidence E, BottomInterior data i)

def bottomPoint {V E : Type*} {half : ℕ} (data : Data V E half) : BottomVertex data → Point
  | .inl v => vertexPoint data v
  | .inr ⟨i, t⟩ => bottomInteriorPoint data i t

@[simp] theorem bottomSample_start {V E : Type*} {half : ℕ} (data : Data V E half) (v : V) (a : Fin 3) :
    bottomSample data v a ⟨0, by omega⟩ = vertexPoint data v := by
  simp only [bottomSample, correctedArm, correctedArm_start, vertexPoint]

theorem bottomPoint_injective {V E : Type*} {half : ℕ} (data : Data V E half) :
    Function.Injective (bottomPoint data) := by
  intro x y he
  cases x with
  | inl v =>
    cases y with
    | inl w => exact congrArg Sum.inl (vertexPoint_injective data he)
    | inr y =>
      rcases y with ⟨i, t⟩
      change vertexPoint data v = bottomInteriorPoint data i t at he
      rw [← bottomSample_start data v 0] at he
      have hh := bottomSample_intersection data v (data.endpoint i.1 i.2) 0 (data.arm i.1 i.2)
        ⟨0, by omega⟩ ⟨t.val + 1, by have := t.isLt; omega⟩ he
      rcases hh.2 with hs | hs <;> simp only at hs <;> omega
  | inr x =>
    rcases x with ⟨i, t⟩
    cases y with
    | inl v =>
      change bottomInteriorPoint data i t = vertexPoint data v at he
      rw [← bottomSample_start data v 0] at he
      have hh := bottomSample_intersection data (data.endpoint i.1 i.2) v (data.arm i.1 i.2) 0
        ⟨t.val + 1, by have := t.isLt; omega⟩ ⟨0, by omega⟩ he
      rcases hh.2 with hs | hs <;> simp only at hs <;> omega
    | inr y =>
      rcases y with ⟨j, u⟩
      have hh := bottomSample_intersection data (data.endpoint i.1 i.2) (data.endpoint j.1 j.2)
        (data.arm i.1 i.2) (data.arm j.1 j.2)
        ⟨t.val + 1, by have := t.isLt; omega⟩ ⟨u.val + 1, by have := u.isLt; omega⟩ he
      rcases hh.2 with hs | hs
      · have hij : i = j := data.incidence_injective (Prod.ext hh.1 hs.1)
        subst j
        have htu : t = u := Fin.ext (by simpa only [Nat.add_right_cancel_iff] using hs.2)
        subst u
        rfl
      · simp only at hs
        omega

theorem bottomPoint_height {V E : Type*} {half : ℕ} (data : Data V E half) (v : BottomVertex data) :
    -16 ≤ (bottomPoint data v).2.2 ∧ (bottomPoint data v).2.2 < 0 := by
  cases v with
  | inl v =>
    simp only [bottomPoint, vertexPoint, translate, tileTranslation, zero_add]
    cases data.part v <;> decide
  | inr interior =>
    rcases interior with ⟨i, t⟩
    have hb := correctedArm_bounds (data.part (data.endpoint i.1 i.2)) (data.arm i.1 i.2)
      ⟨t.val + 1, by have := t.isLt; omega⟩
    have hf := correctedArm_face (data.part (data.endpoint i.1 i.2)) (data.arm i.1 i.2)
      ⟨t.val + 1, by have := t.isLt; omega⟩
    have ht := t.isLt
    simp only [bottomPoint, bottomInteriorPoint, bottomSample, translate, tileTranslation, zero_add]
    simp only at hf
    omega

noncomputable def networkRoutes {V E : Type*} {half : ℕ} (data : Data V E half) :=
  routes (permutationSchedule data.colors) (6 * (2 * half))

def NetworkVertex {V E : Type*} {half : ℕ} (data : Data V E half) :=
  Σ i : Incidence E, Assembly.TrajectoryIndex (networkRoutes data) (token data i)

noncomputable def networkPoint {V E : Type*} {half : ℕ} (data : Data V E half) : NetworkVertex data → Point
  | ⟨i, t⟩ => Assembly.trajectoryPoint (networkRoutes data) (token data i) t

theorem networkPoint_injective {V E : Type*} {half : ℕ} (data : Data V E half) :
    Function.Injective (networkPoint data) := by
  rintro ⟨i, t⟩ ⟨j, u⟩ he
  have hh := @permutationSchedule_trajectory_injective (2 * half) data.target data.colors
    ⟨token data i, t⟩ ⟨token data j, u⟩ he
  have hij : i = j := token_injective data (congrArg Sigma.fst hh)
  subst j
  have htu : t = u := eq_of_heq (Sigma.mk.inj_iff.mp hh).2
  subst u
  rfl

theorem networkPoint_height {V E : Type*} {half : ℕ} (data : Data V E half) (v : NetworkVertex data) :
    0 ≤ (networkPoint data v).2.2 ∧ (networkPoint data v).2.2 ≤ 96 * (2 * half) :=
  (permutationSchedule_box data.colors (token data v.1) v.2).2

def TopVertex (Edge : Type*) := Edge × Fin 47

def topInteriorPoint {V E : Type*} {half : ℕ} (data : Data V E half) (v : TopVertex E) : Point :=
  placedTopBridge (data.pair v.1).1.val (data.pair v.1).2.val (96 * (2 * half))
    ⟨v.2.val + 1, by have := v.2.isLt; omega⟩

theorem topInteriorPoint_injective {V E : Type*} {half : ℕ} (data : Data V E half) :
    Function.Injective (topInteriorPoint data) := by
  rintro ⟨e, t⟩ ⟨f, u⟩ he
  have hef : e = f := by
    by_contra hn
    have hp : data.pair e ≠ data.pair f := fun h => hn (data.pair_injective h)
    have hs : ((data.pair e).1.val : ℤ) ≠ (data.pair f).1.val ∨
        ((data.pair e).2.val : ℤ) ≠ (data.pair f).2.val := by
      by_contra h
      push Not at h
      apply hp
      apply Prod.ext <;> apply Fin.ext <;> omega
    exact placedTopBridge_disjoint _ _ _ _ _ hs _ _ he
  subst f
  have hh := topBridge_injective (translate_injective _ he)
  have ht := congrArg Fin.val hh
  exact Prod.ext rfl (Fin.ext (by simpa only [Nat.add_right_cancel_iff] using ht))

theorem topInteriorPoint_height {V E : Type*} {half : ℕ} (data : Data V E half) (v : TopVertex E) :
    96 * (2 * half) < (topInteriorPoint data v).2.2 ∧
      (topInteriorPoint data v).2.2 ≤ 96 * (2 * half) + 16 := by
  have hb := topBridge_bounds ⟨v.2.val + 1, by have := v.2.isLt; omega⟩
  have hf := topBridge_faces ⟨v.2.val + 1, by have := v.2.isLt; omega⟩
  have ht := v.2.isLt
  simp only at hf
  simp only [topInteriorPoint, placedTopBridge, translate]
  omega

/-- Every original and subdivision vertex is stored exactly once. -/
def RoutedVertex {V E : Type*} {half : ℕ} (data : Data V E half) :=
  BottomVertex data ⊕ NetworkVertex data ⊕ TopVertex E

noncomputable def embedding {V E : Type*} {half : ℕ} (data : Data V E half) : RoutedVertex data → Point
  | .inl v => bottomPoint data v
  | .inr (.inl v) => networkPoint data v
  | .inr (.inr v) => topInteriorPoint data v

/-- The complete graph construction, including actual parity detours,
bottom stars, sorting network, and top pairings, is globally injective. -/
theorem embedding_injective {V E : Type*} {half : ℕ} (data : Data V E half) :
    Function.Injective (embedding data) := by
  intro a b he
  cases a with
  | inl a =>
    cases b with
    | inl b => exact congrArg Sum.inl (bottomPoint_injective data he)
    | inr b =>
      have ha := bottomPoint_height data a
      cases b with
      | inl b =>
        have hb := networkPoint_height data b
        have hz := congrArg (fun p : Point => p.2.2) he
        change (bottomPoint data a).2.2 = (networkPoint data b).2.2 at hz
        omega
      | inr b =>
        have hb := topInteriorPoint_height data b
        have hz := congrArg (fun p : Point => p.2.2) he
        change (bottomPoint data a).2.2 = (topInteriorPoint data b).2.2 at hz
        omega
  | inr a =>
    cases a with
    | inl a =>
      have ha := networkPoint_height data a
      cases b with
      | inl b =>
        have hb := bottomPoint_height data b
        have hz := congrArg (fun p : Point => p.2.2) he
        change (networkPoint data a).2.2 = (bottomPoint data b).2.2 at hz
        omega
      | inr b =>
        cases b with
        | inl b => exact congrArg (Sum.inr ∘ Sum.inl) (networkPoint_injective data he)
        | inr b =>
          have hb := topInteriorPoint_height data b
          have hz := congrArg (fun p : Point => p.2.2) he
          change (networkPoint data a).2.2 = (topInteriorPoint data b).2.2 at hz
          omega
    | inr a =>
      have ha := topInteriorPoint_height data a
      cases b with
      | inl b =>
        have hb := bottomPoint_height data b
        have hz := congrArg (fun p : Point => p.2.2) he
        change (topInteriorPoint data a).2.2 = (bottomPoint data b).2.2 at hz
        omega
      | inr b =>
        cases b with
        | inl b =>
          have hb := networkPoint_height data b
          have hz := congrArg (fun p : Point => p.2.2) he
          change (topInteriorPoint data a).2.2 = (networkPoint data b).2.2 at hz
          omega
        | inr b => exact congrArg (Sum.inr ∘ Sum.inr) (topInteriorPoint_injective data he)

theorem pairPort_injective (half : ℕ) :
    Function.Injective (fun entry : (Fin half × Fin (2 * half)) × Bool => pairPort entry.1 entry.2) := by
  rintro ⟨a, i⟩ ⟨b, j⟩ he
  have hx := congrArg (fun p : Port (2 * half) => p.1.val) he
  have hy := congrArg (fun p : Port (2 * half) => p.2.val) he
  change (a, i) = (b, j)
  cases i <;> cases j <;> simp only [pairPort, Bool.false_eq_true, ↓reduceIte] at hx hy
  all_goals first
    | omega
    | apply Prod.ext
      · apply Prod.ext <;> apply Fin.ext <;> dsimp only <;> omega
      · rfl

/-- All unused ports can be filled with dummy tokens: any injective finite
incidence placement extends to a total target permutation. -/
theorem targetPermutation_exists {E : Type*} [Finite E] {half : ℕ}
    (source : Incidence E → Port (2 * half)) (hsource : Function.Injective source)
    (pairs : E → Fin half × Fin (2 * half)) (hpairs : Function.Injective pairs) :
    ∃ target : Equiv.Perm (Port (2 * half)), ∀ i : Incidence E,
      target (source i) = pairPort (pairs i.1) i.2 := by
  apply Equiv.Perm.exists_extending_pair source _ hsource
  intro a b he
  have hh := @pairPort_injective half (pairs a.1, a.2) (pairs b.1, b.2) he
  exact Prod.ext (hpairs (congrArg Prod.fst hh)) (congrArg (fun x : (Fin half × Fin (2 * half)) × Bool => x.2) hh)

theorem bottomSample_horizontal_bounds {V E : Type*} {half : ℕ} (data : Data V E half)
    (v : V) (a : Fin 3) (t : Fin (correctedArmLength (data.part v) a + 1)) :
    InHorizontalBox (2 * half) (bottomSample data v a t) := by
  have hb := correctedArm_bounds (data.part v) a t
  have hx := (data.tile v).1.isLt
  have hy := (data.tile v).2.isLt
  simp only [InHorizontalBox, bottomSample, tileTranslation, translate]
  push_cast
  omega

theorem bottomPoint_horizontal_bounds {V E : Type*} {half : ℕ} (data : Data V E half)
    (v : BottomVertex data) : InHorizontalBox (2 * half) (bottomPoint data v) := by
  cases v with
  | inl v =>
    change InHorizontalBox (2 * half) (vertexPoint data v)
    rw [← bottomSample_start data v 0]
    exact bottomSample_horizontal_bounds data v 0 _
  | inr v => exact bottomSample_horizontal_bounds data _ _ _

theorem topInteriorPoint_horizontal_bounds {V E : Type*} {half : ℕ} (data : Data V E half)
    (v : TopVertex E) : InHorizontalBox (2 * half) (topInteriorPoint data v) := by
  have hb := topBridge_bounds ⟨v.2.val + 1, by have := v.2.isLt; omega⟩
  have hx := (data.pair v.1).1.isLt
  have hy := (data.pair v.1).2.isLt
  simp only [InHorizontalBox, topInteriorPoint, placedTopBridge, translate]
  push_cast
  omega

/-- All actual vertices, including detours and terminal connectors, lie
in the manuscript's full ambient box. -/
theorem embedding_box {V E : Type*} {half : ℕ} (data : Data V E half) (v : RoutedVertex data) :
    InHorizontalBox (2 * half) (embedding data v) ∧
      -16 ≤ (embedding data v).2.2 ∧ (embedding data v).2.2 ≤ 96 * (2 * half) + 16 := by
  cases v with
  | inl v =>
    have hb := bottomPoint_height data v
    exact ⟨bottomPoint_horizontal_bounds data v, hb.1, by change (bottomPoint data v).2.2 ≤ _; omega⟩
  | inr v =>
    cases v with
    | inl v =>
      have hb := permutationSchedule_box data.colors (token data v.1) v.2
      exact ⟨hb.1, by change -16 ≤ (networkPoint data v).2.2; have := networkPoint_height data v; omega,
        by change (networkPoint data v).2.2 ≤ _; have := networkPoint_height data v; omega⟩
    | inr v =>
      have hb := topInteriorPoint_height data v
      exact ⟨topInteriorPoint_horizontal_bounds data v, by change -16 ≤ (topInteriorPoint data v).2.2; omega, hb.2⟩

/-- Shift the proved ambient box to zero-based integer occupancy coordinates. -/
noncomputable def boxIndex {V E : Type*} {half : ℕ} (data : Data V E half) (v : RoutedVertex data) :
    Fin (boxSideXY (2 * half)) × Fin (boxSideXY (2 * half)) × Fin (boxSideZ (2 * half)) :=
  let p := embedding data v
  (⟨(p.1 + 4).toNat, by have h := embedding_box data v; unfold InHorizontalBox at h; unfold boxSideXY; dsimp only [p]; omega⟩,
   ⟨(p.2.1 + 4).toNat, by have h := embedding_box data v; unfold InHorizontalBox at h; unfold boxSideXY; dsimp only [p]; omega⟩,
   ⟨(p.2.2 + 16).toNat, by have h := embedding_box data v; unfold boxSideZ; dsimp only [p]; omega⟩)

theorem boxIndex_injective {V E : Type*} {half : ℕ} (data : Data V E half) :
    Function.Injective (boxIndex data) := by
  intro a b he
  have ha := embedding_box data a
  have hb := embedding_box data b
  have hx := congrArg (fun p => p.1.val) he
  have hy := congrArg (fun p => p.2.1.val) he
  have hz := congrArg (fun p => p.2.2.val) he
  simp only [boxIndex] at hx hy hz
  unfold InHorizontalBox at ha hb
  apply embedding_injective data
  apply Prod.ext
  · omega
  · apply Prod.ext <;> omega

noncomputable instance {V E : Type*} [Fintype V] [Fintype E] {half : ℕ} (data : Data V E half) :
    Fintype (RoutedVertex data) := by
  unfold RoutedVertex BottomVertex BottomInterior NetworkVertex Assembly.TrajectoryIndex TopVertex Incidence
  infer_instance

/-- Occupied vertices are bounded by the entire integer box, counting every
unused site in the same box formula used by the compiler cost bound. -/
theorem routedVertex_card_le_box {V E : Type*} [Fintype V] [Fintype E] {half : ℕ}
    (data : Data V E half) : Fintype.card (RoutedVertex data) ≤ boxSites (2 * half) := by
  have hh := Fintype.card_le_of_injective (boxIndex data) (boxIndex_injective data)
  simpa only [Fintype.card_prod, Fintype.card_fin, boxSites, pow_two, Nat.mul_assoc] using hh

end Maxwell.Logical.Routing.Gluing
