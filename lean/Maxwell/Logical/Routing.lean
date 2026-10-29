import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-! Exact unit-lattice swap paths used in cubic routing.  The fixed gadget
is verified exhaustively in the kernel; its translation theorems quantify
over every integral placement.  These local facts do not assume, or by
themselves establish, a global permutation-routing theorem. -/

namespace Maxwell.Logical.Routing

abbrev Point := ℤ × ℤ × ℤ

/-- The ordinary unit cubic lattice adjacency relation. -/
def UnitAdjacent (a b : Point) : Prop :=
  |a.1 - b.1| + |a.2.1 - b.2.1| + |a.2.2 - b.2.2| = 1

instance (a b : Point) : Decidable (UnitAdjacent a b) := inferInstanceAs (Decidable (_ = _))

/-- First of the two 40-edge crossing paths in the paper. -/
def swapA (t : Fin 41) : Point :=
  let s : ℤ := t.val
  if t.val ≤ 4 then (0, 0, s)
  else if t.val ≤ 8 then (0, s - 4, 4)
  else if t.val ≤ 24 then (s - 8, 4, 4)
  else if t.val ≤ 32 then (16, 4, s - 20)
  else if t.val ≤ 36 then (16, 36 - s, 12)
  else (16, 0, s - 24)

/-- Second 40-edge crossing path. -/
def swapB (t : Fin 41) : Point :=
  let s : ℤ := t.val
  if t.val ≤ 8 then (16, 0, s)
  else if t.val ≤ 12 then (16, 8 - s, 8)
  else if t.val ≤ 28 then (28 - s, -4, 8)
  else if t.val ≤ 32 then (0, -4, s - 20)
  else if t.val ≤ 36 then (0, s - 36, 12)
  else (0, 0, s - 24)

@[simp] theorem swapA_start : swapA 0 = (0, 0, 0) := by decide
@[simp] theorem swapA_end : swapA 40 = (16, 0, 16) := by decide
@[simp] theorem swapB_start : swapB 0 = (16, 0, 0) := by decide
@[simp] theorem swapB_end : swapB 40 = (0, 0, 16) := by decide

set_option maxRecDepth 100000 in
/-- Every step in both polylines is a unit lattice edge. -/
theorem swap_unit_steps :
    (∀ t : Fin 40, UnitAdjacent (swapA t.castSucc) (swapA t.succ)) ∧
    (∀ t : Fin 40, UnitAdjacent (swapB t.castSucc) (swapB t.succ)) := by decide

set_option maxRecDepth 100000 in
/-- Each path is simple; the two vertex sets are disjoint. -/
theorem swap_simple_disjoint :
    Function.Injective swapA ∧ Function.Injective swapB ∧
    (∀ s t, swapA s ≠ swapB t) := by decide

set_option maxRecDepth 100000 in
theorem swap_bounds :
    ∀ t : Fin 41,
      (0 ≤ (swapA t).1 ∧ (swapA t).1 ≤ 16 ∧
       0 ≤ (swapA t).2.1 ∧ (swapA t).2.1 ≤ 4 ∧
       0 ≤ (swapA t).2.2 ∧ (swapA t).2.2 ≤ 16) ∧
      (0 ≤ (swapB t).1 ∧ (swapB t).1 ≤ 16 ∧
       -4 ≤ (swapB t).2.1 ∧ (swapB t).2.1 ≤ 0 ∧
       0 ≤ (swapB t).2.2 ∧ (swapB t).2.2 ≤ 16) := by decide

set_option maxRecDepth 100000 in
/-- No interior path vertex lies on a slab face. -/
theorem swap_interior_faces :
    ∀ t : Fin 41, t ≠ 0 → t ≠ 40 →
      (0 < (swapA t).2.2 ∧ (swapA t).2.2 < 16) ∧
      (0 < (swapB t).2.2 ∧ (swapB t).2.2 < 16) := by decide

/-- Integral translation of a lattice point. -/
def translate (v a : Point) : Point :=
  (v.1 + a.1, v.2.1 + a.2.1, v.2.2 + a.2.2)

theorem translate_injective (v : Point) : Function.Injective (translate v) := by
  intro a b h
  rcases a with ⟨ax, ay, az⟩
  rcases b with ⟨bx, byy, bz⟩
  simp only [translate, Prod.mk.injEq, add_right_inj] at h
  exact Prod.ext h.1 (Prod.ext h.2.1 h.2.2)

theorem translate_unit_adjacent (v a b : Point) :
    UnitAdjacent (translate v a) (translate v b) ↔ UnitAdjacent a b := by
  simp only [UnitAdjacent, translate, add_sub_add_left_eq_sub]

/-- Every translated copy has simple disjoint paths and unit steps. -/
theorem translated_swap (v : Point) :
    Function.Injective (translate v ∘ swapA) ∧
    Function.Injective (translate v ∘ swapB) ∧
    (∀ s t, translate v (swapA s) ≠ translate v (swapB t)) ∧
    (∀ t : Fin 40, UnitAdjacent (translate v (swapA t.castSucc))
      (translate v (swapA t.succ))) ∧
    (∀ t : Fin 40, UnitAdjacent (translate v (swapB t.castSucc))
      (translate v (swapB t.succ))) := by
  refine ⟨(translate_injective v).comp swap_simple_disjoint.1,
    (translate_injective v).comp swap_simple_disjoint.2.1, ?_, ?_, ?_⟩
  · intro s t h
    exact swap_simple_disjoint.2.2 s t (translate_injective v h)
  · intro t
    exact (translate_unit_adjacent _ _ _).mpr (swap_unit_steps.1 t)
  · intro t
    exact (translate_unit_adjacent _ _ _).mpr (swap_unit_steps.2 t)

/-- Coordinate interchange turns a row gadget into a column gadget. -/
def transposeXY (a : Point) : Point := (a.2.1, a.1, a.2.2)

theorem transposeXY_injective : Function.Injective transposeXY := by
  intro a b h
  have h' := congrArg transposeXY h
  simpa only [transposeXY] using h'

theorem transposeXY_unit_adjacent (a b : Point) :
    UnitAdjacent (transposeXY a) (transposeXY b) ↔ UnitAdjacent a b := by
  simp only [UnitAdjacent, transposeXY]
  rw [add_comm |a.2.1 - b.2.1| |a.1 - b.1|]

/-- An odd path length is corrected by zero or two extra edges. -/
def parityCorrection (length : ℕ) : ℕ := if length % 4 = 1 then 0 else 2

theorem parityCorrection_le_two (length : ℕ) : parityCorrection length ≤ 2 := by
  unfold parityCorrection
  split_ifs <;> omega

theorem corrected_length_mod_four (length : ℕ) (hodd : length % 2 = 1) :
    (length + parityCorrection length) % 4 = 1 := by
  unfold parityCorrection
  split_ifs <;> omega

/-- Either strand of the local swap. -/
def swap (strand : Bool) : Fin 41 → Point := if strand then swapA else swapB

lemma swap_xy_bounds (strand : Bool) (t : Fin 41) :
    0 ≤ (swap strand t).1 ∧ (swap strand t).1 ≤ 16 ∧
    -4 ≤ (swap strand t).2.1 ∧ (swap strand t).2.1 ≤ 4 := by
  cases strand
  · have h := (swap_bounds t).2
    simp only [swap, Bool.false_eq_true, ↓reduceIte]
    omega
  · have h := (swap_bounds t).1
    simp only [swap, ↓reduceIte]
    omega

/-- A row swap placed at integral array coordinates `(column,row)`. -/
def rowSwap (column row height : ℤ) (strand : Bool) (t : Fin 41) : Point :=
  translate (16 * column, 16 * row, height) (swap strand t)

/-- Distinct pairs in the same comparison layer have disjoint swap boxes;
row separation is 16 and sideways excursions have radius only four. -/
theorem parallel_row_swaps_disjoint
    (c d r s z : ℤ) (hsep : r ≠ s ∨ c + 1 < d ∨ d + 1 < c)
    (a b : Bool) (i j : Fin 41) : rowSwap c r z a i ≠ rowSwap d s z b j := by
  intro he
  have hxy := congrArg (fun p : Point => (p.1, p.2.1)) he
  have ha := swap_xy_bounds a i
  have hb := swap_xy_bounds b j
  simp only [rowSwap, translate, Prod.mk.injEq] at hxy
  omega

/-- Unswapped columns outside a swap pair do not enter its box. -/
theorem row_swap_stationary_disjoint
    (c d r s z w : ℤ) (hsep : r ≠ s ∨ d < c ∨ c + 1 < d)
    (a : Bool) (i : Fin 41) : rowSwap c r z a i ≠ (16 * d, 16 * s, w) := by
  intro he
  have hxy := congrArg (fun p : Point => (p.1, p.2.1)) he
  have ha := swap_xy_bounds a i
  simp only [rowSwap, translate, Prod.mk.injEq] at hxy
  omega

/-- A three-edge replacement for the arm segment from height -8 to -7. -/
def detour : Fin 4 → Point
  | 0 => (0, 0, -8)
  | 1 => (1, 0, -8)
  | 2 => (1, 0, -7)
  | 3 => (0, 0, -7)

theorem detour_unit_steps :
    ∀ i : Fin 3, UnitAdjacent (detour i.castSucc) (detour i.succ) := by decide

theorem detour_injective : Function.Injective detour := by decide

theorem detour_endpoints : detour 0 = (0, 0, -8) ∧ detour 3 = (0, 0, -7) := by decide

/-- Translating the detour to any incidence arm preserves simplicity and
unit edges, while retaining exactly the replaced segment endpoints. -/
theorem translated_detour (v : Point) :
    Function.Injective (translate v ∘ detour) ∧
    (∀ i : Fin 3, UnitAdjacent (translate v (detour i.castSucc))
      (translate v (detour i.succ))) := by
  refine ⟨(translate_injective v).comp detour_injective, ?_⟩
  intro i
  exact (translate_unit_adjacent _ _ _).mpr (detour_unit_steps i)

/-- Distinct incidence-arm detours on the 16-spaced array are disjoint. -/
theorem arm_detours_disjoint (c d r s : ℤ) (h : c ≠ d ∨ r ≠ s)
    (i j : Fin 4) :
    translate (16 * c, 16 * r, 0) (detour i) ≠
      translate (16 * d, 16 * s, 0) (detour j) := by
  intro he
  have hxy := congrArg (fun p : Point => (p.1, p.2.1)) he
  have hi : 0 ≤ (detour i).1 ∧ (detour i).1 ≤ 1 ∧ (detour i).2.1 = 0 := by
    exact (by decide : ∀ t : Fin 4, 0 ≤ (detour t).1 ∧ (detour t).1 ≤ 1 ∧ (detour t).2.1 = 0) i
  have hj : 0 ≤ (detour j).1 ∧ (detour j).1 ≤ 1 ∧ (detour j).2.1 = 0 := by
    exact (by decide : ∀ t : Fin 4, 0 ≤ (detour t).1 ∧ (detour t).1 ≤ 1 ∧ (detour t).2.1 = 0) j
  simp only [translate, Prod.mk.injEq] at hxy
  omega

/-- The concrete layer and path-length budgets in the routing construction. -/
def layerCount (q : ℕ) := 6 * q

def trajectoryLengthBound (q : ℕ) := 40 * layerCount q

def edgeLengthBound (q : ℕ) := 2 * trajectoryLengthBound q + 64 + 32 + 16 + 2

theorem trajectory_length_formula (q : ℕ) : trajectoryLengthBound q = 240 * q := by
  simp [trajectoryLengthBound, layerCount]; omega

theorem edge_length_formula (q : ℕ) : edgeLengthBound q = 480 * q + 114 := by
  simp [edgeLengthBound, trajectoryLengthBound, layerCount]; omega

theorem edge_length_le (q : ℕ) (hq : 1 ≤ q) : edgeLengthBound q ≤ 1024 * q := by
  rw [edge_length_formula]; omega

/-- Inclusive integer side lengths of a containing box. -/
def boxSideXY (q : ℕ) := 16 * q + 9

def boxSideZ (q : ℕ) := 96 * q + 33

def boxSites (q : ℕ) := boxSideXY q * boxSideXY q * boxSideZ q

/-- The ambient box is cubic in the port-array side, with explicit constant. -/
theorem box_sites_le (q : ℕ) (hq : 1 ≤ q) : boxSites q ≤ 80625 * q ^ 3 := by
  have hx : boxSideXY q ≤ 25 * q := by unfold boxSideXY; omega
  have hz : boxSideZ q ≤ 129 * q := by unfold boxSideZ; omega
  calc
    boxSites q ≤ (25 * q) * (25 * q) * (129 * q) :=
      Nat.mul_le_mul (Nat.mul_le_mul hx hx) hz
    _ = 80625 * q ^ 3 := by ring

/-- Every translated swap used in any of the `6*q` layers is inside the
claimed common horizontal box and the routing height range. -/
theorem row_swap_global_bounds (q : ℕ) (c r layer : Fin q)
    (phase : Fin 6) (a : Bool) (i : Fin 41) :
    let p := rowSwap c.val r.val (16 * (phase.val * q + layer.val)) a i;
    -4 ≤ p.1 ∧ p.1 ≤ 16 * q + 4 ∧
    -4 ≤ p.2.1 ∧ p.2.1 ≤ 16 * q + 4 ∧
    0 ≤ p.2.2 ∧ p.2.2 ≤ 96 * q := by
  have hxy := swap_xy_bounds a i
  have hz : 0 ≤ (swap a i).2.2 ∧ (swap a i).2.2 ≤ 16 := by
    cases a
    · exact (swap_bounds i).2.2.2.2.2
    · exact (swap_bounds i).1.2.2.2.2
  have hc := c.isLt
  have hr := r.isLt
  have hl := layer.isLt
  have hp := phase.isLt
  dsimp [rowSwap, translate]
  norm_cast at *
  have hm : phase.val * q ≤ 5 * q := Nat.mul_le_mul_right q (by omega)
  have hh : phase.val * q + layer.val < 6 * q := by omega
  omega

/-- Least power-of-two half-side whose square covers the graph vertices. -/
def portHalfSide (vertices : ℕ) := 2 ^ Nat.clog 4 vertices

def portSide (vertices : ℕ) := 2 * portHalfSide vertices

lemma portHalfSide_square (vertices : ℕ) : portHalfSide vertices ^ 2 = 4 ^ Nat.clog 4 vertices := by
  unfold portHalfSide
  rw [← pow_mul, Nat.mul_comm (Nat.clog 4 vertices) 2, pow_mul]
  norm_num

theorem portSide_power_two (vertices : ℕ) :
    portSide vertices = 2 ^ (Nat.clog 4 vertices + 1) := by
  simp [portSide, portHalfSide, pow_succ, Nat.mul_comm]

theorem portSide_square_bounds (vertices : ℕ) (h : 0 < vertices) :
    4 * vertices ≤ portSide vertices ^ 2 ∧ portSide vertices ^ 2 < 16 * vertices := by
  have hlow : vertices ≤ portHalfSide vertices ^ 2 := by
    rw [portHalfSide_square]
    exact Nat.le_pow_clog (by decide) vertices
  have hup : portHalfSide vertices ^ 2 < 4 * vertices := by
    by_cases h1 : vertices = 1
    · subst vertices
      norm_num [portHalfSide]
    · have h2 : 1 < vertices := by omega
      have hp := Nat.pow_pred_clog_lt_self (b := 4) (by decide) h2
      simp only [Nat.pred_eq_sub_one] at hp
      have hc := Nat.clog_pos (b := 4) (by decide) h2
      have he : Nat.clog 4 vertices = Nat.clog 4 vertices - 1 + 1 := by omega
      rw [portHalfSide_square, he, pow_succ]
      omega
  unfold portSide
  constructor <;> nlinarith

/-- The real square-root inequalities quoted in the routing lemma. -/
theorem portSide_sqrt_bounds (vertices : ℕ) (h : 0 < vertices) :
    2 * Real.sqrt vertices ≤ (portSide vertices : ℝ) ∧
      (portSide vertices : ℝ) < 4 * Real.sqrt vertices := by
  have hsq := Real.sq_sqrt (Nat.cast_nonneg vertices : (0 : ℝ) ≤ vertices)
  have hnon := Real.sqrt_nonneg (vertices : ℝ)
  obtain ⟨hl, hu⟩ := portSide_square_bounds vertices h
  have hl' : (4 : ℝ) * vertices ≤ (portSide vertices : ℝ) ^ 2 := by exact_mod_cast hl
  have hu' : (portSide vertices : ℝ) ^ 2 < (16 : ℝ) * vertices := by exact_mod_cast hu
  constructor <;> nlinarith [Nat.cast_nonneg (α := ℝ) (portSide vertices)]

/-- Ports are represented as `(column,row)`. -/
abbrev Port (q : ℕ) := Fin q × Fin q

/-- A proper color assignment for source-row/target-row incidence tokens.
Existence and construction of this coloring are separate obligations. -/
structure RowColoring {q : ℕ} (target : Equiv.Perm (Port q)) where
  color : Port q → Fin q
  source_unique : ∀ a b, a.2 = b.2 → color a = color b → a = b
  target_unique : ∀ a b, (target a).2 = (target b).2 → color a = color b → a = b

def firstPlacement {q : ℕ} {target : Equiv.Perm (Port q)}
    (colors : RowColoring target) (token : Port q) : Port q :=
  (colors.color token, token.2)

def secondPlacement {q : ℕ} {target : Equiv.Perm (Port q)}
    (colors : RowColoring target) (token : Port q) : Port q :=
  (colors.color token, (target token).2)

theorem firstPlacement_injective {q : ℕ} {target : Equiv.Perm (Port q)}
    (colors : RowColoring target) : Function.Injective (firstPlacement colors) := by
  intro a b h
  simp only [firstPlacement, Prod.mk.injEq] at h
  exact colors.source_unique a b h.2 h.1

theorem secondPlacement_injective {q : ℕ} {target : Equiv.Perm (Port q)}
    (colors : RowColoring target) : Function.Injective (secondPlacement colors) := by
  intro a b h
  simp only [secondPlacement, Prod.mk.injEq] at h
  exact colors.target_unique a b h.2 h.1

noncomputable def firstPermutation {q : ℕ} {target : Equiv.Perm (Port q)}
    (colors : RowColoring target) : Equiv.Perm (Port q) :=
  Equiv.ofBijective (firstPlacement colors)
    ⟨firstPlacement_injective colors, Finite.surjective_of_injective (firstPlacement_injective colors)⟩

noncomputable def secondPermutation {q : ℕ} {target : Equiv.Perm (Port q)}
    (colors : RowColoring target) : Equiv.Perm (Port q) :=
  Equiv.ofBijective (secondPlacement colors)
    ⟨secondPlacement_injective colors, Finite.surjective_of_injective (secondPlacement_injective colors)⟩

/-- The middle phase maps the first placement to the second placement. -/
noncomputable def columnPhase {q : ℕ} {target : Equiv.Perm (Port q)}
    (colors : RowColoring target) : Equiv.Perm (Port q) :=
  (firstPermutation colors).symm.trans (secondPermutation colors)

/-- The final phase maps the second placement to the prescribed target. -/
noncomputable def finalRowPhase {q : ℕ} {target : Equiv.Perm (Port q)}
    (colors : RowColoring target) : Equiv.Perm (Port q) :=
  (secondPermutation colors).symm.trans target

theorem first_phase_preserves_row {q : ℕ} {target : Equiv.Perm (Port q)}
    (colors : RowColoring target) (p : Port q) : (firstPermutation colors p).2 = p.2 := rfl

theorem column_phase_preserves_column {q : ℕ} {target : Equiv.Perm (Port q)}
    (colors : RowColoring target) (p : Port q) : (columnPhase colors p).1 = p.1 := by
  have h := congrArg Prod.fst ((firstPermutation colors).apply_symm_apply p)
  exact h

theorem final_phase_preserves_row {q : ℕ} {target : Equiv.Perm (Port q)}
    (colors : RowColoring target) (p : Port q) : (finalRowPhase colors p).2 = p.2 := by
  have h := congrArg Prod.snd ((secondPermutation colors).apply_symm_apply p)
  exact h

/-- For every array size and every proper token coloring, the three actual
permutations realize the prescribed target with row-column-row locality. -/
theorem three_phase_routing {q : ℕ} {target : Equiv.Perm (Port q)}
    (colors : RowColoring target) (token : Port q) :
    finalRowPhase colors (columnPhase colors (firstPermutation colors token)) = target token := by
  simp [finalRowPhase, columnPhase]

/-- Magnitude of the bottom vertex height in the two bipartitions. -/
def bottomDepth (part : Bool) : ℕ := if part then 15 else 16

def armHorizontalLength (arm : Fin 3) : ℕ := if arm = 0 then 0 else 16

def armLength (part : Bool) (arm : Fin 3) : ℕ :=
  armHorizontalLength arm + bottomDepth part

/-- The three actual bottom arms: horizontal spoke first, then vertical. -/
def armPoint (part : Bool) (arm : Fin 3) (t : ℕ) : Point :=
  let h := armHorizontalLength arm
  let x : ℤ := if arm = 1 then min t h else 0
  let y : ℤ := if arm = 2 then min t h else 0
  (x, y, -(bottomDepth part : ℤ) + (t - h : ℕ))

def bottomArm (part : Bool) (arm : Fin 3) (t : Fin (armLength part arm + 1)) : Point :=
  armPoint part arm t.val

set_option maxRecDepth 100000 in
theorem bottom_arm_unit_steps :
    ∀ (part : Bool) (arm : Fin 3) (t : Fin (armLength part arm)),
      UnitAdjacent (bottomArm part arm t.castSucc) (bottomArm part arm t.succ) := by decide

set_option maxRecDepth 100000 in
theorem bottom_arm_simple :
    ∀ (part : Bool) (arm : Fin 3), Function.Injective (bottomArm part arm) := by decide

set_option maxRecDepth 100000 in
theorem bottom_arms_meet_only_at_start :
    ∀ (part : Bool) (a b : Fin 3) (s : Fin (armLength part a + 1))
      (t : Fin (armLength part b + 1)),
      a ≠ b → bottomArm part a s = bottomArm part b t → s.val = 0 ∧ t.val = 0 := by decide

set_option maxRecDepth 100000 in
theorem bottom_arm_bounds :
    ∀ (part : Bool) (arm : Fin 3) (t : Fin (armLength part arm + 1)),
      0 ≤ (bottomArm part arm t).1 ∧ (bottomArm part arm t).1 ≤ 16 ∧
      0 ≤ (bottomArm part arm t).2.1 ∧ (bottomArm part arm t).2.1 ≤ 16 ∧
      -16 ≤ (bottomArm part arm t).2.2 ∧ (bottomArm part arm t).2.2 ≤ 0 := by decide

theorem bottom_arm_start : ∀ (part : Bool) (arm : Fin 3),
    armPoint part arm 0 = (0, 0, -(bottomDepth part : ℤ)) := by decide

def incidencePort (arm : Fin 3) : Point :=
  if arm = 0 then (0, 0, 0) else if arm = 1 then (16, 0, 0) else (0, 16, 0)

theorem bottom_arm_end : ∀ (part : Bool) (arm : Fin 3),
    armPoint part arm (armLength part arm) = incidencePort arm := by decide

/-- Distinct 32-spaced vertex tiles have disjoint bottom stars. -/
theorem different_bottom_stars_disjoint
    (c d r s : ℤ) (hne : c ≠ d ∨ r ≠ s)
    (part other : Bool) (a b : Fin 3) (i : Fin (armLength part a + 1))
    (j : Fin (armLength other b + 1)) :
    translate (32 * c, 32 * r, 0) (bottomArm part a i) ≠
      translate (32 * d, 32 * s, 0) (bottomArm other b j) := by
  intro he
  have hxy := congrArg (fun p : Point => (p.1, p.2.1)) he
  have hi := bottom_arm_bounds part a i
  have hj := bottom_arm_bounds other b j
  simp only [translate, Prod.mk.injEq] at hxy
  omega

/-- Integer coordinate sum, whose parity colors the cubic lattice. -/
def coordinateSum (p : Point) : ℤ := p.1 + p.2.1 + p.2.2

theorem unit_adjacent_parity (a b : Point) (h : UnitAdjacent a b) :
    (coordinateSum b - coordinateSum a) % 2 = 1 := by
  unfold UnitAdjacent at h
  unfold coordinateSum
  rw [abs_eq_max_neg, abs_eq_max_neg, abs_eq_max_neg] at h
  omega

/-- Every finite unit-lattice walk flips parity once per edge. -/
theorem walk_parity (walk : ℕ → Point) (length : ℕ)
    (hstep : ∀ t < length, UnitAdjacent (walk t) (walk (t + 1))) :
    (coordinateSum (walk length) - coordinateSum (walk 0)) % 2 = (length : ℤ) % 2 := by
  induction length with
  | zero => simp
  | succ length ih =>
    have hprefix : ∀ t < length, UnitAdjacent (walk t) (walk (t + 1)) := by
      intro t ht
      exact hstep t (by omega)
    have hp := ih hprefix
    have hs := unit_adjacent_parity (walk length) (walk (length + 1))
      (hstep length (by omega))
    push_cast
    omega

theorem walk_length_odd_of_endpoint_parity (walk : ℕ → Point) (length : ℕ)
    (hstep : ∀ t < length, UnitAdjacent (walk t) (walk (t + 1)))
    (hend : (coordinateSum (walk length) - coordinateSum (walk 0)) % 2 = 1) :
    length % 2 = 1 := by
  have h := walk_parity walk length hstep
  omega

/-- The selected bipartition heights give opposite endpoint lattice parity,
independently of the integer tile coordinates. -/
theorem bottom_bipartition_parity (c d r s : ℤ) :
    (coordinateSum (translate (32 * d, 32 * s, 0) (0, 0, -(bottomDepth true : ℤ))) -
      coordinateSum (translate (32 * c, 32 * r, 0) (0, 0, -(bottomDepth false : ℤ)))) % 2 = 1 := by
  norm_num [coordinateSum, translate, bottomDepth]
  omega

set_option maxRecDepth 100000 in
/-- The two new detour vertices avoid every original bottom arm in the tile. -/
theorem detour_interior_avoids_bottom_arms :
    ∀ (part : Bool) (a b : Fin 3) (i : Fin 4) (t : Fin (armLength part b + 1)),
      (i = 1 ∨ i = 2) → translate (incidencePort a) (detour i) ≠ bottomArm part b t := by decide

/-- All bottom arms for an `a` by `a` tile array fit the common box for `q=2a`. -/
theorem bottom_global_bounds (a : ℕ) (c r : Fin a)
    (part : Bool) (arm : Fin 3) (t : Fin (armLength part arm + 1)) :
    let p := translate (32 * c.val, 32 * r.val, 0) (bottomArm part arm t)
    0 ≤ p.1 ∧ p.1 ≤ 16 * (2 * a) ∧
    0 ≤ p.2.1 ∧ p.2.1 ≤ 16 * (2 * a) ∧
    -16 ≤ p.2.2 ∧ p.2.2 ≤ 0 := by
  have hb := bottom_arm_bounds part arm t
  have hc := c.isLt
  have hr := r.isLt
  dsimp [translate]
  omega

end Maxwell.Logical.Routing
