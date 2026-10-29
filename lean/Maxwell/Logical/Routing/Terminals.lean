import Maxwell.Logical.Routing.SortSchedule

/-! Actual terminal connectors and corrected bottom stars. -/

namespace Maxwell.Logical.Routing.Terminals

open Maxwell.Logical.Routing
open Maxwell.Logical.Routing.Schedule
open Maxwell.Logical.Routing.SortSchedule

/-- The entire top connector: rise by 16, cross by 16, descend by 16. -/
def topPoint (t : ℕ) : Point :=
  if t ≤ 16 then (0, 0, t)
  else if t ≤ 32 then (t - 16, 0, 16)
  else (16, 0, 48 - t)

def topBridge (t : Fin 49) : Point := topPoint t.val

set_option maxRecDepth 100000 in
theorem topBridge_steps : ∀ t : Fin 48,
    UnitAdjacent (topBridge t.castSucc) (topBridge t.succ) := by decide

set_option maxRecDepth 100000 in
theorem topBridge_injective : Function.Injective topBridge := by decide

set_option maxRecDepth 100000 in
theorem topBridge_bounds : ∀ t : Fin 49,
    0 ≤ (topBridge t).1 ∧ (topBridge t).1 ≤ 16 ∧ (topBridge t).2.1 = 0 ∧
    0 ≤ (topBridge t).2.2 ∧ (topBridge t).2.2 ≤ 16 := by decide

set_option maxRecDepth 100000 in
theorem topBridge_faces : ∀ t : Fin 49,
    (topBridge t).2.2 = 0 ↔ t.val = 0 ∨ t.val = 48 := by decide

theorem topBridge_start : topBridge 0 = (0, 0, 0) := by decide

theorem topBridge_end : topBridge 48 = (16, 0, 0) := by decide

/-- A top bridge above the adjacent port pair `(2c,r),(2c+1,r)`. -/
def placedTopBridge (c r height : ℤ) (t : Fin 49) : Point :=
  translate (32 * c, 16 * r, height) (topBridge t)

/-- Distinct designated port pairs have disjoint complete top connectors. -/
theorem placedTopBridge_disjoint (c d r s height : ℤ) (hne : c ≠ d ∨ r ≠ s)
    (i j : Fin 49) : placedTopBridge c r height i ≠ placedTopBridge d s height j := by
  intro he
  have hi := topBridge_bounds i
  have hj := topBridge_bounds j
  have hp := congrArg (fun p : Point => (p.1, p.2.1)) he
  simp only [placedTopBridge, translate, Prod.mk.injEq] at hp
  omega

/-- A top connector can meet the routing slab only at its two prescribed ports. -/
theorem topBridge_meets_network_only_at_ports {q : ℕ} {target : Equiv.Perm (Port q)}
    (colors : RowColoring target) (token : Port q)
    (index : Assembly.TrajectoryIndex (routes (permutationSchedule colors) (6 * q)) token)
    (c r : ℤ) (t : Fin 49)
    (he : placedTopBridge c r (96 * q) t =
      Assembly.trajectoryPoint (routes (permutationSchedule colors) (6 * q)) token index) :
    t.val = 0 ∨ t.val = 48 := by
  have hb := permutationSchedule_box colors token index
  have ht := topBridge_bounds t
  have hz := congrArg (fun p : Point => p.2.2) he
  simp only [placedTopBridge, translate] at hz
  exact (topBridge_faces t).mp (by omega)

/-- One bipartition takes the fixed two-edge parity correction. Every
uncorrected edge has length 3 modulo 4 because slab lengths are multiples of 8. -/
def correctedArmLength (part : Bool) (arm : Fin 3) : ℕ :=
  armLength part arm + if part then 0 else 2

/-- Replace the vertical edge from height -8 to -7 by the actual three-edge
positive-x detour, on the height -16 bipartition. -/
def correctedArmPoint (part : Bool) (arm : Fin 3) (t : ℕ) : Point :=
  if part then armPoint part arm t
  else
    let cut := armHorizontalLength arm + 8
    if t ≤ cut then armPoint false arm t
    else if t = cut + 1 then translate (1, 0, 0) (armPoint false arm cut)
    else if t = cut + 2 then translate (1, 0, 0) (armPoint false arm (cut + 1))
    else armPoint false arm (t - 2)

def correctedArm (part : Bool) (arm : Fin 3)
    (t : Fin (correctedArmLength part arm + 1)) : Point := correctedArmPoint part arm t.val

set_option maxRecDepth 100000 in
theorem correctedArm_steps : ∀ (part : Bool) (arm : Fin 3)
    (t : Fin (correctedArmLength part arm)),
    UnitAdjacent (correctedArm part arm t.castSucc) (correctedArm part arm t.succ) := by decide

set_option maxRecDepth 100000 in
theorem correctedArm_injective : ∀ (part : Bool) (arm : Fin 3),
    Function.Injective (correctedArm part arm) := by decide

set_option maxRecDepth 100000 in
theorem correctedArms_meet_only_at_start : ∀ (part : Bool) (a b : Fin 3)
    (s : Fin (correctedArmLength part a + 1)) (t : Fin (correctedArmLength part b + 1)),
    a ≠ b → correctedArm part a s = correctedArm part b t → s.val = 0 ∧ t.val = 0 := by decide

set_option maxRecDepth 100000 in
theorem correctedArm_bounds : ∀ (part : Bool) (arm : Fin 3)
    (t : Fin (correctedArmLength part arm + 1)),
    0 ≤ (correctedArm part arm t).1 ∧ (correctedArm part arm t).1 ≤ 17 ∧
    0 ≤ (correctedArm part arm t).2.1 ∧ (correctedArm part arm t).2.1 ≤ 16 ∧
    -16 ≤ (correctedArm part arm t).2.2 ∧ (correctedArm part arm t).2.2 ≤ 0 := by decide

set_option maxRecDepth 100000 in
theorem correctedArm_face : ∀ (part : Bool) (arm : Fin 3)
    (t : Fin (correctedArmLength part arm + 1)),
    (correctedArm part arm t).2.2 = 0 ↔ t.val = correctedArmLength part arm := by decide

theorem correctedArm_start : ∀ (part : Bool) (arm : Fin 3),
    correctedArmPoint part arm 0 = (0, 0, -(bottomDepth part : ℤ)) := by decide

theorem correctedArm_end : ∀ (part : Bool) (arm : Fin 3),
    correctedArmPoint part arm (correctedArmLength part arm) = incidencePort arm := by decide

theorem correctedArm_length_bounds : ∀ (a b : Fin 3),
    correctedArmLength false a + correctedArmLength true b ≤ 65 := by decide

theorem correctedArm_length_mod_four : ∀ (a b : Fin 3),
    (correctedArmLength false a + correctedArmLength true b) % 4 = 1 := by decide

/-- The actual parity-corrected bottom stars in distinct tiles remain disjoint. -/
theorem corrected_bottom_stars_disjoint
    (c d r s : ℤ) (hne : c ≠ d ∨ r ≠ s)
    (part other : Bool) (a b : Fin 3) (i : Fin (correctedArmLength part a + 1))
    (j : Fin (correctedArmLength other b + 1)) :
    translate (32 * c, 32 * r, 0) (correctedArm part a i) ≠
      translate (32 * d, 32 * s, 0) (correctedArm other b j) := by
  intro he
  have hxy := congrArg (fun p : Point => (p.1, p.2.1)) he
  have hi := correctedArm_bounds part a i
  have hj := correctedArm_bounds other b j
  simp only [translate, Prod.mk.injEq] at hxy
  omega

/-- Bottom arms meet the network only at their actual incidence endpoints. -/
theorem correctedArm_meets_network_only_at_port {q : ℕ} {target : Equiv.Perm (Port q)}
    (colors : RowColoring target) (token : Port q)
    (index : Assembly.TrajectoryIndex (routes (permutationSchedule colors) (6 * q)) token)
    (c r : ℤ) (part : Bool) (arm : Fin 3) (t : Fin (correctedArmLength part arm + 1))
    (he : translate (32 * c, 32 * r, 0) (correctedArm part arm t) =
      Assembly.trajectoryPoint (routes (permutationSchedule colors) (6 * q)) token index) :
    t.val = correctedArmLength part arm := by
  have hb := permutationSchedule_box colors token index
  have ht := correctedArm_bounds part arm t
  have hz := congrArg (fun p : Point => p.2.2) he
  simp only [translate, zero_add] at hz
  exact (correctedArm_face part arm t).mp (by omega)

theorem rowLayer_length_dvd_four {q parity : ℕ} (selected : RowLayer.Selection q parity)
    (p : Port q) : 4 ∣ (rowLayer selected).length p := by
  change 4 ∣ RowLayer.pathLength selected p
  cases hm : RowLayer.movement selected p <;> simp [RowLayer.pathLength, hm]

theorem permutationSchedule_length_dvd_four {q : ℕ} {target : Equiv.Perm (Port q)}
    (colors : RowColoring target) (level : ℕ) (p : Port q) :
    4 ∣ (permutationSchedule colors level).length p := by
  unfold permutationSchedule appendSchedule
  split_ifs
  · exact rowLayer_length_dvd_four _ _
  · exact rowLayer_length_dvd_four _ _
  · exact rowLayer_length_dvd_four _ _

theorem trajectoryLength_dvd_four {q : ℕ} {target : Equiv.Perm (Port q)}
    (colors : RowColoring target) (p : Port q) :
    4 ∣ trajectoryLength (permutationSchedule colors) (6 * q) p := by
  apply Finset.dvd_sum
  intro level _
  exact permutationSchedule_length_dvd_four colors level.val _

/-- The complete corrected edge length, including both actual routed
trajectories, both bottom arms, and the complete top bridge. -/
noncomputable def edgeLength {q : ℕ} {target : Equiv.Perm (Port q)}
    (colors : RowColoring target) (a b : Fin 3) (left right : Port q) : ℕ :=
  correctedArmLength false a + trajectoryLength (permutationSchedule colors) (6 * q) left + 48 +
    trajectoryLength (permutationSchedule colors) (6 * q) right + correctedArmLength true b

theorem edgeLength_bound {q : ℕ} {target : Equiv.Perm (Port q)}
    (colors : RowColoring target) (a b : Fin 3) (left right : Port q) :
    edgeLength colors a b left right ≤ 480 * q + 113 := by
  have ha := correctedArm_length_bounds a b
  have hl := permutationSchedule_trajectoryLength_le colors left
  have hr := permutationSchedule_trajectoryLength_le colors right
  unfold edgeLength
  omega

theorem edgeLength_mod_four {q : ℕ} {target : Equiv.Perm (Port q)}
    (colors : RowColoring target) (a b : Fin 3) (left right : Port q) :
    edgeLength colors a b left right % 4 = 1 := by
  have ha := correctedArm_length_mod_four a b
  have hl := Nat.mod_eq_zero_of_dvd (trajectoryLength_dvd_four colors left)
  have hr := Nat.mod_eq_zero_of_dvd (trajectoryLength_dvd_four colors right)
  unfold edgeLength
  omega

theorem edgeLength_wire_form {q : ℕ} {target : Equiv.Perm (Port q)}
    (colors : RowColoring target) (a b : Fin 3) (left right : Port q) :
    ∃ j : ℕ, edgeLength colors a b left right = 4 * j + 1 := by
  have hh := edgeLength_mod_four colors a b left right
  exact ⟨edgeLength colors a b left right / 4, by omega⟩

end Maxwell.Logical.Routing.Terminals
