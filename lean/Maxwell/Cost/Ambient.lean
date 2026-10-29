import Maxwell.Cost.Compiler
import Maxwell.Logical.Routing
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Maxwell.Cost
open Maxwell.Logical.Routing

/-- Every ambient coordinate in the explicit containing cuboid is charged.
This theorem instantiates the loop with the concrete routing dimensions. -/
theorem routing_box_write_cost (q perCell : ℕ)
    (body : ℕ → ℕ → ℕ → Program Unit) (hq : 1 ≤ q)
    (hbody : ∀ x < boxSideXY q, ∀ y < boxSideXY q, ∀ z < boxSideZ q,
      (body x y z).steps ≤ perCell) :
    (forBox (boxSideXY q) (boxSideXY q) (boxSideZ q) body).steps ≤
      80625 * q ^ 3 * perCell := by
  exact (forBox_steps_le _ _ _ _ _ hbody).trans
    (Nat.mul_le_mul_right perCell (box_sites_le q hq))

/-- The computed power-of-two port side gives the actual `U^(3/2)`
ambient-loop exponent; there is no uncounted sparse-output convention. -/
theorem portSide_cube_bound (U : ℕ) (hU : 0 < U) :
    ((portSide U : ℕ) : ℝ) ^ 3 ≤ 64 * (U : ℝ) ^ (3 / 2 : ℝ) := by
  have hside := (portSide_sqrt_bounds U hU).2.le
  have hs : (Real.sqrt (U : ℝ)) ^ 3 = (U : ℝ) ^ (3 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg U)]
    congr 1
    norm_num
  calc
    ((portSide U : ℕ) : ℝ) ^ 3 ≤ (4 * Real.sqrt (U : ℝ)) ^ 3 := by
      gcongr
    _ = 64 * (U : ℝ) ^ (3 / 2 : ℝ) := by rw [mul_pow, hs]; norm_num

theorem ambient_three_halves_cost (U perCell : ℕ) (hU : 0 < U)
    (body : ℕ → ℕ → ℕ → Program Unit)
    (hbody : ∀ x < boxSideXY (portSide U), ∀ y < boxSideXY (portSide U),
      ∀ z < boxSideZ (portSide U), (body x y z).steps ≤ perCell) :
    ((forBox (boxSideXY (portSide U)) (boxSideXY (portSide U))
        (boxSideZ (portSide U)) body).steps : ℝ) ≤
      5160000 * (U : ℝ) ^ (3 / 2 : ℝ) * perCell := by
  have hq : 1 ≤ portSide U := by
    unfold portSide portHalfSide
    have hpow : 0 < 2 ^ Nat.clog 4 U := Nat.pow_pos (by omega)
    omega
  have hcost := routing_box_write_cost (portSide U) perCell body hq hbody
  have hcostReal :
      ((forBox (boxSideXY (portSide U)) (boxSideXY (portSide U))
        (boxSideZ (portSide U)) body).steps : ℝ) ≤
        80625 * (portSide U : ℝ) ^ 3 * (perCell : ℝ) := by exact_mod_cast hcost
  have hcube := portSide_cube_bound U hU
  calc
    _ ≤ 80625 * (portSide U : ℝ) ^ 3 * perCell := hcostReal
    _ ≤ 80625 * (64 * (U : ℝ) ^ (3 / 2 : ℝ)) * perCell := by gcongr
    _ = 5160000 * (U : ℝ) ^ (3 / 2 : ℝ) * perCell := by ring

/-- Physical separation and collar width enlarge every side; they are
included before every cell is emitted, so no defect-only size is charged. -/
def physicalSideXY (q spacing buffer : ℕ) := spacing * boxSideXY q + 2 * buffer

def physicalSideZ (q spacing buffer : ℕ) := spacing * boxSideZ q + 2 * buffer

def physicalVolumeFactor (spacing buffer : ℕ) :=
  (25 * spacing + 2 * buffer) ^ 2 * (129 * spacing + 2 * buffer)

theorem physical_box_volume (q spacing buffer : ℕ) (hq : 1 ≤ q) :
    physicalSideXY q spacing buffer * physicalSideXY q spacing buffer *
      physicalSideZ q spacing buffer ≤ physicalVolumeFactor spacing buffer * q ^ 3 := by
  have hb : 2 * buffer ≤ 2 * buffer * q := by nlinarith
  have hx : physicalSideXY q spacing buffer ≤ (25 * spacing + 2 * buffer) * q := by
    unfold physicalSideXY boxSideXY
    nlinarith
  have hz : physicalSideZ q spacing buffer ≤ (129 * spacing + 2 * buffer) * q := by
    unfold physicalSideZ boxSideZ
    nlinarith
  calc
    _ ≤ ((25 * spacing + 2 * buffer) * q) * ((25 * spacing + 2 * buffer) * q) *
        ((129 * spacing + 2 * buffer) * q) := Nat.mul_le_mul (Nat.mul_le_mul hx hx) hz
    _ = physicalVolumeFactor spacing buffer * q ^ 3 := by
      unfold physicalVolumeFactor
      ring

theorem physical_ambient_three_halves_cost (U spacing buffer perCell : ℕ) (hU : 0 < U)
    (body : ℕ → ℕ → ℕ → Program Unit)
    (hbody : ∀ x < physicalSideXY (portSide U) spacing buffer,
      ∀ y < physicalSideXY (portSide U) spacing buffer,
      ∀ z < physicalSideZ (portSide U) spacing buffer, (body x y z).steps ≤ perCell) :
    ((forBox (physicalSideXY (portSide U) spacing buffer)
        (physicalSideXY (portSide U) spacing buffer)
        (physicalSideZ (portSide U) spacing buffer) body).steps : ℝ) ≤
      64 * physicalVolumeFactor spacing buffer * (U : ℝ) ^ (3 / 2 : ℝ) * perCell := by
  have hq : 1 ≤ portSide U := by
    rw [portSide_power_two]
    exact Nat.one_le_pow _ _ (by omega)
  have hwork := (forBox_steps_le _ _ _ _ _ hbody).trans
    (Nat.mul_le_mul_right perCell (physical_box_volume (portSide U) spacing buffer hq))
  have hworkReal :
    ((forBox (physicalSideXY (portSide U) spacing buffer)
        (physicalSideXY (portSide U) spacing buffer)
        (physicalSideZ (portSide U) spacing buffer) body).steps : ℝ) ≤
      physicalVolumeFactor spacing buffer * (portSide U : ℝ) ^ 3 * perCell := by
    exact_mod_cast hwork
  have hcube := portSide_cube_bound U hU
  calc
    _ ≤ physicalVolumeFactor spacing buffer * (portSide U : ℝ) ^ 3 * perCell := hworkReal
    _ ≤ physicalVolumeFactor spacing buffer * (64 * (U : ℝ) ^ (3 / 2 : ℝ)) * perCell := by
      gcongr
    _ = 64 * physicalVolumeFactor spacing buffer * (U : ℝ) ^ (3 / 2 : ℝ) * perCell := by ring

end Maxwell.Cost
