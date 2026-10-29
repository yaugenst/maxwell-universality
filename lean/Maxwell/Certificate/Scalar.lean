import Mathlib.Tactic.NormNum
import Mathlib.Data.Rat.Cast.Order

/-! Exact arithmetic portion of `verify_local_edge_scalar.py`, including the
whole-radius coercivity constants, and the global-comparator scalar transfer.
The statements concern the rational expressions themselves. -/
namespace Maxwell.Certificate.Scalar

def radius : ℚ := 1/20
def theta : ℚ := 11/70
def tailRatio : ℚ := (2 * theta * radius)^2 / 12
def tail : ℚ := 1 / (1 - 1/40000)
def a2 : ℚ := (4 * 2^2 + 6) / 2 * theta^2
def a3 : ℚ := (4 * 2^3 + 6) / 6 * theta^3
def a4 : ℚ := (4 * 2^4 + 6) / 24 * theta^4
def k4Bound : ℚ := (a4 + 6*a3 + 9*a2) * tail
def r3Bound : ℚ := (a3 + 3*a2) * tail
def r4Bound : ℚ := (a4 + 3*a3) * tail

theorem tail_ratio_bound : tailRatio < 1/40000 := by
  norm_num [tailRatio, theta, radius]
theorem fourth_order_bound : k4Bound < 13/5 := by
  norm_num [k4Bound, a4, a3, a2, theta, tail]
theorem third_residual_bound : r3Bound < 17/20 := by
  norm_num [r3Bound, a3, a2, theta, tail]
theorem fourth_residual_bound : r4Bound < 2/25 := by
  norm_num [r4Bound, a4, a3, theta, tail]

def kmin : ℚ := 1/50
def kmax : ℚ := 1
def c2 : ℚ := 18/5
def delta : ℚ := 1/2^20
def b : ℚ := 7/256
def elo : ℚ := 239/25000
def ehi : ℚ := 957/100000
def blo : ℚ := b - ehi
def bhi : ℚ := b - elo
def k4 : ℚ := 13/5
def c3 : ℚ := 17/20
def c4 : ℚ := 2/25

def gRelativeLower : ℚ :=
  blo - 2 * delta * kmax / kmin - c2 * radius^2
    - bhi * k4 / kmin * radius^2 - 2 * delta * c4 / kmin * radius^2
    - (27 * c4 + c3^2 / kmin) * radius^4
    - c4^2 / kmin * radius^6

theorem sqrt_ratio_bound : c2 / kmin < (27/2)^2 := by norm_num [c2, kmin]
theorem delta_lt_blo : delta < blo := by norm_num [delta, blo, b, ehi]
theorem g_relative_lower_value : gRelativeLower = 2178546479/819200000000 := by
  norm_num [gRelativeLower, blo, bhi, b, elo, ehi, delta, kmax, kmin, c2, radius, k4, c4, c3]
theorem g_coercivity : 1/400 < gRelativeLower := by rw [g_relative_lower_value]; norm_num

def bandCoercivity : ℚ := (1/400 * kmin) / (1 + 3^2 * radius^2) / b

theorem band_coercivity_value : bandCoercivity = 128/71575 := by
  norm_num [bandCoercivity, kmin, radius, b]
theorem band_coercivity : 1/600 < bandCoercivity := by rw [band_coercivity_value]; norm_num

def shift : ℚ := 157/16384
def exclusionMargin : ℚ := 1/2^24
def materialPerturbation : ℚ := 1023/2^26
def selectedUpper : ℚ := 23913/2500000

theorem material_perturbation_lt_bulk_gap : materialPerturbation < 1/4096 := by
  norm_num [materialPerturbation]
theorem shifted_exclusion_value : shift + exclusionMargin - materialPerturbation = 642053/2^26 := by
  norm_num [shift, exclusionMargin, materialPerturbation]
theorem outside_separation :
    1/500000 < shift + exclusionMargin - materialPerturbation - selectedUpper := by
  norm_num [shift, exclusionMargin, materialPerturbation, selectedUpper]

/-- The audited constants as one finite theorem, usable without rerunning
any Python or accepting a status receipt. -/
theorem local_scalar_acceptance :
    tailRatio < 1/40000 ∧ k4Bound < 13/5 ∧ r3Bound < 17/20 ∧
    r4Bound < 2/25 ∧ delta < blo ∧ 1/400 < gRelativeLower ∧ 1/600 < bandCoercivity :=
  ⟨tail_ratio_bound, fourth_order_bound, third_residual_bound, fourth_residual_bound,
    delta_lt_blo, g_coercivity, band_coercivity⟩

end Maxwell.Certificate.Scalar
