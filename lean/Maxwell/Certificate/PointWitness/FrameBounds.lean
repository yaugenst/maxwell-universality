import Maxwell.Certificate.PointWitness.Bounds0
import Maxwell.Certificate.PointWitness.Bounds1
import Maxwell.Certificate.PointWitness.Gram

namespace Maxwell.Certificate.PointWitness
noncomputable section

theorem pointVector0_norm_near_one : |‖pointVector0‖ - 1| ≤ (1 : ℝ) / 2^39 := by
  have h := integerVector_norm_sq numerator0 (2^101)
  change ‖pointVector0‖^2 = _ at h
  rw [norm0_checked] at h
  have hn := norm_nonneg pointVector0
  rw [abs_le]
  constructor <;> norm_num at * <;> nlinarith [norm_nonneg pointVector0]

theorem pointVector1_norm_near_one : |‖pointVector1‖ - 1| ≤ (1 : ℝ) / 2^39 := by
  have h := integerVector_norm_sq numerator1 (2^101)
  change ‖pointVector1‖^2 = _ at h
  rw [norm1_checked] at h
  have hn := norm_nonneg pointVector1
  rw [abs_le]
  constructor <;> norm_num at * <;> nlinarith [norm_nonneg pointVector1]

theorem pointVector_inner_small : ‖inner ℂ pointVector0 pointVector1‖ ≤ (1 : ℝ) / 2^39 := by
  have h := pointGram_binding 0 1
  change inner ℂ pointVector0 pointVector1 = (pointGram 0 1 : ℂ) at h
  rw [h]
  norm_num [pointGram]

theorem pointVector0_projection_budget :
    ((1 : ℝ) / 2^47) * ‖pointVector0‖ / (11/2000) ≤ (1 : ℝ) / 2^39 := by
  have h := (abs_le.mp pointVector0_norm_near_one).2
  norm_num at *
  linarith

theorem pointVector1_projection_budget :
    ((1 : ℝ) / 2^47) * ‖pointVector1‖ / (11/2000) ≤ (1 : ℝ) / 2^39 := by
  have h := (abs_le.mp pointVector1_norm_near_one).2
  norm_num at *
  linarith

end
end Maxwell.Certificate.PointWitness
