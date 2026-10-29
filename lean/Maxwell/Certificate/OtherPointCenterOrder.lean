import Maxwell.Certificate.GenericPoint.Center
import Maxwell.Certificate.PointWitness.CorrectorConstruction

namespace Maxwell.Certificate.OtherPointCenterOrder

open PointWitness

/-- The three rounded centers lie above the selected actual eigenvalue by
the stated margin after both residual uncertainties are charged. -/
theorem energy_gt_selected (D : GenericPoint.Data)
    (hcenter : D.center 0=(11563656196705843248309 : ℝ)/2^80 ∨
      D.center 0=(11563712826362221562926 : ℝ)/2^80 ∨
      D.center 0=(11563663360579395381976 : ℝ)/2^80)
    (hradius : D.residualRadius≤(1 : ℝ)/2^44) :
    pointEnergy+(33 : ℝ)/10^9<D.energy := by
  have hs := (abs_le.mp pointEnergy_close).2
  have hd := D.energy_bounds.1
  have hc : pointCenter0+(1 : ℝ)/2^47+33/10^9<D.center 0-(1 : ℝ)/2^44 := by
    rcases hcenter with hc|hc|hc <;>
      rw [hc] <;> norm_num [pointCenter0,lambdaNumerator0]
  linarith

/-- This is only a scalar comparison with the rounded centers; it needs
neither a complementary spectral gap nor acceptance of another point's data. -/
theorem center_distance_lt (D : GenericPoint.Data)
    (hcenter : D.center 0=(11563656196705843248309 : ℝ)/2^80 ∨
      D.center 0=(11563712826362221562926 : ℝ)/2^80 ∨
      D.center 0=(11563663360579395381976 : ℝ)/2^80) :
    |pointEnergy-D.center 0|<(11 : ℝ)/2000 := by
  obtain ⟨hslo,hshi⟩ := abs_le.mp pointEnergy_close
  have hc : pointCenter0-(11 : ℝ)/2000+(1 : ℝ)/2^47<D.center 0 ∧
      D.center 0<pointCenter0+(11 : ℝ)/2000-(1 : ℝ)/2^47 := by
    rcases hcenter with hc|hc|hc <;>
      rw [hc] <;> norm_num [pointCenter0,lambdaNumerator0]
  apply abs_lt.mpr
  constructor <;> linarith [hc.1,hc.2]

end Maxwell.Certificate.OtherPointCenterOrder
