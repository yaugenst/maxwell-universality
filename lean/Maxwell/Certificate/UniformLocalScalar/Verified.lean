import Maxwell.Certificate.UniformLocalScalar.Data
import Maxwell.Certificate.UniformLocalScalarSound
import Maxwell.Spectral.YeeTaylor

namespace Maxwell.Certificate.UniformLocalScalar.Frozen
open Maxwell.Spectral
noncomputable section

def constants : BoxNeighborhoodGeneral.Constants :=
  UniformLocalScalar.constants proposal0000

theorem accepted : BoxNeighborhoodGeneral.Accepted constants :=
  accepts_sound proposal0000 evidence0000 checked0000

theorem rho_eq : constants.rho = 14 := rfl
theorem sigma_eq : constants.σ = 1/4096 := rfl

theorem half_ge (j : Fin 3) : (1/20 : ℝ) ≤ constants.half j := by
  norm_num [constants, UniformLocalScalar.constants, proposal0000]

theorem ball_subset_box (q : PeriodicYee.Momentum) (hq : YeeTaylor.radius q ≤ 1/20)
    (j : Fin 3) : |q j| ≤ constants.half j := by
  have h := PiLp.norm_apply_le (WithLp.toLp 2 q) j
  change ‖q j‖ ≤ YeeTaylor.radius q at h
  rw [Real.norm_eq_abs] at h
  exact h.trans (hq.trans (half_ge j))

theorem cutoff_le : (proposal0000.cutoff : ℝ) ≤ constants.R^2 :=
  accepts_cutoff_le_real proposal0000 evidence0000 checked0000

end
end Maxwell.Certificate.UniformLocalScalar.Frozen
