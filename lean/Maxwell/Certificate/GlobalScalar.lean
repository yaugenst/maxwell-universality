import Maxwell.Spectral.BoxNeighborhood
import Maxwell.Certificate.GlobalScalarCore
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

namespace Maxwell.Certificate.GlobalScalar

open Maxwell.Spectral Maxwell.Spectral.BoxNeighborhood
noncomputable section

def Proposal.constants (p : Proposal) : Constants where
  half := fun _ => p.half
  P0 := 1023/1024
  s := p.s
  r := p.r
  rh := p.rh
  R := p.R
  σ := 1/2^24
  fn := fun i => p.fn i
  en := fun i => p.en i
  kn := fun i j => p.kn i j
  crossder := fun j => p.crossder j
  rhow := fun i j => p.rhow i j
  wn := p.wn
  wp2 := p.wp2
  qfn := p.qfn
  qw := p.qw
  rzero := p.rzero

theorem phaseScale_le : BoxSymbols.phaseScale ≤ (piUpper : ℝ)/10 := by
  have h := Real.pi_lt_d20
  norm_num [piUpper, BoxSymbols.phaseScale] at h ⊢
  linarith

theorem cube_radius_bound (half s : ℚ) (hh : 0 ≤ half)
    (hs : piUpper/10*(sqrtThreeUpper*half) ≤ s) :
    BoxSymbols.phaseScale*BoxSymbols.momentumNorm (fun _ => (half : ℝ)) ≤ (s : ℝ) := by
  have hh0 : 0 ≤ (half : ℝ) := Rat.cast_nonneg.mpr hh
  have hs3 : 3 ≤ (sqrtThreeUpper : ℝ)^2 := by norm_num [sqrtThreeUpper]
  have hr3 : 0 ≤ (sqrtThreeUpper : ℝ) := by norm_num [sqrtThreeUpper]
  have hn : BoxSymbols.momentumNorm (fun _ => (half : ℝ))^2 = 3*(half : ℝ)^2 := by
    rw [BoxSymbols.momentumNorm_sq]
    simp only [Fin.sum_univ_three]
    ring
  have hnorm : BoxSymbols.momentumNorm (fun _ => (half : ℝ)) ≤
      (sqrtThreeUpper : ℝ)*(half : ℝ) := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hr3 hh0)).mp
    change BoxSymbols.momentumNorm (fun _ => (half : ℝ))^2 ≤
      ((sqrtThreeUpper : ℝ)*(half : ℝ))^2
    rw [hn, mul_pow]
    exact mul_le_mul_of_nonneg_right hs3 (sq_nonneg _)
  have hp0 : 0 ≤ (piUpper : ℝ)/10 := by norm_num [piUpper]
  have h := mul_le_mul phaseScale_le hnorm (norm_nonneg _) hp0
  exact h.trans (by exact_mod_cast hs)


end
end Maxwell.Certificate.GlobalScalar
