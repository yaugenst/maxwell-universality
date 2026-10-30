import Maxwell.Continuum.BoxModesSpectrum
import Maxwell.Continuum.HilbertCoefficientEnergy
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! The transverse spectral gap of the literal unit PEC cube. The full
infinite-dimensional curl-free kernel is kept separate. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace Maxwell.Continuum.VacuumBox

open BoxModes

def lengths : Fin 3 → ℝ := fun _ => 1

def domain := boxDomain lengths

theorem lengths_pos (j : Fin 3) : 0 < lengths j := by norm_num [lengths]

private theorem positive_mode_square (n : ℤ) (hn : 0 < n) :
    Real.pi^2 ≤ ((n : ℝ)*Real.pi)^2 := by
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hmul : Real.pi ≤ (n : ℝ)*Real.pi := by nlinarith [Real.pi_pos]
  exact sq_le_sq₀ Real.pi_pos.le (Real.pi_pos.le.trans hmul) |>.mpr hmul

theorem mode_gap (q : ComponentModeIndex) :
    2*Real.pi^2 ≤ modeEigenvalue lengths q.2.val := by
  obtain ⟨c,ν,hν⟩ := q
  change 2*Real.pi^2 ≤ modeEigenvalue lengths ν
  simp only [modeEigenvalue,integerWaveNumber,lengths,div_one,Fin.sum_univ_three]
  fin_cases c
  · have h1 := positive_mode_square (ν 1) (hν.2 1 (by decide))
    have h2 := positive_mode_square (ν 2) (hν.2 2 (by decide))
    nlinarith only [h1,h2,sq_nonneg ((ν 0 : ℝ)*Real.pi)]
  · have h0 := positive_mode_square (ν 0) (hν.2 0 (by decide))
    have h2 := positive_mode_square (ν 2) (hν.2 2 (by decide))
    nlinarith only [h0,h2,sq_nonneg ((ν 1 : ℝ)*Real.pi)]
  · have h0 := positive_mode_square (ν 0) (hν.2 0 (by decide))
    have h1 := positive_mode_square (ν 1) (hν.2 1 (by decide))
    nlinarith only [h0,h1,sq_nonneg ((ν 2 : ℝ)*Real.pi)]

theorem transverse_energy (u : (transverseCurlCurl domain).domain) :
    2*Real.pi^2*‖(u : transverseSpace domain)‖^2 ≤
      (inner ℂ (u : transverseSpace domain) (transverseCurlCurl domain u)).re :=
  HilbertCoefficientEnergy.energy_lower (componentHilbertBasis lengths lengths_pos)
    ((u : transverseSpace domain) : testL2Closure domain)
    (transverseCurlCurl domain u : testL2Closure domain)
    (fun q => modeEigenvalue lengths q.2.val) (2*Real.pi^2)
    (transverseCurlCurl_coefficient lengths lengths_pos u) (fun q _ => mode_gap q)

theorem transverse_shift_energy (u : (transverseCurlCurl domain).domain) :
    ‖(u : transverseSpace domain)‖^2 ≤
      (inner ℂ (u : transverseSpace domain)
        (transverseCurlCurl domain u-(u : transverseSpace domain))).re := by
  have he := transverse_energy u
  have hp : 2 ≤ 2*Real.pi^2 := by nlinarith [Real.pi_gt_three]
  have hp' := mul_le_mul_of_nonneg_right hp (sq_nonneg ‖(u : transverseSpace domain)‖)
  have hi := inner_self_eq_norm_sq (𝕜 := ℂ) (u : transverseSpace domain)
  change (inner ℂ (u : transverseSpace domain) (u : transverseSpace domain)).re =
      ‖(u : transverseSpace domain)‖^2 at hi
  rw [inner_sub_right,Complex.sub_re,hi]
  linarith

#print axioms transverse_energy
#print axioms transverse_shift_energy

end Maxwell.Continuum.VacuumBox
