import Maxwell.Continuum.BoxModes
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-! Smoothness of the literal electric and magnetic sine/cosine modes. -/

noncomputable section
namespace Maxwell.Continuum.BoxModes
open scoped ContDiff

theorem contDiff_electric (p a : Vector) : ContDiff ℝ ∞ (electric p a) := by
  have hs (j : Fin 3) : ContDiff ℝ ∞ (fun x : Point => Real.sin (p j * x j)) :=
    ((contDiff_const : ContDiff ℝ ∞ (fun _ : Point => p j)).mul (PiLp.proj 2 (fun _ : Fin 3 => ℝ) j : Point →L[ℝ] ℝ).contDiff).sin
  have hc (j : Fin 3) : ContDiff ℝ ∞ (fun x : Point => Real.cos (p j * x j)) :=
    ((contDiff_const : ContDiff ℝ ∞ (fun _ : Point => p j)).mul (PiLp.proj 2 (fun _ : Fin 3 => ℝ) j : Point →L[ℝ] ℝ).contDiff).cos
  apply contDiff_pi.mpr
  intro j
  fin_cases j
  · exact (((contDiff_const : ContDiff ℝ ∞ (fun _ : Point => a 0)).mul (hc 0)).mul (hs 1)).mul (hs 2)
  · exact (((contDiff_const : ContDiff ℝ ∞ (fun _ : Point => a 1)).mul (hs 0)).mul (hc 1)).mul (hs 2)
  · exact (((contDiff_const : ContDiff ℝ ∞ (fun _ : Point => a 2)).mul (hs 0)).mul (hs 1)).mul (hc 2)


theorem contDiff_magnetic (p b : Vector) : ContDiff ℝ ∞ (magnetic p b) := by
  have hs (j : Fin 3) : ContDiff ℝ ∞ (fun x : Point => Real.sin (p j * x j)) :=
    ((contDiff_const : ContDiff ℝ ∞ (fun _ : Point => p j)).mul (PiLp.proj 2 (fun _ : Fin 3 => ℝ) j : Point →L[ℝ] ℝ).contDiff).sin
  have hc (j : Fin 3) : ContDiff ℝ ∞ (fun x : Point => Real.cos (p j * x j)) :=
    ((contDiff_const : ContDiff ℝ ∞ (fun _ : Point => p j)).mul (PiLp.proj 2 (fun _ : Fin 3 => ℝ) j : Point →L[ℝ] ℝ).contDiff).cos
  apply contDiff_pi.mpr
  intro j
  fin_cases j
  · exact (((contDiff_const : ContDiff ℝ ∞ (fun _ : Point => b 0)).mul (hs 0)).mul (hc 1)).mul (hc 2)
  · exact (((contDiff_const : ContDiff ℝ ∞ (fun _ : Point => b 1)).mul (hc 0)).mul (hs 1)).mul (hc 2)
  · exact (((contDiff_const : ContDiff ℝ ∞ (fun _ : Point => b 2)).mul (hc 0)).mul (hc 1)).mul (hs 2)

#print axioms contDiff_electric
#print axioms contDiff_magnetic
end Maxwell.Continuum.BoxModes
