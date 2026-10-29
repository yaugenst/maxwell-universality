import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Tactic.Module

/-!
# A real representative of a simple eigenline

Real matrix entries at a symmetry point allow the real or imaginary part of
an eigenvector to be selected and normalized. The resulting coordinate-real
vector has exactly the original rank-one projector, so analytic projection
formulas do not depend on the arbitrary complex phase of a spectral basis.
-/

namespace Maxwell.Spectral.RealEigenvector

noncomputable section
open InnerProductSpace
open scoped ComplexConjugate

variable {n : Type*} [Fintype n] [DecidableEq n]

def realPart (v : EuclideanSpace ℂ n) : EuclideanSpace ℂ n :=
  WithLp.toLp 2 fun i => ((v i).re : ℂ)

def imaginaryPart (v : EuclideanSpace ℂ n) : EuclideanSpace ℂ n :=
  WithLp.toLp 2 fun i => ((v i).im : ℂ)

/-- The real coordinate part remains an eigenvector, possibly zero. -/
theorem realPart_eigenvector (M : Matrix n n ℂ) (E : ℝ)
    (hreal : ∀ i j, (M i j).im = 0) (v : EuclideanSpace ℂ n)
    (hv : M.toEuclideanLin v = (E : ℂ) • v) :
    M.toEuclideanLin (realPart v) = (E : ℂ) • realPart v := by
  ext i
  have hi := congrArg (fun x : EuclideanSpace ℂ n => (x i).re) hv
  change (M.mulVec (fun j => ((v j).re : ℂ)) i) = (E : ℂ) * ((v i).re : ℂ)
  apply Complex.ext
  · simpa [Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
      Complex.mul_re, hreal] using hi
  · simp [Matrix.mulVec, dotProduct, Complex.mul_im, hreal]

/-- The imaginary coordinate part also remains an eigenvector. -/
theorem imaginaryPart_eigenvector (M : Matrix n n ℂ) (E : ℝ)
    (hreal : ∀ i j, (M i j).im = 0) (v : EuclideanSpace ℂ n)
    (hv : M.toEuclideanLin v = (E : ℂ) • v) :
    M.toEuclideanLin (imaginaryPart v) = (E : ℂ) • imaginaryPart v := by
  ext i
  have hi := congrArg (fun x : EuclideanSpace ℂ n => (x i).im) hv
  change (M.mulVec (fun j => ((v j).im : ℂ)) i) = (E : ℂ) * ((v i).im : ℂ)
  apply Complex.ext
  · simpa [Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
      Complex.mul_re, Complex.mul_im, hreal] using hi
  · simp [Matrix.mulVec, dotProduct, Complex.mul_im, hreal]

/-- At least one real coordinate part of a nonzero eigenvector is nonzero. -/
theorem exists_nonzero_real_eigenvector (M : Matrix n n ℂ) (E : ℝ)
    (hreal : ∀ i j, (M i j).im = 0) (v : EuclideanSpace ℂ n) (hv0 : v ≠ 0)
    (hv : M.toEuclideanLin v = (E : ℂ) • v) :
    ∃ w : EuclideanSpace ℂ n, w ≠ 0 ∧ M.toEuclideanLin w = (E : ℂ) • w ∧
      ∀ i, (w i).im = 0 := by
  by_cases hr : realPart v = 0
  · have hi : imaginaryPart v ≠ 0 := by
      intro hi
      apply hv0
      ext i
      have hre := congrArg (fun x : EuclideanSpace ℂ n => (x i).re) hr
      have him := congrArg (fun x : EuclideanSpace ℂ n => (x i).re) hi
      apply Complex.ext
      · simpa [realPart] using hre
      · simpa [imaginaryPart] using him
    exact ⟨imaginaryPart v, hi, imaginaryPart_eigenvector M E hreal v hv,
      fun i => by simp [imaginaryPart]⟩
  · exact ⟨realPart v, hr, realPart_eigenvector M E hreal v hv,
      fun i => by simp [realPart]⟩

section Projector

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Unit vectors on one complex line determine the same orthogonal rank-one
projector; this discharges the otherwise arbitrary spectral-basis phase. -/
theorem rankOne_eq_of_normalized_span (v φ : H) (hv : ‖v‖ = 1) (hφ : ‖φ‖ = 1)
    (hspan : ∃ c : ℂ, φ = c • v) : rankOne ℂ φ φ = rankOne ℂ v v := by
  obtain ⟨c, rfl⟩ := hspan
  have hc : ‖c‖ = 1 := by simpa only [norm_smul, hv, mul_one] using hφ
  have hp : conj c * c = 1 := by rw [Complex.conj_mul', hc]; norm_num
  ext x
  simp only [rankOne_apply, inner_smul_left, smul_smul]
  have he : (conj c * inner ℂ v x) * c = inner ℂ v x := by
    calc
      _ = inner ℂ v x * (conj c * c) := by ring
      _ = _ := by rw [hp, mul_one]
  rw [he]

end Projector

/-- A normalized eigenvector in a one-dimensional eigenspace of a real
matrix admits a coordinate-real normalized representative with the same
rank-one projector. No reality of the chosen spectral basis is assumed. -/
theorem exists_real_normalized_representative (M : Matrix n n ℂ) (E : ℝ)
    (hreal : ∀ i j, (M i j).im = 0) (v : EuclideanSpace ℂ n)
    (hvnorm : ‖v‖ = 1) (hv : M.toEuclideanLin v = (E : ℂ) • v)
    (hdim : Module.finrank ℂ (Module.End.eigenspace M.toEuclideanLin (E : ℂ)) = 1) :
    ∃ φ : EuclideanSpace ℂ n, ‖φ‖ = 1 ∧
      M.toEuclideanLin φ = (E : ℂ) • φ ∧ (∀ i, (φ i).im = 0) ∧
      (innerSL ℂ φ).smulRight φ = (innerSL ℂ v).smulRight v := by
  have hv0 : v ≠ 0 := by
    intro hz
    rw [hz, norm_zero] at hvnorm
    exact zero_ne_one hvnorm
  obtain ⟨w, hw0, hw, hwreal⟩ := exists_nonzero_real_eigenvector M E hreal v hv0 hv
  let φ : EuclideanSpace ℂ n := ((‖w‖⁻¹ : ℝ) : ℂ) • w
  have hφnorm : ‖φ‖ = 1 := by
    simp only [φ, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv,
      abs_of_nonneg (norm_nonneg w), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw0)]
  have hφ : M.toEuclideanLin φ = (E : ℂ) • φ := by
    calc
      M.toEuclideanLin φ = ((‖w‖⁻¹ : ℝ) : ℂ) • M.toEuclideanLin w :=
        M.toEuclideanLin.map_smul ((‖w‖⁻¹ : ℝ) : ℂ) w
      _ = (E : ℂ) • φ := by rw [hw]; dsimp [φ]; module
  have hφreal (i : n) : (φ i).im = 0 := by
    simp [φ, PiLp.smul_apply, Complex.mul_im, hwreal]
  have hspace := eq_span_singleton_of_mem_of_finrank_eq_one hdim
    (Module.End.mem_eigenspace_iff.mpr hv) hv0
  have hφmem : φ ∈ Submodule.span ℂ {v} := by
    rw [← hspace]
    exact Module.End.mem_eigenspace_iff.mpr hφ
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hφmem
  exact ⟨φ, hφnorm, hφ, hφreal,
    rankOne_eq_of_normalized_span v φ hvnorm hφnorm ⟨c, hc.symm⟩⟩

end
end Maxwell.Spectral.RealEigenvector
