import Maxwell.Defect.CompressedNumerator
import Mathlib.Analysis.Complex.Basic

/-! Scalar readout of the actual analytic source-compressed projector.
Both source profiles vary holomorphically; the center coefficient is the
square of their actual overlap with the edge eigenvector. -/

noncomputable section

namespace Maxwell.Green

open Filter InnerProductSpace
open scoped Topology ComplexConjugate

variable {U H W : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℂ U] [CompleteSpace U]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

def scalarOperatorReadout (u : U) : (U →L[ℂ] U) →L[ℂ] ℂ :=
  (innerSL ℂ u).comp (ContinuousLinearMap.apply ℂ U u)

omit [CompleteSpace U] in
@[simp] theorem scalarOperatorReadout_apply (u : U) (T : U →L[ℂ] U) :
    scalarOperatorReadout u T = inner ℂ u (T u) := rfl

omit [CompleteSpace U] in
theorem scalarOperatorReadout_rankOne (u a : U) :
    scalarOperatorReadout u (rankOne ℂ a a) = (‖inner ℂ a u‖ ^ 2 : ℝ) := by
  rw [scalarOperatorReadout_apply, rankOne_apply, inner_smul_right,
    ← inner_conj_symm u a, Complex.mul_conj']
  norm_cast

def scalarCompressedNumerator
    (sourceLeft : W → H →L[ℂ] U) (P : W → H →L[ℂ] H)
    (sourceRight : W → U →L[ℂ] H) (u : U) (q : W) : ℂ :=
  scalarOperatorReadout u (Defect.compressedNumerator sourceLeft P sourceRight q)

omit [CompleteSpace U] [CompleteSpace H] in
theorem scalarCompressedNumerator_analyticAt
    (sourceLeft : W → H →L[ℂ] U) (P : W → H →L[ℂ] H)
    (sourceRight : W → U →L[ℂ] H) (u : U) (q : W)
    (hL : AnalyticAt ℂ sourceLeft q) (hP : AnalyticAt ℂ P q)
    (hR : AnalyticAt ℂ sourceRight q) :
    AnalyticAt ℂ (scalarCompressedNumerator sourceLeft P sourceRight u) q :=
  ((scalarOperatorReadout u).analyticAt _).comp
    (Defect.compressedNumerator_analyticAt sourceLeft P sourceRight q hL hP hR)

omit [NormedAddCommGroup W] [NormedSpace ℂ W] in
theorem scalarCompressedNumerator_center
    (sourceLeft : W → H →L[ℂ] U) (P : W → H →L[ℂ] H)
    (sourceRight : W → U →L[ℂ] H) (u : U) (q : W) (F : U →L[ℂ] H) (φ : H)
    (hL : sourceLeft q = ContinuousLinearMap.adjoint F)
    (hP : P q = rankOne ℂ φ φ) (hR : sourceRight q = F) :
    scalarCompressedNumerator sourceLeft P sourceRight u q =
      (‖inner ℂ φ (F u)‖ ^ 2 : ℝ) := by
  unfold scalarCompressedNumerator
  rw [Defect.compressedNumerator_center sourceLeft P sourceRight q F φ hL hP hR,
    scalarOperatorReadout_rankOne, ContinuousLinearMap.adjoint_inner_left]

/-- Nonzero physical source overlap makes the scalar residue numerator
stay nonzero throughout an actual complex neighborhood of the edge. -/
theorem scalarCompressedNumerator_positive_near_center
    (sourceLeft : W → H →L[ℂ] U) (P : W → H →L[ℂ] H)
    (sourceRight : W → U →L[ℂ] H) (u : U) (q : W) (F : U →L[ℂ] H) (φ : H)
    (hLa : AnalyticAt ℂ sourceLeft q) (hPa : AnalyticAt ℂ P q)
    (hRa : AnalyticAt ℂ sourceRight q)
    (hL : sourceLeft q = ContinuousLinearMap.adjoint F)
    (hP : P q = rankOne ℂ φ φ) (hR : sourceRight q = F)
    (hoverlap : inner ℂ φ (F u) ≠ 0) :
    ∀ᶠ z in 𝓝 q,
      ‖inner ℂ φ (F u)‖ ^ 2 / 2 <
        (scalarCompressedNumerator sourceLeft P sourceRight u z).re ∧
      scalarCompressedNumerator sourceLeft P sourceRight u z ≠ 0 := by
  have hp : 0 < ‖inner ℂ φ (F u)‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hoverlap)
  have hc := (scalarCompressedNumerator_analyticAt sourceLeft P sourceRight u q hLa hPa hRa).continuousAt
  have hcenter := scalarCompressedNumerator_center sourceLeft P sourceRight u q F φ hL hP hR
  have he : ∀ᶠ z in 𝓝 q, ‖inner ℂ φ (F u)‖ ^ 2 / 2 <
      (scalarCompressedNumerator sourceLeft P sourceRight u z).re :=
    (Complex.continuous_re.continuousAt.comp hc).eventually (lt_mem_nhds (by
      rw [Function.comp_apply, hcenter, Complex.ofReal_re]
      linarith))
  filter_upwards [he] with z hz
  refine ⟨hz, ?_⟩
  intro hn
  rw [hn, Complex.zero_re] at hz
  linarith

omit [CompleteSpace U] [CompleteSpace H] [NormedAddCommGroup W] [NormedSpace ℂ W] in
theorem scalarCompressedNumerator_pole_decomposition
    (sourceLeft : W → H →L[ℂ] U) (P regular inverse : W → H →L[ℂ] H)
    (sourceRight : W → U →L[ℂ] H) (u : U) (lam : W → ℂ) (z : ℂ) (q : W)
    (hpole : inverse q = (lam q - z)⁻¹ • P q + regular q) :
    scalarCompressedNumerator sourceLeft inverse sourceRight u q =
      scalarCompressedNumerator sourceLeft P sourceRight u q / (lam q - z) +
        scalarCompressedNumerator sourceLeft regular sourceRight u q := by
  unfold scalarCompressedNumerator
  rw [Defect.compressedNumerator_pole_decomposition sourceLeft P regular inverse sourceRight lam z q hpole,
    map_add, map_smul]
  simp only [smul_eq_mul, div_eq_mul_inv, mul_comm]

end Maxwell.Green
