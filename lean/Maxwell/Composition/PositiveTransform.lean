import Maxwell.Composition.PositiveGraph
import Maxwell.Composition.PositiveInverse
import Maxwell.Composition.Symmetrization

/-! End-to-end H-to-positive-graph algebra. The graph is computed from H;
source coordinates and every-output recovery are exact finite definitions. -/
noncomputable section
namespace Maxwell.Composition.PositiveEdges
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def fullEquiv (H : Matrix ι ι ℝ)
    (e : EuclideanSpace ℝ ι ≃L[ℝ] EuclideanSpace ℝ ι)
    (he : (e : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) =
      Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) H) :
    EuclideanSpace ℝ ((ι ⊕ ι) ⊕ Edge H) ≃L[ℝ] EuclideanSpace ℝ ((ι ⊕ ι) ⊕ Edge H) :=
  equiv H (Symmetrization.equiv e) (Symmetrization.equiv_coe H e he)

@[simp] theorem fullEquiv_coe (H : Matrix ι ι ℝ)
    (e : EuclideanSpace ℝ ι ≃L[ℝ] EuclideanSpace ℝ ι)
    (he : (e : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) =
      Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) H) :
    (fullEquiv H e he : EuclideanSpace ℝ ((ι ⊕ ι) ⊕ Edge H) →L[ℝ]
      EuclideanSpace ℝ ((ι ⊕ ι) ⊕ Edge H)) = operator H := rfl

theorem full_inverse_norm_le (H : Matrix ι ι ℝ)
    (e : EuclideanSpace ℝ ι ≃L[ℝ] EuclideanSpace ℝ ι)
    (he : (e : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) =
      Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) H)
    (halphabet : Alphabet H)
    (hr : ∀ i, (rowSupport H i).card ≤ 3)
    (hc : ∀ j, (columnSupport H j).card ≤ 3)
    (Q : ℝ) (hQ : 1 ≤ Q)
    (hInv : ‖(e.symm : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)‖ ≤ Q) :
    ‖((fullEquiv H e he).symm : EuclideanSpace ℝ ((ι ⊕ ι) ⊕ Edge H) →L[ℝ]
      EuclideanSpace ℝ ((ι ⊕ ι) ⊕ Edge H))‖ ≤ 16 * Q :=
  inverse_norm_le H (Symmetrization.equiv e) (Symmetrization.equiv_coe H e he)
    (alphabet_abs_le H halphabet) hr hc Q hQ ((Symmetrization.inverse_norm_le e).trans hInv)

def source (H : Matrix ι ι ℝ) :
    EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ((ι ⊕ ι) ⊕ Edge H) :=
  sumLeftInjection.comp sumLeftInjection

def readout (H : Matrix ι ι ℝ) :
    EuclideanSpace ℝ ((ι ⊕ ι) ⊕ Edge H) →L[ℝ] EuclideanSpace ℝ ι :=
  sumRightProjection.comp sumLeftProjection

omit [DecidableEq ι] in
theorem source_norm (H : Matrix ι ι ℝ) (g : EuclideanSpace ℝ ι) :
    ‖source H g‖ = ‖g‖ := by
  simp only [source, ContinuousLinearMap.comp_apply, sumLeftInjection_norm_apply]

omit [DecidableEq ι] in
theorem readout_coordinate (H : Matrix ι ι ℝ)
    (z : EuclideanSpace ℝ ((ι ⊕ ι) ⊕ Edge H)) (i : ι) :
    readout H z i = z (Sum.inl (Sum.inr i)) := rfl

/-- Every proposed solution of the concrete positive graph recovers H's
residual; no gate, symmetric, or mediator equation is assumed exact. -/
theorem full_residual_transfer (H : Matrix ι ι ℝ) (halphabet : Alphabet H)
    (hr : ∀ i, (rowSupport H i).card ≤ 3)
    (hc : ∀ j, (columnSupport H j).card ≤ 3)
    (z : EuclideanSpace ℝ ((ι ⊕ ι) ⊕ Edge H)) (g : EuclideanSpace ℝ ι) :
    ‖(Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) H) (readout H z) - g‖ ≤
      4 * ‖operator H z - source H g‖ :=
  (Symmetrization.residual_norm_le H (sumLeftProjection z) g).trans
    (residual_transfer H (alphabet_abs_le H halphabet) hr hc z (sumLeftInjection g))

end Maxwell.Composition.PositiveEdges
