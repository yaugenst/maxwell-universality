import Maxwell.Defect.BirmanSchwinger
import Maxwell.Defect.ScalarDefect

/-! Transfer of a certified finite compressed mode to the actual scalar
defect on the infinite complex Yee lattice. -/

namespace Maxwell.Defect
open Spectral Spectral.Lattice Module.End

noncomputable def unitOperatorEquiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (H : E →L[ℂ] E) (hH : IsUnit H) : E ≃ₗ[ℂ] E where
  toLinearMap := H.toLinearMap
  invFun x := (Ring.inverse H : E →L[ℂ] E) x
  left_inv x := by
    have h := congrArg (fun T : E →L[ℂ] E => T x) (Ring.inverse_mul_cancel H hH)
    exact h
  right_inv x := by
    have h := congrArg (fun T : E →L[ℂ] E => T x) (Ring.mul_inverse_cancel H hH)
    exact h

theorem physical_kernel_simple {U E : Type*}
    [NormedAddCommGroup U] [InnerProductSpace ℂ U] [CompleteSpace U]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (H : E →L[ℂ] E) (hH : IsUnit H) (K : U →L[ℂ] E) (μ : ℂ) (hμ : μ ≠ 0)
    (hsimple : Module.finrank ℂ (eigenspace (sourceCompression K (Ring.inverse H)).toLinearMap μ) = 1) :
    Module.finrank ℂ (LinearMap.ker (H - μ⁻¹ • K.comp K.adjoint).toLinearMap) = 1 := by
  exact birmanSchwinger_simple_kernel (unitOperatorEquiv H hH) K.toLinearMap
    K.adjoint.toLinearMap μ hμ hsimple

theorem physical_kernel_mode {U E : Type*}
    [NormedAddCommGroup U] [InnerProductSpace ℂ U] [CompleteSpace U]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (H : E →L[ℂ] E) (hH : IsUnit H) (K : U →L[ℂ] E) (μ : ℂ) (hμ : μ ≠ 0)
    (u : U) (hu : u ≠ 0) (heig : sourceCompression K (Ring.inverse H) u = μ • u) :
    Ring.inverse H (K u) ≠ 0 ∧
      (H - μ⁻¹ • K.comp K.adjoint) (Ring.inverse H (K u)) = 0 := by
  exact ⟨defect_mode_ne_zero (unitOperatorEquiv H hH) K.toLinearMap K.adjoint.toLinearMap hμ hu heig,
    defect_mode_of_compressed (unitOperatorEquiv H hH) K.toLinearMap K.adjoint.toLinearMap hμ heig⟩

/-- Simplicity is transferred to the actual complex eigenspace of the
electric operator obtained by changing the finite scalar cell set. -/
theorem scalarDefect_simple_mode (D : Finset Site) (m : Edge → ℝ) (K z μ : ℝ)
    (hK : 0 ≤ K) (hm : ∀ e, |m e| ≤ K) (hμ : μ ≠ 0)
    (hH : IsUnit (electricOperator m K hK hm - (z : ℂ) • 1))
    (u : EuclideanSpace ℂ (Fin (ScalarDefect.edges D).card)) (hu : u ≠ 0)
    (heig : sourceCompression (ScalarDefect.injection D)
      (Ring.inverse (electricOperator m K hK hm - (z : ℂ) • 1)) u = (μ : ℂ) • u)
    (hsimple : Module.finrank ℂ (eigenspace
      (sourceCompression (ScalarDefect.injection D)
        (Ring.inverse (electricOperator m K hK hm - (z : ℂ) • 1))).toLinearMap (μ : ℂ)) = 1) :
    let Hdef := ScalarDefect.perturbedOperator D m μ⁻¹ K hK hm
    ∃ y : Field, y ≠ 0 ∧ Hdef y = (z : ℂ) • y ∧
      Module.finrank ℂ (eigenspace Hdef.toLinearMap (z : ℂ)) = 1 := by
  dsimp only
  let H := electricOperator m K hK hm - (z : ℂ) • 1
  let Q := ScalarDefect.injection D
  have hμc : (μ : ℂ) ≠ 0 := by exact_mod_cast hμ
  have hoperator : ScalarDefect.perturbedOperator D m μ⁻¹ K hK hm - (z : ℂ) • 1 =
      H - (μ : ℂ)⁻¹ • Q.comp Q.adjoint := by
    rw [ScalarDefect.perturbedOperator_eq, Complex.ofReal_inv]
    dsimp [H, Q]
    abel
  obtain ⟨hyn, hye⟩ := physical_kernel_mode H hH Q μ hμc u hu heig
  refine ⟨Ring.inverse H (Q u), hyn, ?_, ?_⟩
  · have h := congrArg (fun T : Field →L[ℂ] Field => T (Ring.inverse H (Q u))) hoperator
    rw [hye] at h
    exact sub_eq_zero.mp h
  · rw [eigenspace_def]
    have hlin :
        (ScalarDefect.perturbedOperator D m μ⁻¹ K hK hm).toLinearMap - (z : ℂ) • 1 =
        (H - (μ : ℂ)⁻¹ • Q.comp Q.adjoint).toLinearMap :=
      congrArg ContinuousLinearMap.toLinearMap hoperator
    rw [hlin]
    exact physical_kernel_simple H hH Q μ hμc hsimple

end Maxwell.Defect
