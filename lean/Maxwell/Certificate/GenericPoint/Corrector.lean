import Maxwell.Certificate.GenericPoint.Center
import Maxwell.Certificate.GenericPoint.Parity
import Maxwell.Spectral.ClusterParity
import Maxwell.Spectral.JetTransfer

/-! The exact first-order corrector for arbitrary checked TRIM data and either
common inversion parity. Saved vectors enter only through finite norm/residual
bounds, with the energy and frame replacement losses retained explicitly. -/
namespace Maxwell.Certificate.GenericPoint.Data
open Maxwell.Spectral Maxwell.Spectral.PrimitiveYee
noncomputable section
variable (D : GenericPoint.Data)

def energyGap : ℝ := D.gap-D.residualRadius

theorem energyGap_pos : 0 < D.energyGap := sub_pos.mpr D.gap_gt

theorem energy_complement_gap (hgap : D.ComplementGap) (i : Index) (hi : i ∉ D.cluster) :
    D.energyGap ≤ |(operator_symmetric D.k).eigenvalues rfl i-D.energy| := by
  have hg := hgap i hi 0
  have ht := abs_sub_le ((operator_symmetric D.k).eigenvalues rfl i) D.energy (D.center 0)
  have he := D.energy_close
  unfold energyGap
  linarith

theorem energy_complement_ne (hgap : D.ComplementGap) (i : Index) (hi : i ∉ D.cluster) :
    (operator_symmetric D.k).eigenvalues rfl i ≠ D.energy := by
  intro heq
  have hg := D.energy_complement_gap hgap i hi
  rw [heq,sub_self,abs_zero] at hg
  exact (not_le_of_gt D.energyGap_pos) hg

def reducedInverse : Space →L[ℂ] Space :=
  ClusterInverse.reducedInverse D.eigenbasis ((operator_symmetric D.k).eigenvalues rfl)
    D.cluster D.energy

theorem reducedInverse_norm_le (hgap : D.ComplementGap) : ‖D.reducedInverse‖ ≤ D.energyGap⁻¹ :=
  ClusterInverse.reducedInverse_norm_le D.eigenbasis (operator D.k)
    ((operator_symmetric D.k).eigenvalues rfl)
    ((operator_symmetric D.k).eigenvectorBasis_apply_self_apply rfl)
    D.cluster D.energy D.energyGap D.energyGap_pos (D.energy_complement_gap hgap)

def taylorCoefficient (q : PeriodicYee.Momentum) (n : ℕ) : Space →L[ℂ] Space :=
  YeeTaylor.shiftedOperatorCoefficient Concrete.material (timeReversalMomentum D.k) q D.energy n

def firstOrderRhs (hgap : D.ComplementGap) (q : PeriodicYee.Momentum) :
    EuclideanSpace ℂ (Fin 2) →L[ℂ] Space :=
  (D.taylorCoefficient q 1).comp (D.exactIsometry hgap).toContinuousLinearMap

def corrector (hgap : D.ComplementGap) (q : PeriodicYee.Momentum) :
    EuclideanSpace ℂ (Fin 2) →L[ℂ] Space := D.reducedInverse.comp (D.firstOrderRhs hgap q)

theorem taylorCoefficient_first_norm (q : PeriodicYee.Momentum) :
    ‖D.taylorCoefficient q 1‖ ≤ (11/5:ℝ)*YeeTaylor.radius q := by
  have h := YeeTaylor.shiftedOperatorCoefficient_norm_le Concrete.material
    (timeReversalMomentum D.k) q D.energy 1 (by omega)
  have hc : taylorCoefficientMajorant 1 = (11/5:ℝ) := by norm_num [taylorCoefficientMajorant]
  simpa only [taylorCoefficient,hc,pow_one] using h

theorem firstOrderRhs_parity (hgap : D.ComplementGap) (σ : ℂ)
    (hv : ∀ j, D.inversion (D.vector j) = σ • D.vector j) (q : PeriodicYee.Momentum) :
    HasParity D.inversion (-σ) (D.firstOrderRhs hgap q) := by
  exact (D.exactIsometry_parity hgap σ hv).odd_comp (D.taylorCoefficient q)
    (YeeInversion.shiftedOperator_taylorParity D.k q D.energy) 0

theorem opposite_projection_zero (hgap : D.ComplementGap) (σ : ℂ) (hσ : σ=1 ∨ σ= -1)
    (hv : ∀ j, D.inversion (D.vector j) = σ • D.vector j)
    (x : Space) (hx : D.inversion x = (-σ) • x) : D.projection x=0 :=
  ClusterInverse.projection_zero_of_opposite_parity D.eigenbasis D.cluster D.inversion σ hσ
    (D.cluster_eigenbasis_parity hgap σ hv) x hx

theorem corrector_equation (hgap : D.ComplementGap) (σ : ℂ) (hσ : σ=1 ∨ σ= -1)
    (hv : ∀ j, D.inversion (D.vector j) = σ • D.vector j) (q : PeriodicYee.Momentum) :
    (D.taylorCoefficient q 0).comp (D.corrector hgap q) =
      (D.taylorCoefficient q 1).comp (D.exactIsometry hgap).toContinuousLinearMap := by
  change (YeeTaylor.shiftedOperatorCoefficient Concrete.material
    (timeReversalMomentum D.k) q D.energy 0).comp _ = _
  rw [D.shiftedOperator_eq_coefficient]
  apply ContinuousLinearMap.ext
  intro x
  have h := ClusterInverse.solve_complement D.eigenbasis (operator D.k)
    ((operator_symmetric D.k).eigenvalues rfl)
    ((operator_symmetric D.k).eigenvectorBasis_apply_self_apply rfl)
    D.cluster D.energy (D.energy_complement_ne hgap) (D.firstOrderRhs hgap q x)
    (D.opposite_projection_zero hgap σ hσ hv _ (D.firstOrderRhs_parity hgap σ hv q x))
  change D.continuousOperator (D.corrector hgap q x) -
    (D.energy:ℂ) • D.corrector hgap q x = D.firstOrderRhs hgap q x
  have he := LinearMap.congr_fun D.continuousOperator_toLinearMap (D.corrector hgap q x)
  change D.continuousOperator (D.corrector hgap q x) = operator D.k (D.corrector hgap q x) at he
  rw [he]
  exact h

theorem corrector_parity (hgap : D.ComplementGap) (σ : ℂ) (hσ : σ=1 ∨ σ= -1)
    (hv : ∀ j, D.inversion (D.vector j) = σ • D.vector j) (q : PeriodicYee.Momentum) :
    HasParity D.inversion (-σ) (D.corrector hgap q) := by
  intro x
  exact ClusterInverse.reducedInverse_opposite_parity D.eigenbasis (operator D.k)
    ((operator_symmetric D.k).eigenvalues rfl)
    ((operator_symmetric D.k).eigenvectorBasis_apply_self_apply rfl)
    D.cluster D.energy D.energyGap D.energyGap_pos (D.energy_complement_gap hgap)
    D.inversion σ hσ (D.cluster_eigenbasis_parity hgap σ hv) D.operator_commutes_inversion
    (D.firstOrderRhs hgap q x) (D.firstOrderRhs_parity hgap σ hv q x)

def savedCorrectorResidual (q : PeriodicYee.Momentum)
    (savedY : EuclideanSpace ℂ (Fin 2) →L[ℂ] Space) : EuclideanSpace ℂ (Fin 2) →L[ℂ] Space :=
  (D.shiftedOperator (D.center 0)).comp savedY-(D.taylorCoefficient q 1).comp D.referenceMap

theorem corrector_saved_error (hgap : D.ComplementGap) (σ : ℂ) (hσ : σ=1 ∨ σ= -1)
    (hv : ∀ j, D.inversion (D.vector j) = σ • D.vector j)
    (q : PeriodicYee.Momentum) (savedY : EuclideanSpace ℂ (Fin 2) →L[ℂ] Space)
    (hY : HasParity D.inversion (-σ) savedY) :
    ‖D.corrector hgap q-savedY‖ ≤
      ‖D.firstOrderRhs hgap q-(D.shiftedOperator D.energy).comp savedY‖/D.energyGap := by
  apply ClusterInverse.corrector_error_opNorm D.eigenbasis D.continuousOperator
    ((operator_symmetric D.k).eigenvalues rfl)
    ((operator_symmetric D.k).eigenvectorBasis_apply_self_apply rfl)
    D.cluster D.energy D.energyGap D.energyGap_pos (D.energy_complement_gap hgap)
    (D.firstOrderRhs hgap q) savedY
  intro x
  exact D.opposite_projection_zero hgap σ hσ hv _ (hY x)

theorem corrector_saved_error_reference (hgap : D.ComplementGap) (σ : ℂ) (hσ : σ=1 ∨ σ= -1)
    (hv : ∀ j, D.inversion (D.vector j) = σ • D.vector j)
    (q : PeriodicYee.Momentum) (savedY : EuclideanSpace ℂ (Fin 2) →L[ℂ] Space)
    (hY : HasParity D.inversion (-σ) savedY) :
    ‖D.corrector hgap q-savedY‖ ≤
      (‖D.savedCorrectorResidual q savedY‖+D.residualRadius*‖savedY‖+
        ‖D.taylorCoefficient q 1‖*(16*D.gramRadius))/D.energyGap := by
  apply (D.corrector_saved_error hgap σ hσ hv q savedY hY).trans
  apply div_le_div_of_nonneg_right _ D.energyGap_pos.le
  have ht := JetTransfer.corrector_residual_transport D.continuousOperator
    (D.taylorCoefficient q 1) (D.exactIsometry hgap).toContinuousLinearMap D.referenceMap savedY
    D.energy (D.center 0)
  have he : |D.center 0-D.energy| ≤ D.residualRadius := by
    simpa only [abs_sub_comm] using D.energy_close
  have hf : ‖D.referenceMap-(D.exactIsometry hgap).toContinuousLinearMap‖ ≤ 16*D.gramRadius := by
    simpa only [norm_sub_rev] using D.exactIsometry_close hgap
  change ‖D.firstOrderRhs hgap q-(D.shiftedOperator D.energy).comp savedY‖ ≤ _
  calc
    _ ≤ ‖D.savedCorrectorResidual q savedY‖+|D.center 0-D.energy| *‖savedY‖+
        ‖D.taylorCoefficient q 1‖*‖D.referenceMap-(D.exactIsometry hgap).toContinuousLinearMap‖ := by
      calc
        _ = ‖(D.shiftedOperator D.energy).comp savedY-D.firstOrderRhs hgap q‖ := norm_sub_rev _ _
        _ ≤ _ := ht
    _ ≤ _ := add_le_add
      (add_le_add le_rfl (mul_le_mul_of_nonneg_right he (norm_nonneg _)))
      (mul_le_mul_of_nonneg_left hf (norm_nonneg _))

/-- A finite scalar budget converts saved residual checks into the true
corrector error, without changing the exact spectral construction. -/
theorem corrector_error_of_saved_bounds (hgap : D.ComplementGap) (σ : ℂ) (hσ : σ=1 ∨ σ= -1)
    (hv : ∀ j, D.inversion (D.vector j) = σ • D.vector j)
    (q : PeriodicYee.Momentum) (savedY : EuclideanSpace ℂ (Fin 2) →L[ℂ] Space)
    (hY : HasParity D.inversion (-σ) savedY) (a b η : ℝ)
    (hnorm : ‖savedY‖ ≤ b*YeeTaylor.radius q)
    (hresidual : ‖D.savedCorrectorResidual q savedY‖ ≤ a*YeeTaylor.radius q)
    (hbudget : (a+D.residualRadius*b+(11/5)*(16*D.gramRadius))/D.energyGap ≤ η) :
    ‖D.corrector hgap q-savedY‖ ≤ η*YeeTaylor.radius q := by
  apply (D.corrector_saved_error_reference hgap σ hσ hv q savedY hY).trans
  have hb := (div_le_iff₀ D.energyGap_pos).mp hbudget
  apply (div_le_iff₀ D.energyGap_pos).mpr
  have hy := mul_le_mul_of_nonneg_left hnorm D.residual_nonneg
  have ha := mul_le_mul_of_nonneg_right (D.taylorCoefficient_first_norm q)
    (show 0 ≤ 16*D.gramRadius from mul_nonneg (by norm_num) D.gram_nonneg)
  have hbr := mul_le_mul_of_nonneg_right hb (YeeTaylor.radius_nonneg q)
  nlinarith only [hresidual,hy,ha,hbr]

theorem corrector_norm_of_saved_error (hgap : D.ComplementGap)
    (q : PeriodicYee.Momentum) (savedY : EuclideanSpace ℂ (Fin 2) →L[ℂ] Space) (b η : ℝ)
    (hnorm : ‖savedY‖ ≤ b*YeeTaylor.radius q)
    (herror : ‖D.corrector hgap q-savedY‖ ≤ η*YeeTaylor.radius q) :
    ‖D.corrector hgap q‖ ≤ (b+η)*YeeTaylor.radius q := by
  have ht := norm_le_norm_sub_add (D.corrector hgap q) savedY
  nlinarith only [ht,hnorm,herror]

end
end Maxwell.Certificate.GenericPoint.Data
