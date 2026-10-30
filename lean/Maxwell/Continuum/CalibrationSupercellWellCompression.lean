import Maxwell.Continuum.CalibrationSupercellCompression
import Maxwell.Continuum.CalibrationPeriodizedAuxiliary

/-! Exact physical supercell compression on the actual well cells.
The selected torus size proves all cell inclusion and image-separation
conditions needed for the periodization estimate. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace Maxwell.Continuum.Calibration.Supercell

open FreeFiber CellGauge CellBandFourier PeriodicSampling Auxiliary Bloch MasterConstants EffectiveMass

variable (M : ℕ) [NeZero M]

attribute [local irreducible] physicalOperator actualGridInverse Qh periodizedCompression

theorem twoWellCells_representative {L : ℝ} (hL : 1≤L) (k : Bloch.Alias)
    (hM : 16*(L+(imageRadius k : ℝ)+1)≤(M : ℝ))
    {a : Bloch.Alias} (ha : a∈twoWellCells L k) :
    representative M (Product.frequency M a)=a := by
  apply representative_frequency
  intro i
  have hb := abs_le.mp (twoWellCells_coordinate_bound (zero_le_one.trans hL) k ha i)
  have hk : (0 : ℝ) ≤ imageRadius k := Nat.cast_nonneg _
  have hlo : -(M : ℝ)<2*(a i : ℝ) := by linarith only [hM,hL,hb.1,hk]
  have hhi : 2*(a i : ℝ)≤(M : ℝ) := by linarith only [hM,hL,hb.2,hk]
  exact ⟨by exact_mod_cast hlo,by exact_mod_cast hhi⟩

theorem physicalOperator_twoWell_compression {L z σ : ℝ} (hL : Ls≤L)
    (D : Auxiliary.Calibration L⁻¹ z) (hσ0 : 0≤σ) (hσ : σ≤(L⁻¹)^4/64)
    (hEven : Even M) (k : Bloch.Alias)
    (hM : 16*(L+(imageRadius k : ℝ)+1)≤(M : ℝ)) :
    (familyProjection (twoWellCells L k)).comp
      ((physicalOperator M (fun j => actualGridInverse z σ (fun i => centeredGrid M (j i)))).comp
        (familyProjection (twoWellCells L k)))=
      periodizedCompression D hσ0 hσ M (twoWellCells L k) (twoWellCells L k) := by
  have hL1 := length_ge_one hL
  have hM0 : L≤(M : ℝ) := by nlinarith [show (0 : ℝ) ≤ imageRadius k from Nat.cast_nonneg _]
  exact physicalOperator_compression M hL D hσ0 hσ hM0 hEven _ _
    (fun _ ha => twoWellCells_representative M hL1 k hM ha)
    (fun _ hb => twoWellCells_representative M hL1 k hM hb)
    (fun _ ha _ hb j hj => twoWellCells_image_distance hL1 k M hM ha hb j hj)

def physicalAuxiliary {L z : ℝ} (_D : Auxiliary.Calibration L⁻¹ z) : FieldL2 →L[ℂ] FieldL2 :=
  Qh L⁻¹*physicalOperator M (fun j => actualGridInverse z 0 (fun i => centeredGrid M (j i)))*Qh L⁻¹

theorem physicalAuxiliary_eq_periodized {L z : ℝ} (hL : Ls≤L)
    (D : Auxiliary.Calibration L⁻¹ z) (hEven : Even M)
    (hM : 16*(L+1)≤(M : ℝ)) : physicalAuxiliary M D=periodizedAuxiliary D M := by
  have hc := physicalOperator_twoWell_compression M hL D le_rfl (by positivity) hEven (0 : Bloch.Alias)
    (by simpa only [imageRadius_zero,Nat.cast_zero,add_zero] using hM)
  rw [twoWellCells_zero] at hc
  apply ContinuousLinearMap.ext
  intro f
  have hi := congrArg (fun T : FieldL2 →L[ℂ] FieldL2 => T f) (familyProjection_Qh (length_pos hL))
  change familyProjection (ballCells L) (Qh L⁻¹ f)=Qh L⁻¹ f at hi
  have ho (g : FieldL2) : Qh L⁻¹ (familyProjection (ballCells L) g)=Qh L⁻¹ g :=
    congrArg (fun T : FieldL2 →L[ℂ] FieldL2 => T g) (Qh_familyProjection (length_pos hL))
  have he := congrArg (fun T : FieldL2 →L[ℂ] FieldL2 => Qh L⁻¹ (T (Qh L⁻¹ f))) hc
  simp only [ContinuousLinearMap.comp_apply,hi] at he
  rw [ho] at he
  exact he

theorem physicalAuxiliary_requested_error {L z : ℝ} (hL : Ls≤L)
    (D : Auxiliary.Calibration L⁻¹ z) (hEven : Even M) (N ell : ℕ)
    (hM : 16*(L+1)≤(M : ℝ)) (hlog : L≤(2 : ℝ)^ell)
    (hsize : Cs^4*L*((N : ℝ)+(ell : ℝ)+2)^2≤(M : ℝ)) :
    ‖physicalAuxiliary M D-Sh D‖≤(1/2 : ℝ)^(N+20) := by
  rw [physicalAuxiliary_eq_periodized M hL D hEven hM]
  exact periodizedAuxiliary_requested_error hL D M N ell hM hlog hsize

#print axioms physicalAuxiliary_eq_periodized
#print axioms physicalAuxiliary_requested_error

end Maxwell.Continuum.Calibration.Supercell
