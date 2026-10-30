import Maxwell.Continuum.FiniteAuxiliaryCommonShift

/-! Common lattice translation preserves the literal ideal physical
observable response, including the translated sparse source. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.FiniteAuxiliary

open Auxiliary EffectiveMass Bloch CellGauge

variable {ι : Type*} [Fintype ι]

theorem idealResponse_common_lattice_shift {h z σ : ℝ} (D : Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4/64)
    (r : ι → Space) (v : ι → ℝ) (a : Alias)
    (A : DefectSpace ι ≃L[ℂ] DefectSpace ι) (α : ℝ) (g : BrightSpace ι) :
    idealReadout h (fun i => r i+latticeShift a) v (realMode D hh)
      (auxiliaryField D hσ0 hσ (fun i => r i+latticeShift a) A
        (idealSource D hh (fun i => r i+latticeShift a) α g)) =
      idealReadout h r v (realMode D hh)
        (auxiliaryField D hσ0 hσ r A (idealSource D hh r α g)) := by
  rw [idealSource_shift, auxiliaryField_common_lattice_shift, idealReadout_shift]

theorem brightResponse_common_lattice_shift {h z σ : ℝ} (D : Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4/64)
    (r : ι → Space) (a : Alias) (A : DefectSpace ι ≃L[ℂ] DefectSpace ι)
    (α : ℝ) (g : BrightSpace ι) :
    brightResponse D hh hσ0 hσ (fun i => r i+latticeShift a) A
      (idealSource D hh (fun i => r i+latticeShift a) α g) =
      brightResponse D hh hσ0 hσ r A (idealSource D hh r α g) := by
  rw [idealSource_shift, brightResponse, brightResponse, defectResponse_common_lattice_shift]

#print axioms idealResponse_common_lattice_shift
#print axioms brightResponse_common_lattice_shift

end Maxwell.Continuum.FiniteAuxiliary
