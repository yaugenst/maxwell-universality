import Maxwell.Continuum.CalibrationSupercellIndex
import Maxwell.Continuum.CellFourierUnitary

/-! The complete supercell Fourier space is unitarily regrouped into
its finite Bloch grid, retaining every alias and polarization. -/

noncomputable section

namespace Maxwell.Continuum.Calibration.Supercell

open FreeFiber

variable (M : ℕ) [NeZero M]

abbrev BlockSpace := PiLp 2 (fun _ : Grid M => FiberSpace)

theorem square_summable (u : FiberSpace) : Summable (fun ν => ‖u ν‖^2) := by
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
    u.property.summable (by norm_num : 0<(2 : ENNReal).toReal)

theorem square_norm (u : FiberSpace) : ‖u‖^2=∑' ν, ‖u ν‖^2 := by
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
    lp.norm_rpow_eq_tsum (by norm_num : 0<(2 : ENNReal).toReal) u

theorem regrouped_summable (u : FiberSpace) : Summable (fun p : Grid M × Alias => ‖u (join M p)‖^2) :=
  (indexEquiv M).summable_iff.mpr (square_summable u)

def fiber (u : FiberSpace) (j : Grid M) : FiberSpace :=
  ⟨fun ν => u (join M (j,ν)),by
    apply memℓp_gen
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using (regrouped_summable M u).prod_factor j⟩

def regroup (u : FiberSpace) : BlockSpace M := WithLp.toLp 2 (fun j => fiber M u j)

theorem regroup_norm (u : FiberSpace) : ‖regroup M u‖=‖u‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [PiLp.norm_sq_eq_of_L2]
  change (∑ j : Grid M, ‖fiber M u j‖^2)=‖u‖^2
  simp only [square_norm]
  change (∑ j : Grid M, ∑' ν, ‖u (join M (j,ν))‖^2)=∑' ν, ‖u ν‖^2
  calc
    _ = ∑' j : Grid M, ∑' ν, ‖u (join M (j,ν))‖^2 := (tsum_fintype _).symm
    _ = ∑' p : Grid M × Alias, ‖u (join M p)‖^2 := (regrouped_summable M u).tsum_prod.symm
    _ = _ := (indexEquiv M).tsum_eq (fun ν => ‖u ν‖^2)

def regroupLinear : FiberSpace →ₗ[ℂ] BlockSpace M where
  toFun := regroup M
  map_add' u v := by
    apply PiLp.ext
    intro j
    apply lp.ext
    rfl
  map_smul' c u := by
    apply PiLp.ext
    intro j
    apply lp.ext
    rfl

def regroupIsometry : FiberSpace →ₗᵢ[ℂ] BlockSpace M where
  toLinearMap := regroupLinear M
  norm_map' := regroup_norm M

theorem block_summable (u : BlockSpace M) :
    Summable (fun p : Grid M × Alias => ‖u p.1 p.2‖^2) := by
  apply (summable_prod_of_nonneg (fun _ => sq_nonneg _)).mpr
  exact ⟨fun j => square_summable (u j),hasSum_fintype _ |>.summable⟩

def assemble (u : BlockSpace M) : FiberSpace :=
  ⟨fun n => u ((indexEquiv M).symm n).1 ((indexEquiv M).symm n).2,by
    apply memℓp_gen
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two,Function.comp_def] using
      (indexEquiv M).symm.summable_iff.mpr (block_summable M u)⟩

theorem regroup_assemble (u : BlockSpace M) : regroup M (assemble M u)=u := by
  apply PiLp.ext
  intro j
  apply lp.ext
  funext ν
  change u ((indexEquiv M).symm ((indexEquiv M) (j,ν))).1
    ((indexEquiv M).symm ((indexEquiv M) (j,ν))).2=u j ν
  rw [Equiv.symm_apply_apply]

def unitary : FiberSpace ≃ₗᵢ[ℂ] BlockSpace M :=
  LinearIsometryEquiv.ofSurjective (regroupIsometry M) (fun u => ⟨assemble M u,regroup_assemble M u⟩)

theorem unitary_apply (u : FiberSpace) (j : Grid M) (ν : Alias) :
    unitary M u j ν=u (join M (j,ν)) := rfl

theorem unitary_symm_apply (u : BlockSpace M) (j : Grid M) (ν : Alias) :
    (unitary M).symm u (join M (j,ν))=u j ν := by
  have h := (unitary M).apply_symm_apply u
  exact congrArg (fun v : BlockSpace M => v j ν) h

#print axioms unitary
#print axioms unitary_symm_apply

end Maxwell.Continuum.Calibration.Supercell
