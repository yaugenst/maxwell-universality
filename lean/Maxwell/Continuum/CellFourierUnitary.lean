import Maxwell.Continuum.CellBandFourierL2

/-! The complete cell Fourier unitary for arbitrary square-summable
polarization coefficients. No absolute summability hypothesis is needed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.CellFourier

open FreeFiber CellBandFourier UnitAddTorus MeasureTheory

def synthesis (u : FiberSpace) : CellFieldL2 :=
  WithLp.toLp 2 (fun j => mFourierBasis.repr.symm (componentSequence u j))

theorem componentSequence_add (u v : FiberSpace) (j : Fin 3) :
    componentSequence (u + v) j = componentSequence u j + componentSequence v j := by
  apply lp.ext
  rfl

theorem componentSequence_smul (c : ℂ) (u : FiberSpace) (j : Fin 3) :
    componentSequence (c • u) j = c • componentSequence u j := by
  apply lp.ext
  rfl

def synthesisLinear : FiberSpace →ₗ[ℂ] CellFieldL2 where
  toFun := synthesis
  map_add' u v := by
    apply PiLp.ext
    intro j
    change mFourierBasis.repr.symm (componentSequence (u + v) j) = _
    rw [componentSequence_add, map_add]
    rfl
  map_smul' c u := by
    apply PiLp.ext
    intro j
    change mFourierBasis.repr.symm (componentSequence (c • u) j) = _
    rw [componentSequence_smul, map_smul]
    rfl

theorem synthesis_component_norm_sq (u : FiberSpace) (j : Fin 3) :
    ‖synthesis u j‖^2 = ∑' ν, ‖u ν j‖^2 := by
  change ‖mFourierBasis.repr.symm (componentSequence u j)‖^2 = _
  rw [LinearIsometryEquiv.norm_map]
  have h := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ENNReal).toReal) (componentSequence u j)
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, componentSequence] using h

theorem synthesis_norm (u : FiberSpace) : ‖synthesis u‖ = ‖u‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [PiLp.norm_sq_eq_of_L2]
  change (∑ j : Fin 3, ‖synthesis u j‖^2) = _
  simp only [synthesis_component_norm_sq]
  rw [← Summable.tsum_finsetSum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 3))) =>
    Bloch.polarization_component_summable u j)]
  simp only [← EuclideanSpace.norm_sq_eq]
  have h := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ENNReal).toReal) u
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h.symm

def synthesisIsometry : FiberSpace →ₗᵢ[ℂ] CellFieldL2 where
  toLinearMap := synthesisLinear
  norm_map' := synthesis_norm

def analysisValue (f : CellFieldL2) (ν : Alias) : Polarization :=
  WithLp.toLp 2 (fun j => mFourierBasis.repr (f j) ν)

theorem analysisValue_memℓp (f : CellFieldL2) : Memℓp (analysisValue f) 2 := by
  apply memℓp_gen
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, analysisValue, EuclideanSpace.norm_sq_eq]
  apply summable_sum
  intro j _
  have h := (memℓp_gen_iff (by norm_num : 0 < (2 : ENNReal).toReal)).mp
    (mFourierBasis.repr (f j)).property
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h

def analysis (f : CellFieldL2) : FiberSpace := ⟨analysisValue f, analysisValue_memℓp f⟩

theorem analysis_componentSequence (f : CellFieldL2) (j : Fin 3) :
    componentSequence (analysis f) j = mFourierBasis.repr (f j) := by
  apply lp.ext
  rfl

theorem synthesis_analysis (f : CellFieldL2) : synthesis (analysis f) = f := by
  apply PiLp.ext
  intro j
  change mFourierBasis.repr.symm (componentSequence (analysis f) j) = f j
  rw [analysis_componentSequence, LinearIsometryEquiv.symm_apply_apply]

def unitary : FiberSpace ≃ₗᵢ[ℂ] CellFieldL2 :=
  LinearIsometryEquiv.ofSurjective synthesisIsometry (fun f => ⟨analysis f, synthesis_analysis f⟩)

theorem unitary_apply (u : FiberSpace) : unitary u = synthesis u := rfl

theorem unitary_symm_apply (f : CellFieldL2) : unitary.symm f = analysis f := by
  apply unitary.injective
  rw [LinearIsometryEquiv.apply_symm_apply, unitary_apply, synthesis_analysis]

theorem unitary_eq_cellL2 (u : FiberSpace) (hu : Summable (fun ν => ‖u ν‖)) :
    unitary u = cellL2 u := by
  apply PiLp.ext
  intro j
  exact (scalarCellL2_eq_fourier u hu j).symm

#print axioms synthesis_analysis
#print axioms unitary_eq_cellL2

end Maxwell.Continuum.CellFourier
