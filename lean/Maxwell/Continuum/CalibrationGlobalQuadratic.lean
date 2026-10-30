import Maxwell.Continuum.CalibrationGlobalNorm
import Maxwell.Continuum.CalibrationQuadraticMachine
import Maxwell.Continuum.CalibrationFiniteCoupling

/-! The exact matrices consumed by the quadratic machine produce the literal
finite eigenvalue and coupling centers used by the certified intervals. -/

namespace Maxwell.Continuum.Calibration.GlobalPower

open FreeFiber PeriodicSampling
open scoped BigOperators
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency true

theorem sample_pair (R : ℕ) (f g : RationalAliasField) :
    (∑ i : Fin (2*aliasArraySize R),sample R f i*sample R g i)=(rationalInner f g R).1 := by
  rw [←(realIndex R).sum_comp (fun i => sample R f i*sample R g i)]
  rw [Fintype.sum_prod_type,Fin.sum_univ_two]
  simp only [sample_real,sample_imag,←Finset.sum_add_distrib]
  rw [←(aliasArrayEquiv R).sum_comp
    (fun i => (entry R f i).1*(entry R g i).1+(entry R f i).2*(entry R g i).2)]
  simp only [Fintype.sum_prod_type,entry,Equiv.symm_apply_apply]
  simpa only [rationalInner,Prod.fst_sum,rationalComplexInner,Fintype.sum_prod_type] using
    sum_array_alias R (fun ν => ∑ j : Fin 3,((f ν j).1*(g ν j).1+(f ν j).2*(g ν j).2))

theorem realInner_sample (v w : FourierData) :
    v.realInner w=∑ i : Fin (2*aliasArraySize v.radius),sample v.radius v.field i*sample v.radius w.field i :=
  (sample_pair v.radius v.field w.field).symm

theorem form_matrix (v w : FourierData) (R : ℕ)
    (T : RationalAliasField →ₗ[ℚ] RationalAliasField) (hr : v.radius=R) (hT : T v.field=w.field) :
    PowerMachine.Quadratic.form (matrix R T) (sample R v.field)=v.realInner w := by
  have supported : RationalSupported v.field R := hr ▸ v.supported
  rw [PowerMachine.Quadratic.form,matrix_on_supported R T v.field supported,hT,
    realInner_sample,hr]

def translationLinear (M : ℕ) (a : Alias) (W : ℕ) : RationalAliasField →ₗ[ℚ] RationalAliasField where
  toFun := Supercell.rationalTranslation M a W
  map_add' f g := by
    funext ν j
    exact (complexMulLinear (Supercell.rationalPhaseCoefficient M a ν W)).map_add (f ν j) (g ν j)
  map_smul' c f := by
    funext ν j
    exact (complexMulLinear (Supercell.rationalPhaseCoefficient M a ν W)).map_smul c (f ν j)

def translatedLinear (M : ℕ) [NeZero M] (s z σ : ℚ) (a : Alias) (W ell K P : ℕ) :
    RationalAliasField →ₗ[ℚ] RationalAliasField :=
  (rootLinear s W ell).comp ((supercellLinear M z σ K P).comp
    ((translationLinear M a W).comp (rootLinear s W ell)))

theorem translatedLinear_field (M : ℕ) [NeZero M] (s z σ : ℚ) (a : Alias)
    (W ell K P : ℕ) (v : FourierData) :
    translatedLinear M s z σ a W ell K P v.field=
      (Supercell.finiteTranslatedSandwich M s z σ a W ell K P v).field := by
  rw [Supercell.finiteTranslatedSandwich,rootApply_field,FourierData.inverseApply_field,
    Supercell.finiteTranslation,FourierData.ofSupported_field,rootApply_field]
  · rfl
  · exact Supercell.rationalTranslation_supported M a W (FourierData.rootApply s W ell v).supported

def eigenvalueMatrix (L r N : ℕ) (z : ℚ) :
    Matrix (Fin (2*aliasArraySize (modeRadius L r N))) (Fin (2*aliasArraySize (modeRadius L r N))) ℚ :=
  matrix (modeRadius L r N) (stepLinear (FiniteAlgorithm.size L r N) 1
    (FiniteAlgorithm.scale L r N) z 0 (FiniteAlgorithm.precision L r N)
    (FiniteAlgorithm.rootBits L r N) (FiniteAlgorithm.inverseSteps L r N) (FiniteAlgorithm.cutoffBits L r N))

def couplingMatrix (L r N : ℕ) (z : ℚ) (a : Alias) :
    Matrix (Fin (2*aliasArraySize (modeRadius L r N))) (Fin (2*aliasArraySize (modeRadius L r N))) ℚ :=
  matrix (modeRadius L r N) (translatedLinear (FiniteAlgorithm.size L r N)
    (FiniteAlgorithm.scale L r N) z 0 a (FiniteAlgorithm.precision L r N)
    (FiniteAlgorithm.rootBits L r N) (FiniteAlgorithm.inverseSteps L r N) (FiniteAlgorithm.cutoffBits L r N))

attribute [local irreducible] FiniteAlgorithm.mode FiniteAlgorithm.rawMode FiniteAlgorithm.precision
  FiniteAlgorithm.iterations FiniteAlgorithm.seed FiniteAlgorithm.size modeRadius

theorem mode_radius_eq (L r N : ℕ) (z : ℚ) :
    (FiniteAlgorithm.mode L r N z).radius=modeRadius L r N := by
  rw [←normalizedMode_eq]
  rfl

theorem eigenvalueCenter_matrix (L r N : ℕ) (z : ℚ) :
    PowerMachine.Quadratic.form (eigenvalueMatrix L r N z)
      (sample (modeRadius L r N) (FiniteAlgorithm.mode L r N z).field)=
      FiniteAlgorithm.eigenvalueCenter L r N z := by
  apply form_matrix _ _ _ _ (mode_radius_eq L r N z)
  exact (stepLinear_field _ 1 _ _ _ _ _ _ _ _).trans (by
    rw [FourierData.scale_field,one_smul]
    rfl)

theorem couplingCenter_matrix (L r N : ℕ) (z : ℚ) (a : Alias) :
    PowerMachine.Quadratic.form (couplingMatrix L r N z a)
      (sample (modeRadius L r N) (FiniteAlgorithm.mode L r N z).field)=
      FiniteAlgorithm.couplingCenter L r N z a :=
  form_matrix _ _ _ _ (mode_radius_eq L r N z) (translatedLinear_field _ _ _ _ _ _ _ _ _ _)

#print axioms sample_pair
#print axioms eigenvalueCenter_matrix
#print axioms couplingCenter_matrix

end Maxwell.Continuum.Calibration.GlobalPower
