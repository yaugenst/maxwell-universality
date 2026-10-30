import Maxwell.Continuum.CalibrationFiniteApplication

/-! Exact rational linearity of the literal finite Fourier operator. The
matrix-power construction uses these maps, not an assumed operator model. -/

namespace Maxwell.Continuum.Calibration.GlobalPower
open FreeFiber PeriodicSampling
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

abbrev Field (V : Type*) := Alias→Fin 3→V

section Generic
variable {V : Type*} [AddCommGroup V] [Module ℚ V]

def noncentralLinear : Field V →ₗ[ℚ] Field V where
  toFun := rationalNoncentral
  map_add' f g := by
    funext ν j
    simp only [rationalNoncentral,Pi.add_apply]
    split_ifs <;> simp
  map_smul' c f := by
    funext ν j
    simp only [rationalNoncentral,Pi.smul_apply]
    split_ifs <;> simp

def centralLinear : Field V →ₗ[ℚ] Field V where
  toFun := rationalCentral
  map_add' f g := by
    funext ν j
    simp only [rationalCentral,Pi.add_apply]
    split_ifs <;> simp
  map_smul' c f := by
    funext ν j
    simp only [rationalCentral,Pi.smul_apply]
    split_ifs <;> simp

def potentialLinear : Field V →ₗ[ℚ] Field V where
  toFun := rationalPotential
  map_add' f g := by
    funext ν j
    simp only [rationalPotential,Pi.add_apply,smul_add,Finset.sum_add_distrib]
    abel
  map_smul' c f := by
    funext ν j
    change (∑k : Fin 3,rationalWeight k • (c • f (ν+unitAlias k) j+c • f (ν-unitAlias k) j))=
      c • (∑k : Fin 3,rationalWeight k • (f (ν+unitAlias k) j+f (ν-unitAlias k) j))
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [← smul_add]
    exact smul_comm _ _ _

def perturbationLinear : Field V →ₗ[ℚ] Field V :=
  (-rationalAmplitude) • noncentralLinear.comp (potentialLinear.comp noncentralLinear)

def rightLinear : Field V →ₗ[ℚ] Field V :=
  (-rationalAmplitude) • noncentralLinear.comp (potentialLinear.comp centralLinear)

def leftLinear : Field V →ₗ[ℚ] Field V :=
  (-rationalAmplitude) • centralLinear.comp (potentialLinear.comp noncentralLinear)

def freeLinear (t E : ℚ) (r : Fin 3→ℚ) : Field V →ₗ[ℚ] Field V where
  toFun := rationalFreeApply t E r
  map_add' f g := by
    funext ν j
    simp only [rationalFreeApply,Pi.add_apply,smul_add,Finset.sum_add_distrib]
  map_smul' c f := by
    funext ν j
    change (∑k : Fin 3,rationalFreeInverseMatrix t E r ν j k • (c • f ν k))=
      c • (∑k : Fin 3,rationalFreeInverseMatrix t E r ν j k • f ν k)
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro k _
    exact smul_comm _ _ _

def inverseLinear (t E : ℚ) (r : Fin 3→ℚ) : ℕ→(Field V →ₗ[ℚ] Field V)
  | 0 => 0
  | k+1 => freeLinear t E r-(freeLinear t E r).comp
      (perturbationLinear.comp (inverseLinear t E r k))

theorem inverseLinear_apply (t E : ℚ) (r : Fin 3→ℚ) (K : ℕ) (f : Field V) :
    inverseLinear t E r K f=rationalInverseApply t E r f K := by
  induction K with
  | zero => rfl
  | succ K ih =>
    change rationalFreeApply t E r f-rationalFreeApply t E r
      (rationalPerturbation (inverseLinear t E r K f))=_
    rw [ih]
    rfl

def centralMatrixLinear (A : Matrix (Fin 24) (Fin 24) ℚ) : Field V →ₗ[ℚ] Field V where
  toFun := rationalCentralMatrixApply A
  map_add' f g := by
    funext ν j
    simp only [rationalCentralMatrixApply,rationalExpandCoordinates,rationalCoordinates,Pi.add_apply]
    split_ifs <;> simp [smul_add,Finset.sum_add_distrib]
  map_smul' c f := by
    funext ν j
    simp only [rationalCentralMatrixApply,rationalExpandCoordinates,rationalCoordinates,Pi.smul_apply]
    split_ifs
    · rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro k _
      exact smul_comm _ _ _
    · exact (smul_zero _).symm

def fullLinear (t E : ℚ) (r : Fin 3→ℚ) (K : ℕ) : Field V →ₗ[ℚ] Field V :=
  let C := (inverseLinear t E r K).comp noncentralLinear
  C+(centralLinear-C.comp rightLinear).comp
    ((centralMatrixLinear (rationalMatrixInverse (rationalSchurMatrix t E r K))).comp
      (LinearMap.id-leftLinear.comp C))

theorem fullLinear_apply (t E : ℚ) (r : Fin 3→ℚ) (K : ℕ) (f : Field V) :
    fullLinear t E r K f=rationalFullApply t E r K f := by
  simp only [fullLinear,LinearMap.add_apply,LinearMap.comp_apply,LinearMap.sub_apply,
    LinearMap.id_apply,inverseLinear_apply]
  rfl

def gridLinear (z σ : ℚ) (r : Fin 3→ℚ) (K P : ℕ) : Field V →ₗ[ℚ] Field V :=
  if activeGrid r then (gridCutoffApprox r P).center • fullLinear (piCenter K) (z+σ+7) r K else 0

theorem gridLinear_apply (z σ : ℚ) (r : Fin 3→ℚ) (K P : ℕ) (f : Field V) :
    gridLinear z σ r K P f=rationalGridApply z σ r K P f := by
  unfold gridLinear rationalGridApply
  split_ifs
  · simp only [LinearMap.smul_apply,fullLinear_apply]
  · rfl

def supercellLinear (M : ℕ) [NeZero M] (z σ : ℚ) (K P : ℕ) : Field V →ₗ[ℚ] Field V where
  toFun := Supercell.rationalApply M z σ K P
  map_add' f g := by
    funext ν j
    let p := (Supercell.indexEquiv M).symm ν
    have h := (gridLinear z σ (Supercell.gridCoordinates M p.1) K P).map_add
      (fun μ k => f (Supercell.join M (p.1,μ)) k)
      (fun μ k => g (Supercell.join M (p.1,μ)) k)
    simp only [gridLinear_apply] at h
    exact congrFun (congrFun h p.2) j
  map_smul' c f := by
    funext ν j
    let p := (Supercell.indexEquiv M).symm ν
    have h := (gridLinear z σ (Supercell.gridCoordinates M p.1) K P).map_smul c
      (fun μ k => f (Supercell.join M (p.1,μ)) k)
    simp only [gridLinear_apply] at h
    exact congrFun (congrFun h p.2) j

end Generic

def complexMulLinear (a : RationalComplex) : RationalComplex →ₗ[ℚ] RationalComplex where
  toFun := rationalComplexMul a
  map_add' b c := by
    ext <;> simp only [rationalComplexMul,Prod.fst_add,Prod.snd_add] <;> ring
  map_smul' c b := by
    ext <;> simp [rationalComplexMul,smul_eq_mul] <;> ring

def rootLinear (s : ℚ) (W ell : ℕ) : RationalAliasField →ₗ[ℚ] RationalAliasField where
  toFun := rationalRootApply s W ell
  map_add' f g := by
    funext ν j
    change (∑n∈Product.frequencyCube (rootDegree s W ell),
      complexMulLinear (rectangleRational (computedRootCoefficient s W ell n))
        (f (ν-n) j+g (ν-n) j))=_
    simp only [map_add,Finset.sum_add_distrib]
    rfl
  map_smul' c f := by
    funext ν j
    change (∑n∈Product.frequencyCube (rootDegree s W ell),
      complexMulLinear (rectangleRational (computedRootCoefficient s W ell n))
        (c • f (ν-n) j))=c • (∑n∈Product.frequencyCube (rootDegree s W ell),
      complexMulLinear (rectangleRational (computedRootCoefficient s W ell n)) (f (ν-n) j))
    simp only [map_smul,Finset.smul_sum]

def stepLinear (M : ℕ) [NeZero M] (c s z σ : ℚ) (W ell K P : ℕ) :
    RationalAliasField →ₗ[ℚ] RationalAliasField :=
  c • (rootLinear s W ell).comp
    ((supercellLinear M z σ K P).comp (rootLinear s W ell))

theorem rootApply_field (s : ℚ) (W ell : ℕ) (v : FourierData) :
    (FourierData.rootApply s W ell v).field=rationalRootApply s W ell v.field :=
  FourierData.ofSupported_field (v.supported.rootApply s W ell)

theorem stepLinear_field (M : ℕ) [NeZero M] (c s z σ : ℚ) (W ell K P : ℕ) (v : FourierData) :
    stepLinear M c s z σ W ell K P v.field=
      (FourierData.scale c (FourierData.sandwichApply M s z σ W ell K P v)).field := by
  rw [FourierData.scale_field,FourierData.sandwichApply,rootApply_field,
    FourierData.inverseApply_field,rootApply_field]
  rfl

#print axioms fullLinear_apply
#print axioms stepLinear_field

end Maxwell.Continuum.Calibration.GlobalPower
