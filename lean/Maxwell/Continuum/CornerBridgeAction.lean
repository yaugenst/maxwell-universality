import Maxwell.Continuum.CornerBridgeCoordinates

/-!
# Exact action of the continuum cluster in sign-cube coordinates

The infinite nearest-neighbor potential, compressed by the actual fixed
transverse projection, becomes the certified finite corner action.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.CornerBridge

open FreeFiber ClusterComplement
open scoped Classical

def realMatrix (M : Corner.Mat) : BlockMatrix := M.map (algebraMap ℝ ℂ)

theorem matrixCLM_realMatrix (M : Corner.Mat) (u : Corner.Vec) :
    matrixCLM (realMatrix M) (momentumVector (realMomentum u)) =
      momentumVector (realMomentum (M.mulVec u)) := by
  apply PiLp.ext
  intro j
  change ∑ k, (M j k : ℂ) * (u k : ℂ) = (∑ k, M j k * u k : ℝ)
  simp only [Complex.ofReal_sum,Complex.ofReal_mul]

theorem clusterBlock_cubeAlias (s : Corner.Parity) :
    clusterBlock (cubeAlias s) = matrixCLM (realMatrix (Corner.waveProjection s)) := by
  rw [clusterBlock_central _ (alias_central s),alias_signs]
  rw [longitudinal,longitudinalMatrix,matrixCLM_smul,← matrixCLM_one_eq,← matrixCLM_smul,← matrixCLM_sub]
  congr 1
  ext i j
  change (1 : BlockMatrix) i j - (1 / 3 : ℂ) *
    ((Corner.waveSigns s i : ℂ) * (Corner.waveSigns s j : ℂ)) =
      (((1 : Corner.Mat) i j - (1 / 3 : ℝ) *
        (Corner.waveSigns s i * Corner.waveSigns s j) : ℝ) : ℂ)
  push_cast
  by_cases h : i = j <;> simp [Matrix.one_apply,h]

def cubeProjection (u : Cube) : Cube :=
  fun s => (realMatrix (Corner.waveProjection s)).mulVec (u s)

theorem clusterProjection_pack (u : Cube) :
    clusterProjection (pack u) = pack (cubeProjection u) := by
  apply eq_of_aliases
  · intro ν hν
    rw [clusterProjection_apply,clusterBlock_noncentral ν hν,zero_apply]
  · exact pack_noncentral _
  · intro s
    rw [clusterProjection_apply,pack_alias,clusterBlock_cubeAlias,pack_alias]
    rfl

theorem cubeProjection_realCube (u : Corner.ClusterField) :
    cubeProjection (realCube u) = realCube (Corner.clusterProjection u) := by
  funext s j
  exact congrArg (fun v : Polarization => v j)
    (matrixCLM_realMatrix (Corner.waveProjection s) (u s))

theorem clusterProjection_packReal (u : Corner.ClusterField) :
    clusterProjection (packReal u) = packReal (Corner.clusterProjection u) := by
  rw [packReal,clusterProjection_pack,cubeProjection_realCube]
  rfl

theorem cubeAlias_toggle_apply (s : Corner.Parity) (j k : Fin 3) :
    cubeAlias (Corner.toggle s j) k = if k = j then -cubeAlias s k - 1 else cubeAlias s k := by
  obtain ⟨a,b,c⟩ := s
  cases a <;> cases b <;> cases c <;> fin_cases j <;> fin_cases k <;>
    norm_num [alias_apply,parityBoolEquiv,Corner.toggle]

theorem cubeAlias_toggle_of_true (s : Corner.Parity) (j : Fin 3)
    (h : parityBoolEquiv s j = true) :
    cubeAlias (Corner.toggle s j) = cubeAlias s - unitAlias j := by
  funext k
  rw [cubeAlias_toggle_apply]
  by_cases hkj : k = j
  · subst k
    simp [alias_apply,h,unitAlias]
  · simp [hkj,unitAlias]

theorem cubeAlias_toggle_of_false (s : Corner.Parity) (j : Fin 3)
    (h : parityBoolEquiv s j = false) :
    cubeAlias (Corner.toggle s j) = cubeAlias s + unitAlias j := by
  funext k
  rw [cubeAlias_toggle_apply]
  by_cases hkj : k = j
  · subst k
    simp [alias_apply,h,unitAlias]
  · simp [hkj,unitAlias]

theorem cubeAlias_plus_noncentral (s : Corner.Parity) (j : Fin 3)
    (h : parityBoolEquiv s j = true) : ¬IsCentralAlias (cubeAlias s + unitAlias j) := by
  intro hn
  have hj := hn j
  norm_num [alias_apply,h,unitAlias] at hj

theorem cubeAlias_minus_noncentral (s : Corner.Parity) (j : Fin 3)
    (h : parityBoolEquiv s j = false) : ¬IsCentralAlias (cubeAlias s - unitAlias j) := by
  intro hn
  have hj := hn j
  norm_num [alias_apply,h,unitAlias] at hj

theorem pack_neighbor_sum (u : Cube) (s : Corner.Parity) (j : Fin 3) :
    pack u (cubeAlias s + unitAlias j) + pack u (cubeAlias s - unitAlias j) =
      momentumVector (u (Corner.toggle s j)) := by
  cases h : parityBoolEquiv s j
  · rw [← cubeAlias_toggle_of_false s j h,pack_alias,
      pack_noncentral _ _ (cubeAlias_minus_noncentral s j h),add_zero]
  · rw [pack_noncentral _ _ (cubeAlias_plus_noncentral s j h),
      ← cubeAlias_toggle_of_true s j h,pack_alias,zero_add]

def cubeOperator (u : Cube) : Cube := fun s =>
  ∑ j : Fin 3, -(potentialWeight j : ℂ) •
    (realMatrix (Corner.waveProjection s)).mulVec
      ((realMatrix (Corner.waveProjection (Corner.toggle s j))).mulVec (u (Corner.toggle s j)))

theorem clusterPotential_pack (u : Cube) :
    clusterPotential (pack u) = pack (cubeOperator u) := by
  apply eq_of_aliases
  · intro ν hν
    change -(clusterProjection (potential (clusterProjection (pack u))) ν) = 0
    rw [clusterProjection_apply,clusterBlock_noncentral ν hν,zero_apply,neg_zero]
  · exact pack_noncentral _
  · intro s
    change -(clusterBlock (cubeAlias s) (potential (clusterProjection (pack u)) (cubeAlias s))) = _
    rw [clusterProjection_pack,potential_apply]
    simp_rw [pack_neighbor_sum]
    rw [map_sum,← Finset.sum_neg_distrib,pack_alias,clusterBlock_cubeAlias]
    apply PiLp.ext
    intro i
    simp only [cubeOperator,cubeProjection,momentumVector,Finset.sum_apply,Pi.smul_apply]
    simp only [map_smul,neg_smul]
    rfl

theorem cubeOperator_realCube (u : Corner.ClusterField) :
    cubeOperator (realCube u) = realCube (Corner.clusterOperator u) := by
  funext s i
  change (∑ j : Fin 3, -(potentialWeight j : ℂ) •
      (realMatrix (Corner.waveProjection s)).mulVec
        ((realMatrix (Corner.waveProjection (Corner.toggle s j))).mulVec
          (realMomentum (u (Corner.toggle s j))))) i = _
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,realCube,realMomentum,
    Corner.clusterOperator,Complex.ofReal_sum,Complex.ofReal_mul,Complex.ofReal_neg,
    Complex.ofReal_div,Complex.ofReal_ofNat]
  apply Finset.sum_congr rfl
  intro j _
  have hw : potentialWeight j = Corner.weights j / 2 := by
    fin_cases j <;> norm_num [potentialWeight,Corner.weights]
  rw [hw,Complex.ofReal_div,Complex.ofReal_ofNat]
  congr 1
  change matrixCLM (realMatrix (Corner.waveProjection s))
    (matrixCLM (realMatrix (Corner.waveProjection (Corner.toggle s j)))
      (momentumVector (realMomentum (u (Corner.toggle s j))))) i = _
  rw [matrixCLM_realMatrix,matrixCLM_realMatrix]
  rfl

theorem clusterPotential_packReal (u : Corner.ClusterField) :
    clusterPotential (packReal u) = packReal (Corner.clusterOperator u) := by
  rw [packReal,clusterPotential_pack,cubeOperator_realCube]
  rfl

end Maxwell.Continuum.CornerBridge
