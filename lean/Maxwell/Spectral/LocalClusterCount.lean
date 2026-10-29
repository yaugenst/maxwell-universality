import Maxwell.Spectral.GlobalComparison
import Maxwell.Spectral.YeeTaylorRemainder

/-! Actual local cluster cardinality from the independent lower and upper
threshold certificates, including the frozen-material perturbation. -/
noncomputable section
namespace Maxwell.Spectral.LocalClusterCount
open Maxwell.Certificate.FourierBinding Maxwell.Spectral.PrimitiveYee
open Maxwell.Spectral.PeriodicYee (Momentum)

/-- Disjoint negative and positive directions share the same upper threshold. -/
theorem positive_count_le_two {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : ι → ℝ) (b : ℝ) (hb : 0 < b) (N : ℕ)
    (hneg : N ≤ (Finset.univ.filter fun i => μ i < 0).card)
    (hupper : (Finset.univ.filter fun i => μ i < b).card ≤ N+2) :
    (Finset.univ.filter fun i => 0 < μ i ∧ μ i < b).card ≤ 2 := by
  classical
  let neg := Finset.univ.filter fun i => μ i < 0
  let pos := Finset.univ.filter fun i => 0 < μ i ∧ μ i < b
  have hd : Disjoint neg pos := by
    apply Finset.disjoint_left.mpr
    intro i hn hp
    have hn' := (Finset.mem_filter.mp hn).2
    have hp' := (Finset.mem_filter.mp hp).2.1
    linarith
  have hsub : neg ∪ pos ⊆ Finset.univ.filter fun i => μ i < b := by
    intro i hi
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rcases Finset.mem_union.mp hi with hn | hp
    · exact ((Finset.mem_filter.mp hn).2).trans hb
    · exact (Finset.mem_filter.mp hp).2.2
  have hc := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hd] at hc
  change neg.card + pos.card ≤ _ at hc
  change N ≤ neg.card at hneg
  change pos.card ≤ 2
  omega

/-- Uniform shift appropriate to the upper endpoint of the local band window. -/
def localMaterial : PeriodicYee.Cell20 → ℝ := fun r => Concrete.baseMaterial r + 64*(7/256)

theorem localMaterial_edge_bounds (e : Electric) :
    1 ≤ edgeAverage localMaterial e ∧ edgeAverage localMaterial e ≤ 14 := by
  change 1 ≤ edgeAverage (fun r => Concrete.baseMaterial r + 64*(7/256)) e ∧
    edgeAverage (fun r => Concrete.baseMaterial r + 64*(7/256)) e ≤ 14
  rw [primitive_edgeAverage_uniform_shift]
  have h := GlobalComparison.base_edge_bounds e
  constructor <;> linarith

theorem actual_negative_count (c : Momentum)
    (hlo : 2002 ≤ (Finset.univ.filter fun i =>
      (electricFiber_symmetric Concrete.baseMaterial (boundaryMomentum c)).eigenvalues rfl i < -1/4096).card) :
    2002 ≤ (Finset.univ.filter fun i =>
      (electricFiber_symmetric Concrete.material (boundaryMomentum c)).eigenvalues rfl i < 0).card := by
  apply hlo.trans
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  have hcomp := (Concrete.primitive_eigenvalue_comparison (boundaryMomentum c) i).1
  change (electricFiber_symmetric Concrete.material (boundaryMomentum c)).eigenvalues rfl i ≤
    (electricFiber_symmetric Concrete.baseMaterial (boundaryMomentum c)).eigenvalues rfl i at hcomp
  linarith

theorem actual_upper_count (c : Momentum)
    (hhi : (Finset.univ.filter fun i =>
      (electricFiber_symmetric localMaterial (boundaryMomentum c)).eigenvalues rfl i < 1/4096).card ≤ 2004) :
    (Finset.univ.filter fun i =>
      (electricFiber_symmetric Concrete.material (boundaryMomentum c)).eigenvalues rfl i < 7/256).card ≤ 2004 := by
  have hb : (Finset.univ.filter fun i =>
      (electricFiber_symmetric Concrete.baseMaterial (boundaryMomentum c)).eigenvalues rfl i <
        7/256+1/4096).card ≤ 2004 := by
    rw [GlobalComparison.uniform_shift_threshold_count]
    exact hhi
  refine le_trans (Finset.card_le_card ?_) hb
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  have hcomp := (Concrete.primitive_eigenvalue_comparison (boundaryMomentum c) i).2
  change (electricFiber_symmetric Concrete.baseMaterial (boundaryMomentum c)).eigenvalues rfl i ≤
    (electricFiber_symmetric Concrete.material (boundaryMomentum c)).eigenvalues rfl i+1023/2^26 at hcomp
  have herr : (1023 : ℝ)/2^26 < 1/4096 := by norm_num
  linarith

/-- Only the two finite threshold counts remain; material order and the
explicit perturbation displacement are already discharged. -/
theorem actual_positive_count (c : Momentum)
    (hlo : 2002 ≤ (Finset.univ.filter fun i =>
      (electricFiber_symmetric Concrete.baseMaterial (boundaryMomentum c)).eigenvalues rfl i < -1/4096).card)
    (hhi : (Finset.univ.filter fun i =>
      (electricFiber_symmetric localMaterial (boundaryMomentum c)).eigenvalues rfl i < 1/4096).card ≤ 2004) :
    (Finset.univ.filter fun i =>
      0 < (electricFiber_symmetric Concrete.material (boundaryMomentum c)).eigenvalues rfl i ∧
      (electricFiber_symmetric Concrete.material (boundaryMomentum c)).eigenvalues rfl i < 7/256).card ≤ 2 :=
  positive_count_le_two _ _ (by norm_num) 2002 (actual_negative_count c hlo) (actual_upper_count c hhi)

theorem actual_positive_count_of_magnetic_upper (c : Momentum)
    (hlo : 2002 ≤ (Finset.univ.filter fun i =>
      (electricFiber_symmetric Concrete.baseMaterial (boundaryMomentum c)).eigenvalues rfl i < -1/4096).card)
    (hhi : (Finset.univ.filter fun i =>
      (shiftedMagneticFourier_symmetric localMaterial c (1/64+1/4096)).eigenvalues rfl i < 0).card ≤ 2004) :
    (Finset.univ.filter fun i =>
      0 < (electricFiber_symmetric Concrete.material (boundaryMomentum c)).eigenvalues rfl i ∧
      (electricFiber_symmetric Concrete.material (boundaryMomentum c)).eigenvalues rfl i < 7/256).card ≤ 2 := by
  exact actual_positive_count c hlo ((MagneticThreshold.energy_threshold_upper localMaterial
    (fun e => (localMaterial_edge_bounds e).1) c (1/4096) (by norm_num)).trans hhi)

theorem actual_positive_count_of_magnetic_counts (c : Momentum)
    (hlo : 2002 ≤ (Finset.univ.filter fun i =>
      (shiftedMagneticFourier_symmetric Concrete.baseMaterial c (1/64-1/4096)).eigenvalues rfl i < 0).card)
    (hhi : (Finset.univ.filter fun i =>
      (shiftedMagneticFourier_symmetric localMaterial c (1/64+1/4096)).eigenvalues rfl i < 0).card ≤ 2004) :
    (Finset.univ.filter fun i =>
      0 < (electricFiber_symmetric Concrete.material (boundaryMomentum c)).eigenvalues rfl i ∧
      (electricFiber_symmetric Concrete.material (boundaryMomentum c)).eigenvalues rfl i < 7/256).card ≤ 2 := by
  exact actual_positive_count_of_magnetic_upper c (hlo.trans
    (by simpa only [neg_div] using (MagneticThreshold.energy_threshold_lower Concrete.baseMaterial
      (fun e => (GlobalComparison.base_edge_bounds e).1) c (1/4096) (by norm_num) (by norm_num)))) hhi

/-- Unitary conjugacy preserves strict threshold counts, including their
multiplicities, without requiring a common ordering of eigenvectors. -/
theorem threshold_count_unitary {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B U : Matrix ι ι ℂ) (hleft : U.conjTranspose*U = 1)
    (hright : U*U.conjTranspose = 1) (hbind : U.conjTranspose*A*U = B)
    (hA : A.toEuclideanLin.IsSymmetric) (hB : B.toEuclideanLin.IsSymmetric) (a : ℝ) :
    (Finset.univ.filter fun i => hA.eigenvalues rfl i < a).card =
      (Finset.univ.filter fun i => hB.eigenvalues rfl i < a).card := by
  let AS := A-(a : ℂ)•1
  let BS := B-(a : ℂ)•1
  have hAS : AS.toEuclideanLin.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    ((Matrix.isSymmetric_toEuclideanLin_iff.mp hA).sub
      (Matrix.isHermitian_one.smul (by simp : star (a : ℂ) = (a : ℂ))))
  have hBS : BS.toEuclideanLin.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    ((Matrix.isSymmetric_toEuclideanLin_iff.mp hB).sub
      (Matrix.isHermitian_one.smul (by simp : star (a : ℂ) = (a : ℂ))))
  rw [threshold_count_eq_negative_of_shift A.toEuclideanLin AS.toEuclideanLin hA hAS a
    (by simp only [AS, map_sub, map_smul, Matrix.toLpLin_one]), threshold_count_eq_negative_of_shift B.toEuclideanLin BS.toEuclideanLin hB hBS a
    (by simp only [BS, map_sub, map_smul, Matrix.toLpLin_one])]
  apply matrix_negative_count_unitary AS BS U hleft hright _ hAS hBS
  simp only [AS, BS, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, hleft, hbind]

/-- Cartesian box coordinates of the actual centered primitive momentum. -/
def centeredMomentum (k : Translation) (q : Momentum) : Momentum :=
  cartesianMomentum (fun j => (k j : ℝ)/2) + q

theorem centeredMomentum_binding (k : Translation) (q : Momentum) :
    boundaryMomentum (centeredMomentum k q) = timeReversalMomentum k + YeeTaylor.cartesianIncrement q := by
  funext j
  fin_cases j <;>
    simp [centeredMomentum, cartesianMomentum, boundaryMomentum, timeReversalMomentum,
      YeeTaylor.cartesianIncrement] <;> ring

/-- The local Taylor operator and the actual boundary-phase matrix have
the same threshold counts by the proved midpoint gauge identity. -/
theorem centered_threshold_count (k : Translation) (q : Momentum) (a : ℝ) :
    (Finset.univ.filter fun i =>
      (electricFiber_symmetric Concrete.material (boundaryMomentum (centeredMomentum k q))).eigenvalues rfl i < a).card =
    (Finset.univ.filter fun i =>
      (YeeTaylorRemainder.centeredOperator_symmetric k q).eigenvalues rfl i < a).card := by
  apply threshold_count_unitary
    (fiber Concrete.material (boundaryMomentum (centeredMomentum k q)))
    (YeeTaylor.centeredFiber Concrete.material (timeReversalMomentum k) q)
    (YeeTaylor.electricGauge q) (YeeTaylor.electricGauge_unitary q).1
    (YeeTaylor.electricGauge_unitary q).2 _ _ _ a
  rw [centeredMomentum_binding]
  exact YeeTaylor.centeredFiber_gauge Concrete.material (timeReversalMomentum k) q

/-- The two actual finite cover counts directly supply the cluster premise
used by the centered polynomial trial-subspace argument. -/
theorem centered_positive_count (k : Translation) (q : Momentum)
    (hlo : 2002 ≤ (Finset.univ.filter fun i =>
      (electricFiber_symmetric Concrete.baseMaterial (boundaryMomentum (centeredMomentum k q))).eigenvalues rfl i < -1/4096).card)
    (hhi : (Finset.univ.filter fun i =>
      (shiftedMagneticFourier_symmetric localMaterial (centeredMomentum k q)
        (1/64+1/4096)).eigenvalues rfl i < 0).card ≤ 2004) :
    (Finset.univ.filter fun i =>
      0 < (YeeTaylorRemainder.centeredOperator_symmetric k q).eigenvalues rfl i ∧
      (YeeTaylorRemainder.centeredOperator_symmetric k q).eigenvalues rfl i < 7/256).card ≤ 2 := by
  apply positive_count_le_two _ _ (by norm_num) 2002
  · rw [← centered_threshold_count]
    exact actual_negative_count _ hlo
  · rw [← centered_threshold_count]
    exact actual_upper_count _ ((MagneticThreshold.energy_threshold_upper localMaterial
      (fun e => (localMaterial_edge_bounds e).1) _ (1/4096) (by norm_num)).trans hhi)

end Maxwell.Spectral.LocalClusterCount
