import Maxwell.Spectral.MagneticThreshold
import Maxwell.Spectral.PrimitivePerturbation
import Maxwell.Spectral.SeparatedInverse
import Maxwell.Certificate.PointWitness.CenterBounds

/-! The two independent finite covers give complementary electric threshold
counts. Their combination excludes every actual perturbed eigenvalue at the
selected edge energy, with the paper's explicit rational global margin. -/

noncomputable section
namespace Maxwell.Spectral.GlobalComparison
open Maxwell.Certificate Maxwell.Certificate.FourierBinding Maxwell.Certificate.PointWitness
open Maxwell.Spectral.PrimitiveYee
open Maxwell.Spectral.PeriodicYee (Momentum)

/-- Saturated threshold counts leave no spectral value between the thresholds. -/
theorem outside_of_threshold_counts {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : ι → ℝ) (a b : ℝ) (N : ℕ) (hab : a ≤ b)
    (hlo : N ≤ (Finset.univ.filter fun i => μ i < a).card)
    (hhi : (Finset.univ.filter fun i => μ i < b).card ≤ N) (i : ι) :
    μ i < a ∨ b ≤ μ i := by
  classical
  have hsub : (Finset.univ.filter fun i => μ i < a) ⊆
      (Finset.univ.filter fun i => μ i < b) := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    exact hj.trans_le hab
  have heq := Finset.eq_of_subset_of_card_le hsub (hhi.trans hlo)
  by_cases hi : μ i < b
  · left
    have hm : i ∈ Finset.univ.filter fun i => μ i < b := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
    rw [← heq] at hm
    exact (Finset.mem_filter.mp hm).2
  · exact Or.inr (le_of_not_gt hi)

private theorem negative_count_congr {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    {A B : H →ₗ[ℂ] H} (hAB : A = B) (hA : A.IsSymmetric) (hB : B.IsSymmetric) :
    (Finset.univ.filter fun i => hA.eigenvalues rfl i < 0).card =
      (Finset.univ.filter fun i => hB.eigenvalues rfl i < 0).card := by
  subst B
  rfl

/-- Uniform material shifting is exactly an electric energy-threshold shift,
including multiplicities and without choosing compatible eigenvalue orderings. -/
theorem uniform_shift_threshold_count (material : PeriodicYee.Cell20 → ℝ)
    (c : Momentum) (a b : ℝ) :
    (Finset.univ.filter fun i =>
      (electricFiber_symmetric material (boundaryMomentum c)).eigenvalues rfl i < a+b).card =
    (Finset.univ.filter fun i =>
      (electricFiber_symmetric (fun r => material r+64*a) (boundaryMomentum c)).eigenvalues rfl i < b).card := by
  rw [MagneticThreshold.energy_threshold_count, MagneticThreshold.energy_threshold_count]
  have he : MagneticThreshold.energyShift material (boundaryMomentum c) (a+b) =
      MagneticThreshold.energyShift (fun r => material r+64*a) (boundaryMomentum c) b := by
    simp only [MagneticThreshold.energyShift, primitive_fiber_uniform_shift,
      Complex.ofReal_add, add_smul]
    abel
  exact negative_count_congr (congrArg (fun A : Matrix Electric Electric ℂ => A.toEuclideanLin) he) _ _

def comparatorMaterial : PeriodicYee.Cell20 → ℝ := fun r => Concrete.baseMaterial r + 64*(157/16384)

theorem base_edge_bounds (e : Electric) :
    1 ≤ edgeAverage Concrete.baseMaterial e ∧ edgeAverage Concrete.baseMaterial e ≤ 12 := by
  rw [edgeAverage_binding]
  apply PeriodicYee.edgeAverage_bounds
  intro r
  dsimp [Concrete.baseMaterial, Material.baseValue]
  split <;> norm_num

theorem comparator_edge_bounds (e : Electric) :
    1 ≤ edgeAverage comparatorMaterial e ∧ edgeAverage comparatorMaterial e ≤ 13 := by
  change 1 ≤ edgeAverage (fun r => Concrete.baseMaterial r + 64*(157/16384)) e ∧
    edgeAverage (fun r => Concrete.baseMaterial r + 64*(157/16384)) e ≤ 13
  rw [primitive_edgeAverage_uniform_shift]
  have h := base_edge_bounds e
  constructor <;> linarith

/-- The actual perturbed eigenvalues obey the complementary global bounds
once the two finite box families have supplied their counts at this momentum. -/
theorem actual_eigenvalue_outside (c : Momentum)
    (hlo : 2002 ≤ (Finset.univ.filter fun i =>
      (electricFiber_symmetric Concrete.baseMaterial (boundaryMomentum c)).eigenvalues rfl i < -1/4096).card)
    (hhi : (Finset.univ.filter fun i =>
      (electricFiber_symmetric comparatorMaterial (boundaryMomentum c)).eigenvalues rfl i < 1/2^24).card ≤ 2002)
    (i : Fin (Module.finrank ℂ FourierSpace)) :
    (electricFiber_symmetric Concrete.material (boundaryMomentum c)).eigenvalues rfl i < -1/4096 ∨
      642053/2^26 ≤ (electricFiber_symmetric Concrete.material (boundaryMomentum c)).eigenvalues rfl i := by
  have hb : (Finset.univ.filter fun i =>
      (electricFiber_symmetric Concrete.baseMaterial (boundaryMomentum c)).eigenvalues rfl i <
        157/16384+1/2^24).card ≤ 2002 := by
    rw [uniform_shift_threshold_count]
    exact hhi
  have ho := outside_of_threshold_counts
    ((electricFiber_symmetric Concrete.baseMaterial (boundaryMomentum c)).eigenvalues rfl)
    (-1/4096) (157/16384+1/2^24) 2002 (by norm_num) hlo hb i
  have hcomp := Concrete.primitive_eigenvalue_comparison (boundaryMomentum c) i
  rcases ho with h | h
  · exact Or.inl (hcomp.1.trans_lt h)
  · right
    have hcomp2 := hcomp.2
    change (electricFiber_symmetric Concrete.baseMaterial (boundaryMomentum c)).eigenvalues rfl i ≤
      (electricFiber_symmetric Concrete.material (boundaryMomentum c)).eigenvalues rfl i+1023/2^26 at hcomp2
    linarith

theorem pointEnergy_precise_upper : pointEnergy < 23913/2500000 := by
  have h := (abs_le.mp pointIndex0_interval).2
  change pointEnergy-pointCenter0 ≤ 1/2^47 at h
  have hc : pointCenter0+1/2^47 < (23913/2500000 : ℝ) := by
    norm_num [pointCenter0, lambdaNumerator0]
  linarith

/-- The global complement is separated from the same selected actual edge
energy by at least the explicit `1/500000` margin. -/
theorem actual_edge_gap (c : Momentum)
    (hlo : 2002 ≤ (Finset.univ.filter fun i =>
      (electricFiber_symmetric Concrete.baseMaterial (boundaryMomentum c)).eigenvalues rfl i < -1/4096).card)
    (hhi : (Finset.univ.filter fun i =>
      (electricFiber_symmetric comparatorMaterial (boundaryMomentum c)).eigenvalues rfl i < 1/2^24).card ≤ 2002)
    (i : Fin (Module.finrank ℂ FourierSpace)) :
    1/500000 ≤ |(electricFiber_symmetric Concrete.material (boundaryMomentum c)).eigenvalues rfl i-pointEnergy| := by
  rcases actual_eigenvalue_outside c hlo hhi i with hn | hp
  · apply le_trans _ (neg_le_abs _)
    linarith [pointEnergy_range.1]
  · apply le_trans _ (le_abs_self _)
    linarith [pointEnergy_precise_upper]

/-- This constructs the actual finite Yee inverse on the global complement;
its entries or existence are not supplied as a premise. -/
theorem actual_edge_invertible (c : Momentum)
    (hlo : 2002 ≤ (Finset.univ.filter fun i =>
      (electricFiber_symmetric Concrete.baseMaterial (boundaryMomentum c)).eigenvalues rfl i < -1/4096).card)
    (hhi : (Finset.univ.filter fun i =>
      (electricFiber_symmetric comparatorMaterial (boundaryMomentum c)).eigenvalues rfl i < 1/2^24).card ≤ 2002) :
    (Matrix.toEuclideanCLM (n := Electric) (𝕜 := ℂ)
      (fiber Concrete.material (boundaryMomentum c)) - (pointEnergy : ℂ) • 1).IsInvertible := by
  let A := Matrix.toEuclideanCLM (n := Electric) (𝕜 := ℂ)
    (fiber Concrete.material (boundaryMomentum c))
  let B := SeparatedInverse.equiv A (electricFiber_symmetric Concrete.material (boundaryMomentum c))
    pointEnergy (1/500000) (by norm_num) (actual_edge_gap c hlo hhi)
  exact ⟨B, rfl⟩

end Maxwell.Spectral.GlobalComparison
