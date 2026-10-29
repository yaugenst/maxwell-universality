import Maxwell.Spectral.ConcreteFolding
import Maxwell.Spectral.YeeTaylor

namespace Maxwell.Spectral

noncomputable section

section BlockAlgebra
variable {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq α] [DecidableEq ι]

omit [DecidableEq ι] in
theorem sectorDiagonal_mul (A B : α → Matrix ι ι ℂ) :
    sectorDiagonal A * sectorDiagonal B = sectorDiagonal (fun a => A a * B a) := by
  ext ⟨i,a⟩ ⟨j,b⟩
  by_cases hab : a = b
  · subst b
    simp [sectorDiagonal, Matrix.mul_apply, Fintype.sum_prod_type,
      mul_ite, ite_mul, Finset.sum_ite_eq']
  · simp [sectorDiagonal, Matrix.mul_apply, Fintype.sum_prod_type,
      mul_ite, ite_mul, Finset.sum_ite_eq', hab]

omit [Fintype α] [Fintype ι] [DecidableEq ι] in
theorem sectorDiagonal_conjTranspose (A : α → Matrix ι ι ℂ) :
    (sectorDiagonal A).conjTranspose = sectorDiagonal (fun a => (A a).conjTranspose) := by
  ext ⟨i,a⟩ ⟨j,b⟩
  by_cases h : a = b
  · subst b
    simp [sectorDiagonal, Matrix.conjTranspose_apply]
  · simp [sectorDiagonal, Matrix.conjTranspose_apply, h, Ne.symm h]

omit [Fintype α] [Fintype ι] in
theorem sectorDiagonal_one :
    sectorDiagonal (fun _ : α => (1 : Matrix ι ι ℂ)) = 1 := by
  ext ⟨i,a⟩ ⟨j,b⟩
  by_cases ha : a = b <;> by_cases hi : i = j <;>
    simp [sectorDiagonal, Matrix.one_apply, ha, hi]

theorem sectorDiagonal_unitary (A : α → Matrix ι ι ℂ)
    (hA : ∀ a, (A a).conjTranspose * A a = 1 ∧ A a * (A a).conjTranspose = 1) :
    (sectorDiagonal A).conjTranspose * sectorDiagonal A = 1 ∧
      sectorDiagonal A * (sectorDiagonal A).conjTranspose = 1 := by
  rw [sectorDiagonal_conjTranspose, sectorDiagonal_mul, sectorDiagonal_mul]
  constructor
  · simp only [(hA _).1, sectorDiagonal_one]
  · simp only [(hA _).2, sectorDiagonal_one]
end BlockAlgebra

namespace Folding
open PeriodicYee YeeTaylor

theorem conventionalMomentum_cartesianIncrement (k q : Momentum) :
    conventionalMomentum (k + cartesianIncrement q) = conventionalMomentum k + (2 * Real.pi) • q := by
  ext j
  fin_cases j <;> simp [conventionalMomentum, cartesianIncrement] <;> ring

theorem sectorMomentum_cartesianIncrement (k q : Momentum) (a : Coset) :
    sectorMomentum (k + cartesianIncrement q) a = sectorMomentum k a + cartesianIncrement q := by
  simp only [sectorMomentum]
  abel

/-- The exact full-cell unitary from conventional boundary-phase variables to
the four centered primitive fibers. The Cartesian variable `q` becomes a
conventional angular displacement `2πq`. -/
def centeredFoldingMatrix (k q : Momentum) :=
  foldingMatrix (k + cartesianIncrement q) *
    sectorDiagonal (fun _ : Coset => electricGauge q)

theorem centeredFoldingMatrix_unitary (k q : Momentum) :
    (centeredFoldingMatrix k q).conjTranspose * centeredFoldingMatrix k q = 1 ∧
      centeredFoldingMatrix k q * (centeredFoldingMatrix k q).conjTranspose = 1 := by
  have hF := foldingMatrix_unitary (k + cartesianIncrement q)
  have hG := sectorDiagonal_unitary (fun _ : Coset => electricGauge q)
    (fun _ => electricGauge_unitary q)
  unfold centeredFoldingMatrix
  rw [Matrix.conjTranspose_mul]
  constructor
  · calc
      _ = (sectorDiagonal (fun _ : Coset => electricGauge q)).conjTranspose *
          ((foldingMatrix (k + cartesianIncrement q)).conjTranspose *
            foldingMatrix (k + cartesianIncrement q)) *
            sectorDiagonal (fun _ : Coset => electricGauge q) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hF.1, Matrix.mul_one, hG.1]
  · calc
      _ = foldingMatrix (k + cartesianIncrement q) *
          (sectorDiagonal (fun _ : Coset => electricGauge q) *
            (sectorDiagonal (fun _ : Coset => electricGauge q)).conjTranspose) *
            (foldingMatrix (k + cartesianIncrement q)).conjTranspose := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hG.2, Matrix.mul_one, hF.2]

theorem centered_fiber_folding (material : Cell20 → ℝ) (hmat : FCCPeriodic material)
    (k q : Momentum) :
    (centeredFoldingMatrix k q).conjTranspose *
        PeriodicYee.fiber material (conventionalMomentum k + (2 * Real.pi) • q) *
        centeredFoldingMatrix k q =
      sectorDiagonal (fun a => centeredFiber material (sectorMomentum k a) q) := by
  rw [← conventionalMomentum_cartesianIncrement]
  unfold centeredFoldingMatrix
  rw [Matrix.conjTranspose_mul]
  calc
    _ = (sectorDiagonal (fun _ : Coset => electricGauge q)).conjTranspose *
        ((foldingMatrix (k + cartesianIncrement q)).conjTranspose *
          PeriodicYee.fiber material (conventionalMomentum (k + cartesianIncrement q)) *
          foldingMatrix (k + cartesianIncrement q)) *
        sectorDiagonal (fun _ : Coset => electricGauge q) := by simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [fiber_folding material hmat, sectorDiagonal_conjTranspose,
        sectorDiagonal_mul, sectorDiagonal_mul]
      congr 1
      funext a
      rw [sectorMomentum_cartesianIncrement, centeredFiber_gauge]

theorem concrete_centered_folding (k q : Momentum) :
    (centeredFoldingMatrix k q).conjTranspose *
        PeriodicYee.fiber Concrete.material (conventionalMomentum k + (2 * Real.pi) • q) *
        centeredFoldingMatrix k q =
      sectorDiagonal (fun a => centeredFiber Concrete.material (sectorMomentum k a) q) :=
  centered_fiber_folding Concrete.material Concrete.material_FCCPeriodic k q

theorem centered_fiber_folding_intertwining (material : Cell20 → ℝ)
    (hmat : FCCPeriodic material) (k q : Momentum) :
    PeriodicYee.fiber material (conventionalMomentum k + (2 * Real.pi) • q) *
        centeredFoldingMatrix k q =
      centeredFoldingMatrix k q *
        sectorDiagonal (fun a => centeredFiber material (sectorMomentum k a) q) := by
  rw [← centered_fiber_folding material hmat k q]
  calc
    _ = (centeredFoldingMatrix k q * (centeredFoldingMatrix k q).conjTranspose) *
        PeriodicYee.fiber material (conventionalMomentum k + (2 * Real.pi) • q) *
          centeredFoldingMatrix k q := by rw [(centeredFoldingMatrix_unitary k q).2, Matrix.one_mul]
    _ = _ := by simp only [Matrix.mul_assoc]

end Folding
end
end Maxwell.Spectral
