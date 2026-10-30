import Maxwell.Continuum.FiniteAuxiliaryDecomposition
import Maxwell.Composition.SourceDecoration

/-! Literal nearest-neighbor blocks and their identification with the
compiled doubled terminal/midpoint lattice. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.FiniteAuxiliary

open Auxiliary EffectiveMass Maxwell.Composition

variable {ι : Type*} [Fintype ι]

def nearBlocks {L : ℕ} {z : ℝ} (D : Calibration (L : ℝ)⁻¹ z)
    (d : ℕ) (position : ι → Bloch.Alias) (i j : ι) : FieldL2 →L[ℂ] FieldL2 :=
  if latticeOneNorm (position i-position j) = 1 then
    physicalWellBlock D le_rfl (by positivity) d (position i-position j) else 0

theorem offsite_near_far {L : ℕ} {z : ℝ} (D : Calibration (L : ℝ)⁻¹ z)
    (d : ℕ) (position : ι → Bloch.Alias) :
    offsite D d position = blockOperator (nearBlocks D d position)+
      blockOperator (shellBlocks D le_rfl (by positivity) d position 2) := by
  classical
  apply ContinuousLinearMap.ext
  intro f
  apply PiLp.ext
  intro i
  simp only [offsite, add_apply, PiLp.add_apply, blockOperator_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h0 : latticeOneNorm (position i-position j) = 0
  · simp [shellBlocks, nearBlocks, h0]
  · by_cases h1 : latticeOneNorm (position i-position j) = 1
    · simp [shellBlocks, nearBlocks, h1]
    · have h2 : 2 ≤ latticeOneNorm (position i-position j) := by omega
      have hge : 1 ≤ latticeOneNorm (position i-position j) := by omega
      simp [shellBlocks, nearBlocks, h1, h2, hge]

theorem block_bright_matrix {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [DecidableEq ι] (u : H) (A : ι → ι → H →L[ℂ] H) :
    (brightCoefficient u).comp ((blockOperator A).comp (bright u)) =
      Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) (fun i j => inner ℂ u (A i j u)) := by
  apply ContinuousLinearMap.ext
  intro f
  apply PiLp.ext
  intro i
  simp only [ContinuousLinearMap.comp_apply, brightCoefficient_apply, blockOperator_apply,
    bright_apply, map_smul, inner_sum, inner_smul_right]
  change (∑ j, f j*inner ℂ u (A i j u)) = ∑ j, inner ℂ u (A i j u)*f j
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

theorem latticeOneNorm_int (a : Bloch.Alias) :
    (latticeOneNorm a : ℤ) = |a 0|+|a 1|+|a 2| := by
  simp only [latticeOneNorm, Fin.sum_univ_three, Nat.cast_add, Int.natCast_natAbs]

theorem source_nearest_iff (S : Source.SparseSystem) (precision : ℕ)
    (i j : SourceDecoration.Vertex S precision) :
    latticeOneNorm (SourceDecoration.site S precision i-SourceDecoration.site S precision j) = 1 ↔
      SourceDecoration.Incident S precision i j := by
  rw [← SourceDecoration.adjacent_iff_incident, DecoratedLattice.adjacent_iff]
  have he := latticeOneNorm_int (SourceDecoration.site S precision i-SourceDecoration.site S precision j)
  simp only [Pi.sub_apply] at he
  rw [← he]
  exact_mod_cast (Iff.rfl : latticeOneNorm
    (SourceDecoration.site S precision i-SourceDecoration.site S precision j) = 1 ↔
      latticeOneNorm (SourceDecoration.site S precision i-SourceDecoration.site S precision j) = 1)

theorem source_tail_displacement (S : Source.SparseSystem) (precision : ℕ)
    (e : SourceIncidence.E S precision) :
    SourceDecoration.site S precision (.inl e.val.1)-SourceDecoration.site S precision (.inr e) =
      -Pi.single (SourceIncidence.axis S precision e) 1 := by
  rw [SourceDecoration.site, SourceDecoration.site, SourceIncidence.axis_spec S precision e]
  funext k
  simp only [DecoratedLattice.terminal, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
    Pi.neg_apply, smul_eq_mul, Spectral.Lattice.unitSite]
  ring

theorem source_head_displacement (S : Source.SparseSystem) (precision : ℕ)
    (e : SourceIncidence.E S precision) :
    SourceDecoration.site S precision (.inl e.val.2)-SourceDecoration.site S precision (.inr e) =
      Pi.single (SourceIncidence.axis S precision e) 1 := by
  rw [SourceDecoration.site, SourceDecoration.site, SourceIncidence.axis_spec S precision e]
  funext k
  simp only [DecoratedLattice.terminal, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, Spectral.Lattice.unitSite]
  ring

#print axioms offsite_near_far
#print axioms block_bright_matrix
#print axioms source_nearest_iff

end Maxwell.Continuum.FiniteAuxiliary
