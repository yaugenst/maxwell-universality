import Maxwell.Continuum.CalibrationSupercellEmbedding

/-! The adjoint of the physical supercell embedding, with the actual
cell restriction and the exact volume factor. -/

noncomputable section

namespace Maxwell.Continuum.Calibration.Supercell

open FreeFiber CellGauge CellBandFourier PeriodicSampling
open scoped InnerProduct

variable (M : ℕ) [NeZero M]

theorem restrict_embed_ne {a b : Alias} (hab : a≠b) (f : CellFieldL2) :
    restrictLatticeCell a (embedLatticeCell b f)=0 := by
  apply ext_inner_left ℂ
  intro g
  rw [inner_zero_right]
  have h := embedLatticeCell_pairing a g (embedLatticeCell b f)
  rw [embed_lattice_orthogonal hab] at h
  exact (mul_eq_zero.mp h.symm).resolve_left (by norm_num)

theorem restrict_blockEmbedding (a : Grid M) (u : BlockSpace M) :
    restrictLatticeCell (representative M a) (blockEmbedding M u)=
      (physicalFactor M : ℂ) • ∑ j : Grid M,
        cellPhase M j (representative M a) • cellUnitary M j (u j) := by
  classical
  rw [blockEmbedding_apply,map_smul,map_sum]
  congr 1
  rw [Finset.sum_eq_single a]
  · simp only [map_sum,map_smul,restrict_embed_lattice]
  · intro b _ hba
    have hab : representative M a≠representative M b :=
      fun h => hba ((representative_injective M) h).symm
    simp only [map_sum,map_smul,restrict_embed_ne hab,smul_zero,Finset.sum_const_zero]
  · simp

def blockAnalysis (f : FieldL2) : BlockSpace M :=
  WithLp.toLp 2 (fun j => ((8 : ℂ)*(physicalFactor M : ℂ)) •
    ∑ a : Grid M, star (cellPhase M j (representative M a)) •
      (cellUnitary M j).symm (restrictLatticeCell (representative M a) f))

omit [NeZero M] in
theorem cellUnitary_pairing (j : Grid M) (u : FiberSpace) (f : CellFieldL2) :
    inner ℂ (cellUnitary M j u) f=inner ℂ u ((cellUnitary M j).symm f) := by
  rw [← (cellUnitary M j).inner_map_map u ((cellUnitary M j).symm f),
    LinearIsometryEquiv.apply_symm_apply]

theorem blockEmbedding_pairing (u : BlockSpace M) (f : FieldL2) :
    inner ℂ (blockEmbedding M u) f=inner ℂ u (blockAnalysis M f) := by
  have hc : star (physicalFactor M : ℂ)=(physicalFactor M : ℂ) := Complex.conj_ofReal _
  rw [blockEmbedding_apply,inner_smul_left,sum_inner,PiLp.inner_apply]
  simp only [sum_inner,inner_smul_left,embedLatticeCell_pairing,cellUnitary_pairing,
    blockAnalysis,inner_smul_right,inner_sum,starRingEnd_apply,hc,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem blockEmbedding_adjoint (f : FieldL2) :
    (blockEmbedding M).toContinuousLinearMap.adjoint f=blockAnalysis M f := by
  apply ext_inner_left ℂ
  intro u
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact blockEmbedding_pairing M u f

theorem blockAnalysis_embed (a : Grid M) (f : CellFieldL2) (j : Grid M) :
    blockAnalysis M (embedLatticeCell (representative M a) f) j=
      ((8 : ℂ)*(physicalFactor M : ℂ)*star (cellPhase M j (representative M a))) •
        (cellUnitary M j).symm f := by
  classical
  change ((8 : ℂ)*(physicalFactor M : ℂ)) • (∑ b : Grid M,
    star (cellPhase M j (representative M b)) • (cellUnitary M j).symm
      (restrictLatticeCell (representative M b) (embedLatticeCell (representative M a) f)))=_
  rw [Finset.sum_eq_single a]
  · rw [restrict_embed_lattice,smul_smul]
  · intro b _ hba
    have hab : representative M b≠representative M a :=
      fun h => hba ((representative_injective M) h)
    rw [restrict_embed_ne hab,map_zero,smul_zero]
  · simp

#print axioms blockEmbedding_adjoint
#print axioms restrict_blockEmbedding

end Maxwell.Continuum.Calibration.Supercell
