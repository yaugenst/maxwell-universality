import Maxwell.Continuum.CalibrationSupercellTransport
import Maxwell.Continuum.CalibrationSupercellWellCompression

/-! The range of the supercell Fourier embedding is exactly the L²
fields on its physical cells. In particular it contains every well field. -/

noncomputable section
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.Calibration.Supercell

open FreeFiber CellGauge CellBandFourier PeriodicSampling Auxiliary Bloch EffectiveMass MeasureTheory

variable (M : ℕ) [NeZero M]

theorem cellPhase_orthogonality (a b : Grid M) :
    (∑ j : Grid M, cellPhase M j (representative M a)*star (cellPhase M j (representative M b)))=
      if a=b then (M : ℂ)^3 else 0 := by
  classical
  have hc : (∑ j : Grid M, star (Product.character M b j)*Product.character M a j)=
      if b=a then (M : ℂ)^3 else 0 := by
    convert character_orthogonality M b a using 1
    apply Finset.sum_congr rfl
    intro j _
    rw [character_comm M b j,character_comm M a j]
  simp only [cellPhase,frequency_representative,star_mul]
  calc
    _ = (carrier (latticeShift (representative M a))*star (carrier (latticeShift (representative M b))))*
        ∑ j : Grid M, star (Product.character M b j)*Product.character M a j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by
      rw [hc]
      by_cases hab : a=b
      · subst b
        rw [ite_eq_left rfl,Complex.star_def,
          ← Complex.inv_eq_conj (carrier_norm _),mul_inv_cancel₀,one_mul]
        intro hz
        have hn := carrier_norm (latticeShift (representative M a))
        rw [hz,norm_zero] at hn
        norm_num at hn
      · rw [ite_eq_right (Ne.symm hab),ite_eq_right hab,mul_zero]

theorem blockEmbedding_analysis (f : FieldL2) :
    blockEmbedding M (blockAnalysis M f)=
      ∑ a : Grid M, embedLatticeCell (representative M a)
        (restrictLatticeCell (representative M a) f) := by
  rw [blockEmbedding_apply]
  simp only [blockAnalysis,map_smul,map_sum,LinearIsometryEquiv.apply_symm_apply,
    Finset.smul_sum,smul_smul]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  calc
    _ = ∑ b : Grid M,
        ((8 : ℂ)*(physicalFactor M : ℂ)^2*
          ∑ j : Grid M, cellPhase M j (representative M a)*star (cellPhase M j (representative M b))) •
        embedLatticeCell (representative M a) (restrictLatticeCell (representative M b) f) := by
      simp only [Finset.mul_sum,Finset.sum_smul]
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      ring
    _ = _ := by
      simp only [cellPhase_orthogonality,mul_ite,mul_zero,ite_smul,zero_smul]
      rw [Finset.sum_ite_eq]
      simp only [Finset.mem_univ,ite_eq_left]
      rw [physicalFactor_volume,inv_mul_cancel₀,one_smul]
      exact pow_ne_zero 3 (by exact_mod_cast NeZero.ne M : (M : ℂ)≠0)

def representedCells : Finset Bloch.Alias :=
  Finset.univ.map ⟨representative M,representative_injective M⟩

theorem representedProjection_apply (f : FieldL2) :
    familyProjection (representedCells M) f=
      ∑ a : Grid M, embedLatticeCell (representative M a)
        (restrictLatticeCell (representative M a) f) := by
  rw [familyProjection_apply,representedCells,Finset.sum_map]
  rfl

theorem embedding_range_projection (f : FieldL2) :
    embedding M ((embedding M).toContinuousLinearMap.adjoint f)=
      familyProjection (representedCells M) f := by
  rw [embedding_adjoint,embedding_apply,LinearIsometryEquiv.apply_symm_apply,
    blockEmbedding_analysis,representedProjection_apply]

theorem familyProjection_subset_apply {s t : Finset Bloch.Alias} (hst : s⊆t) (f : FieldL2) :
    familyProjection t (familyProjection s f)=familyProjection s f := by
  classical
  apply PiLp.ext
  intro j
  apply Lp.ext
  filter_upwards [familyProjection_ae t (familyProjection s f) j,familyProjection_ae s f j]
    with x ht hs
  rw [ht]
  by_cases hx : cellIndex x∈t
  · rw [ite_eq_left hx]
  · rw [ite_eq_right hx,hs,ite_eq_right (fun h => hx (hst h))]

theorem ballCells_subset_represented {L : ℝ} (hL : 1≤L) (hM : 16*(L+1)≤(M : ℝ)) :
    ballCells L⊆representedCells M := by
  intro a ha
  exact Finset.mem_map.mpr ⟨Product.frequency M a,Finset.mem_univ _,
    ballCells_representative M hL hM ha⟩

theorem embedding_range_Qh {L : ℝ} (hL : 1≤L) (hM : 16*(L+1)≤(M : ℝ)) (f : FieldL2) :
    embedding M ((embedding M).toContinuousLinearMap.adjoint (Qh L⁻¹ f))=Qh L⁻¹ f := by
  rw [embedding_range_projection]
  have hi : familyProjection (ballCells L) (Qh L⁻¹ f)=Qh L⁻¹ f :=
    congrArg (fun T : FieldL2 →L[ℂ] FieldL2 => T f) (familyProjection_Qh (by linarith : 0<L))
  have h := familyProjection_subset_apply (ballCells_subset_represented M hL hM) (Qh L⁻¹ f)
  rw [hi] at h
  exact h

#print axioms embedding_range_projection
#print axioms embedding_range_Qh

end Maxwell.Continuum.Calibration.Supercell
