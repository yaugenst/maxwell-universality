import Maxwell.Continuum.CellSpatialFamily

/-! Normalized embedding of a finite array of distinct physical cells.
The normalization is derived from the literal volume-eight cells. -/

noncomputable section

namespace Maxwell.Continuum.Calibration.Supercell

open CellGauge CellBandFourier Bloch
open scoped InnerProduct

theorem restrict_embed_cell (f : CellFieldL2) : restrictCell (embedCell f)=f := by
  have h (g : PhysicalCellL2) : restrictField (extendField g)=g := by
    apply PiLp.ext
    intro j
    exact restrict_extend (g j)
  change spatialUnitary (restrictField (extendField (spatialUnitary.symm f)))=f
  rw [h,LinearIsometryEquiv.apply_symm_apply]

theorem restrict_embed_lattice (a : Bloch.Alias) (f : CellFieldL2) :
    restrictLatticeCell a (embedLatticeCell a f)=f := by
  change restrictCell (fieldTranslation (latticeShift a)
    (fieldTranslation (-latticeShift a) (embedCell f)))=f
  rw [fieldTranslation_neg_apply,restrict_embed_cell]

theorem projection_embed_lattice (a : Bloch.Alias) (f : CellFieldL2) :
    cellProjection a (embedLatticeCell a f)=embedLatticeCell a f := by
  change embedLatticeCell a (restrictLatticeCell a (embedLatticeCell a f))=_
  rw [restrict_embed_lattice]

theorem embed_lattice_orthogonal {a b : Bloch.Alias} (hab : a≠b) (f g : CellFieldL2) :
    inner ℂ (embedLatticeCell a f) (embedLatticeCell b g)=0 := by
  have h := cellProjection_orthogonal hab (embedLatticeCell a f) (embedLatticeCell b g)
  simpa only [projection_embed_lattice] using h

variable {ι : Type*} [Fintype ι]

def cellArrayEmbed (a : ι → Bloch.Alias) :
    PiLp 2 (fun _ : ι => CellFieldL2) →L[ℂ] FieldL2 :=
  ∑ i, (embedLatticeCell (a i)).comp (PiLp.proj 2 _ i)

theorem cellArrayEmbed_apply (a : ι → Bloch.Alias) (u : PiLp 2 (fun _ : ι => CellFieldL2)) :
    cellArrayEmbed a u=∑ i, embedLatticeCell (a i) (u i) := by
  simp only [cellArrayEmbed,sum_apply,ContinuousLinearMap.comp_apply,PiLp.proj_apply]

theorem cellArrayEmbed_norm_sq (a : ι → Bloch.Alias) (ha : Function.Injective a)
    (u : PiLp 2 (fun _ : ι => CellFieldL2)) : ‖cellArrayEmbed a u‖^2=8*‖u‖^2 := by
  classical
  have hi : inner ℂ (cellArrayEmbed a u) (cellArrayEmbed a u)=
      ∑ i, inner ℂ (embedLatticeCell (a i) (u i)) (embedLatticeCell (a i) (u i)) := by
    rw [cellArrayEmbed_apply,sum_inner]
    apply Finset.sum_congr rfl
    intro i _
    rw [inner_sum]
    apply Finset.sum_eq_single i
    · intro j _ hji
      exact embed_lattice_orthogonal (fun h => hji (ha h.symm)) (u i) (u j)
    · simp
  rw [norm_sq_eq_re_inner (𝕜 := ℂ),hi,RCLike.re_eq_complex_re,Complex.re_sum,
    PiLp.norm_sq_eq_of_L2,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  change RCLike.re (inner ℂ (embedLatticeCell (a i) (u i))
    (embedLatticeCell (a i) (u i)))=8*‖u i‖^2
  rw [← norm_sq_eq_re_inner (𝕜 := ℂ),embedLatticeCell_norm_sq]

def cellFactor : ℝ := (Real.sqrt 8)⁻¹

theorem cellFactor_pos : 0<cellFactor := by unfold cellFactor; positivity

theorem cellFactor_square : cellFactor^2*8=1 := by
  rw [cellFactor,inv_pow,Real.sq_sqrt (by norm_num : (0 : ℝ)≤8)]
  norm_num

def normalizedCellEmbed (a : ι → Bloch.Alias) :
    PiLp 2 (fun _ : ι => CellFieldL2) →L[ℂ] FieldL2 :=
  (cellFactor : ℂ) • cellArrayEmbed a

theorem normalizedCellEmbed_norm (a : ι → Bloch.Alias) (ha : Function.Injective a)
    (u : PiLp 2 (fun _ : ι => CellFieldL2)) : ‖normalizedCellEmbed a u‖=‖u‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [normalizedCellEmbed,smul_apply,norm_smul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos cellFactor_pos,mul_pow,cellArrayEmbed_norm_sq a ha,← mul_assoc,cellFactor_square,one_mul]

def cellEmbedding (a : ι → Bloch.Alias) (ha : Function.Injective a) :
    PiLp 2 (fun _ : ι => CellFieldL2) →ₗᵢ[ℂ] FieldL2 where
  toLinearMap := (normalizedCellEmbed a).toLinearMap
  norm_map' := normalizedCellEmbed_norm a ha

#print axioms cellEmbedding

end Maxwell.Continuum.Calibration.Supercell
