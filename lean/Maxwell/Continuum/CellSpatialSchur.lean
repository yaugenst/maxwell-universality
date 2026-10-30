import Maxwell.Continuum.CellSpatialFamily

/-! A finite block estimate for the actual orthogonal spatial cells.
The loss is the geometric mean of the two cell counts, rather than the
number of pairs. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.CellGauge

open Bloch
open scoped InnerProduct

theorem cellProjection_apply_idempotent (a : Bloch.Alias) (f : FieldL2) :
    cellProjection a (cellProjection a f) = cellProjection a f :=
  congrArg (fun T : FieldL2 →L[ℂ] FieldL2 => T f) (cellProjection_idempotent a)

theorem cellProjection_inner (a : Bloch.Alias) (f g : FieldL2) :
    inner ℂ (cellProjection a f) g = inner ℂ f (cellProjection a g) :=
  (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (cellProjection_selfAdjoint a)) f g

theorem family_block_pairing (F G : Finset Bloch.Alias) (T : FieldL2 →L[ℂ] FieldL2)
    (g f : FieldL2) :
    inner ℂ g (familyProjection F (T (familyProjection G f))) =
      ∑ a ∈ F, ∑ b ∈ G, inner ℂ (cellProjection a g) (T (cellProjection b f)) := by
  rw [familyProjection_apply, inner_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [← cellProjection_inner, familyProjection_apply, map_sum, inner_sum]

theorem cell_block_inner_bound (T : FieldL2 →L[ℂ] FieldL2) (a b : Bloch.Alias)
    {M : ℝ} (hT : ‖(cellProjection a).comp (T.comp (cellProjection b))‖ ≤ M)
    (g f : FieldL2) :
    ‖inner ℂ (cellProjection a g) (T (cellProjection b f))‖ ≤
      M * ‖cellProjection a g‖ * ‖cellProjection b f‖ := by
  have hi := cellProjection_inner a (cellProjection a g) (T (cellProjection b f))
  rw [cellProjection_apply_idempotent] at hi
  rw [hi]
  have hb := ((cellProjection a).comp (T.comp (cellProjection b))).le_of_opNorm_le hT
    (cellProjection b f)
  simp only [ContinuousLinearMap.comp_apply, cellProjection_apply_idempotent] at hb
  calc
    _ ≤ ‖cellProjection a g‖ * ‖cellProjection a (T (cellProjection b f))‖ :=
      norm_inner_le_norm _ _
    _ ≤ ‖cellProjection a g‖ * (M * ‖cellProjection b f‖) :=
      mul_le_mul_of_nonneg_left hb (norm_nonneg _)
    _ = _ := by ring

theorem family_block_inner_bound (F G : Finset Bloch.Alias) (T : FieldL2 →L[ℂ] FieldL2)
    {M : ℝ} (hM : 0 ≤ M)
    (hT : ∀ a ∈ F, ∀ b ∈ G, ‖(cellProjection a).comp (T.comp (cellProjection b))‖ ≤ M)
    (g f : FieldL2) :
    ‖inner ℂ g (familyProjection F (T (familyProjection G f)))‖ ≤
      (M * Real.sqrt (F.card : ℝ) * Real.sqrt (G.card : ℝ)) * ‖g‖ * ‖f‖ := by
  rw [family_block_pairing]
  calc
    _ ≤ ∑ a ∈ F, ∑ b ∈ G,
        ‖inner ℂ (cellProjection a g) (T (cellProjection b f))‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => norm_sum_le _ _)
    _ ≤ ∑ a ∈ F, ∑ b ∈ G, M * ‖cellProjection a g‖ * ‖cellProjection b f‖ :=
      Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun b hb =>
        cell_block_inner_bound T a b (hT a ha b hb) g f
    _ = M * (∑ a ∈ F, ‖cellProjection a g‖) * (∑ b ∈ G, ‖cellProjection b f‖) := by
      simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
      rw [Finset.sum_comm]
    _ ≤ M * (Real.sqrt (F.card : ℝ) * ‖g‖) * (Real.sqrt (G.card : ℝ) * ‖f‖) := by
      gcongr
      · exact familyProjection_sum_norm_le F g
      · exact familyProjection_sum_norm_le G f
    _ = _ := by ring

theorem family_block_norm_le (F G : Finset Bloch.Alias) (T : FieldL2 →L[ℂ] FieldL2)
    {M : ℝ} (hM : 0 ≤ M)
    (hT : ∀ a ∈ F, ∀ b ∈ G, ‖(cellProjection a).comp (T.comp (cellProjection b))‖ ≤ M) :
    ‖(familyProjection F).comp (T.comp (familyProjection G))‖ ≤
      M * Real.sqrt (F.card : ℝ) * Real.sqrt (G.card : ℝ) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro f
  let y := familyProjection F (T (familyProjection G f))
  have hb := family_block_inner_bound F G T hM hT y f
  change ‖inner ℂ y y‖ ≤ _ at hb
  rw [inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal,
    abs_of_nonneg (norm_nonneg y)] at hb
  change ‖y‖ ≤ _
  have hC : 0 ≤ M * Real.sqrt (F.card : ℝ) * Real.sqrt (G.card : ℝ) := by positivity
  by_contra hn
  have hlt := lt_of_not_ge hn
  have hy : 0 < ‖y‖ := lt_of_le_of_lt (mul_nonneg hC (norm_nonneg f)) hlt
  nlinarith

theorem family_block_norm_le_count (F G : Finset Bloch.Alias) (T : FieldL2 →L[ℂ] FieldL2)
    {M N : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hF : (F.card : ℝ) ≤ N) (hG : (G.card : ℝ) ≤ N)
    (hT : ∀ a ∈ F, ∀ b ∈ G, ‖(cellProjection a).comp (T.comp (cellProjection b))‖ ≤ M) :
    ‖(familyProjection F).comp (T.comp (familyProjection G))‖ ≤ M * N := by
  apply (family_block_norm_le F G T hM hT).trans
  calc
    _ ≤ M * Real.sqrt N * Real.sqrt N := by gcongr
    _ = M * N := by rw [mul_assoc, ← pow_two, Real.sq_sqrt hN]

#print axioms family_block_norm_le
#print axioms family_block_norm_le_count

end Maxwell.Continuum.CellGauge
