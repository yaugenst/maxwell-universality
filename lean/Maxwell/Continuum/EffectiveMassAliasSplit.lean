import Maxwell.Continuum.EffectiveMassBandKernel
import Maxwell.Continuum.AliasOperatorBound

/-! Exact separation of the complete alias kernel into the diagonal
Fourier-vector inner product and the already estimated off-alias sum. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.EffectiveMass

open FreeFiber

theorem well_physicalFourier_le (p : Space) : ‖Well.physicalFourier Well.w p‖ ≤ 24 := by
  apply (Well.w_physicalFourier_decay p).trans
  have he : Real.exp (-Real.sqrt ‖p‖ / 64) ≤ 1 := Real.exp_le_one_iff.mpr
    (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Real.sqrt_nonneg _)) (by norm_num))
  nlinarith

theorem fullAliasTerm_summable {h : ℝ} (hh : 0 < h) (p r : Space)
    (hp : p ∈ aliasChart h) (hr : r ∈ aliasChart h) :
    Summable (fun a : Alias × Alias => inner ℂ (scaledFiber h p a.1) (scaledFiber h r a.2) *
      Well.physicalFourier Well.w (aliasTransfer h p r a.1 a.2)) := by
  apply ((aliasWeight_sum hh.le p r ((mem_aliasChart hh p).mp hp)
    ((mem_aliasChart hh r).mp hr)).1.mul_right 24).of_norm_bounded
  intro a
  rw [norm_mul]
  exact mul_le_mul (norm_inner_le_norm _ _) (well_physicalFourier_le _)
    (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))

theorem aliasTransfer_diagonal (h : ℝ) (p r : Space) (ν : Alias) :
    aliasTransfer h p r ν ν = p - r := by
  unfold aliasTransfer
  have hz : Bloch.integerVector (0 : Alias) = 0 := by ext i; simp [Bloch.integerVector]
  rw [sub_self, hz, smul_zero, add_zero]

theorem fullAliasKernel_split {h : ℝ} (hh : 0 < h) (p r : Space)
    (hp : p ∈ aliasChart h) (hr : r ∈ aliasChart h) :
    fullAliasKernel h p r = inner ℂ (scaledFiber h p) (scaledFiber h r) *
      Well.physicalFourier Well.w (p-r) + offAliasKernel h p r := by
  let F : Alias × Alias → ℂ := fun a =>
    inner ℂ (scaledFiber h p a.1) (scaledFiber h r a.2) *
      Well.physicalFourier Well.w (aliasTransfer h p r a.1 a.2)
  let G : Alias × Alias → ℂ := fun a => if a.1 = a.2 then F a else 0
  have hF : Summable F := fullAliasTerm_summable hh p r hp hr
  have hG : Summable G := by
    apply hF.norm.of_norm_bounded
    intro a
    dsimp only [G]
    split_ifs
    · exact le_rfl
    · simpa only [norm_zero] using norm_nonneg (F a)
  have hO := offAliasTerm_summable hh p r ((mem_aliasChart hh p).mp hp)
    ((mem_aliasChart hh r).mp hr)
  have hsplit : F = fun a => G a + offAliasTerm h p r a := by
    funext a
    dsimp only [F, G, offAliasTerm]
    split_ifs <;> simp only [add_zero, zero_add]
  change ∑' a, F a = _
  rw [hsplit, hG.tsum_add hO]
  congr 1
  rw [hG.tsum_prod]
  have hrow (ν : Alias) : (∑' μ, G (ν,μ)) =
      inner ℂ (scaledFiber h p ν) (scaledFiber h r ν) * Well.physicalFourier Well.w (p-r) := by
    simp only [G, F]
    rw [tsum_eq_single ν]
    · simp only [ite_true, aliasTransfer_diagonal]
    · intro μ hμ
      simp only [Ne.symm hμ, ite_false]
  simp_rw [hrow]
  rw [tsum_mul_right, lp.inner_eq_tsum]

def diagonalAliasKernel (h z : ℝ) (p r : Space) : ℂ :=
  (fourierNormalization : ℂ) * (cutoffBandMultiplier h z p : ℂ) *
    (inner ℂ (scaledFiber h p) (scaledFiber h r) * Well.physicalFourier Well.w (p-r)) *
      (cutoffBandMultiplier h z r : ℂ)

theorem weightedFullAliasKernel_split {h z : ℝ} (hh : 0 < h) (p r : Space)
    (hp : p ∈ aliasChart h) (hr : r ∈ aliasChart h) :
    weightedFullAliasKernel h z p r = diagonalAliasKernel h z p r + weightedOffAliasKernel h z p r := by
  rw [weightedFullAliasKernel, fullAliasKernel_split hh p r hp hr]
  simp only [diagonalAliasKernel, weightedOffAliasKernel, fourierNormalization, Complex.real_smul]
  ring

#print axioms fullAliasKernel_split
#print axioms weightedFullAliasKernel_split

end Maxwell.Continuum.EffectiveMass
