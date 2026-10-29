import Maxwell.Spectral.Lattice
import Mathlib.Analysis.InnerProductSpace.Rayleigh

/-! The uniform norm bound for the concrete infinite Yee operator. -/

namespace Maxwell.Spectral

noncomputable section

theorem selfAdjoint_norm_le_of_quadratic
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (A : E →L[ℂ] E) (hA : IsSelfAdjoint A) (R : ℝ) (hR : 0 ≤ R)
    (h : ∀ x, |RCLike.re (inner ℂ (A x) x)| ≤ R * ‖x‖ ^ 2) : ‖A‖ ≤ R := by
  rw [A.norm_eq_iSup_rayleighQuotient hA.isSymmetric]
  apply ciSup_le
  intro x
  by_cases hx : x = 0
  · simpa [hx] using hR
  rw [ContinuousLinearMap.rayleighQuotient,
    ContinuousLinearMap.reApplyInnerSelf_apply, abs_div, abs_sq]
  exact (div_le_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr hx))).mpr (h x)

theorem realSequenceMultiplier_quadratic_nonneg {ι : Type*}
    (m : ι → ℝ) (K : ℝ) (hK : 0 ≤ K) (hm : ∀ i, |m i| ≤ K)
    (hm0 : ∀ i, 0 ≤ m i) (x : SequenceL2 ι) :
    0 ≤ RCLike.re (inner ℂ (realSequenceMultiplier m K hK hm x) x) := by
  rw [lp.inner_eq_tsum, RCLike.re_tsum ℂ (lp.summable_inner _ _)]
  apply tsum_nonneg
  intro i
  change 0 ≤ RCLike.re (inner ℂ ((m i : ℂ) • x i) (x i))
  rw [inner_smul_left]
  change 0 ≤ ((starRingEnd ℂ) (m i : ℂ) * inner ℂ (x i) (x i)).re
  simpa using mul_nonneg (hm0 i) (inner_self_nonneg (𝕜 := ℂ) (x := x i))

theorem realSequenceMultiplier_norm_le_of_bound {ι : Type*}
    (m : ι → ℝ) (K : ℝ) (hK : 0 ≤ K) (hm : ∀ i, |m i| ≤ K)
    (M : ℝ) (hM : 0 ≤ M) (hmM : ∀ i, |m i| ≤ M) :
    ‖realSequenceMultiplier m K hK hm‖ ≤ M := by
  have heq : realSequenceMultiplier m K hK hm = realSequenceMultiplier m M hM hmM := by
    ext x i
    rfl
  rw [heq]
  exact realSequenceMultiplier_norm_le m M hM hmM

namespace Lattice

theorem electricOperator_norm_le (m : Edge → ℝ) (K : ℝ)
    (hK : 0 ≤ K) (hm : ∀ i, |m i| ≤ K)
    (hm0 : ∀ i, 0 ≤ m i) (hm25 : ∀ i, m i ≤ 25) :
    ‖electricOperator m K hK hm‖ ≤ 16 := by
  apply selfAdjoint_norm_le_of_quadratic _ (electricOperator_selfAdjoint m K hK hm)
    16 (by norm_num)
  intro x
  have hD0 := realSequenceMultiplier_quadratic_nonneg m K hK hm hm0 x
  have hDn : ‖realSequenceMultiplier m K hK hm‖ ≤ 25 :=
    realSequenceMultiplier_norm_le_of_bound m K hK hm 25 (by norm_num)
      (fun i => by rw [abs_of_nonneg (hm0 i)]; exact hm25 i)
  have hD : RCLike.re (inner ℂ (realSequenceMultiplier m K hK hm x) x) ≤
      25 * ‖x‖ ^ 2 := by
    calc
      _ ≤ ‖inner ℂ (realSequenceMultiplier m K hK hm x) x‖ := RCLike.re_le_norm _
      _ ≤ ‖realSequenceMultiplier m K hK hm x‖ * ‖x‖ := norm_inner_le_norm _ _
      _ ≤ (25 * ‖x‖) * ‖x‖ := by
        gcongr
        exact (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr)
      _ = _ := by ring
  have hCn : ‖yeeCurl x‖ ≤ 4 * ‖x‖ :=
    (yeeCurl.le_opNorm x).trans (by gcongr; exact yeeCurl_norm_le)
  have hC : ‖yeeCurl x‖ ^ 2 ≤ 16 * ‖x‖ ^ 2 := by nlinarith [norm_nonneg (yeeCurl x)]
  have heq : RCLike.re (inner ℂ (electricOperator m K hK hm x) x) =
      ‖yeeCurl x‖ ^ 2 - (1 / 64 : ℝ) *
        RCLike.re (inner ℂ (realSequenceMultiplier m K hK hm x) x) := by
    simp only [electricOperator, sub_apply, ContinuousLinearMap.comp_apply, smul_apply,
      inner_sub_left, inner_smul_left, map_sub]
    rw [ContinuousLinearMap.adjoint_inner_left]
    simp
    norm_cast
  rw [heq, abs_le]
  constructor <;> nlinarith [sq_nonneg ‖x‖, sq_nonneg ‖yeeCurl x‖]

end Lattice
end
end Maxwell.Spectral
