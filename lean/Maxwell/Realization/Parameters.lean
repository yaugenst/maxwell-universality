import Maxwell.Realization.Precision
import Maxwell.Realization.Buffer
import Maxwell.Probability

/-! Actual rational parameter choices for finite physical composition.
Every precision is selected by a terminating rational comparison, and the
literal composition budgets are consequences of the definitions. -/
namespace Maxwell.Realization

/-- Fixed positive rational bounds chosen once from the certified platform. -/
structure PhysicalConstants where
  gap : ℚ
  rowBound : ℚ
  materialHeadroom : ℚ
  weightMinimum : ℚ
  inverseWeightBound : ℚ
  incrementBound : ℚ
  defectGap : ℚ
  gap_pos : 0 < gap
  rowBound_pos : 0 < rowBound
  materialHeadroom_pos : 0 < materialHeadroom
  weightMinimum_pos : 0 < weightMinimum
  inverseWeightBound_pos : 0 < inverseWeightBound
  incrementBound_pos : 0 < incrementBound
  defectGap_pos : 0 < defectGap

namespace PhysicalConstants

def detuningBudget (P : PhysicalConstants) (ζ : ℚ) : ℚ :=
  min 1 (min (P.gap/4) (min (P.gap^2*ζ^2/16) P.materialHeadroom))

theorem detuningBudget_pos (P : PhysicalConstants) (ζ : ℚ) (hζ : 0 < ζ) :
    0 < P.detuningBudget ζ := by
  have hg := P.gap_pos
  unfold detuningBudget
  exact lt_min (by norm_num) (lt_min (by positivity)
    (lt_min (by positivity) P.materialHeadroom_pos))

def detuningWidth (P : PhysicalConstants) (ζ : ℚ) (hζ : 0 < ζ) : ℚ :=
  precisionUnit (P.detuningBudget ζ) (P.detuningBudget_pos ζ hζ)

theorem detuningWidth_pos (P : PhysicalConstants) (ζ : ℚ) (hζ : 0 < ζ) :
    0 < P.detuningWidth ζ hζ := precisionUnit_pos _ _

/-- The dyadic detuning interval meets every finite-boundary and material
headroom restriction before a random index is drawn. -/
theorem detuningWidth_bounds (P : PhysicalConstants) (ζ : ℚ) (hζ : 0 < ζ) :
    P.detuningWidth ζ hζ ≤ 1 ∧ P.detuningWidth ζ hζ ≤ P.gap/4 ∧
      P.detuningWidth ζ hζ ≤ P.gap^2*ζ^2/16 ∧
      P.detuningWidth ζ hζ ≤ P.materialHeadroom := by
  have h := precisionUnit_le (P.detuningBudget ζ) (P.detuningBudget_pos ζ hζ)
  change P.detuningWidth ζ hζ ≤ _ at h
  unfold detuningBudget at h
  exact ⟨h.trans (min_le_left _ _), h.trans ((min_le_right _ _).trans (min_le_left _ _)),
    h.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))),
    h.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))⟩

/-- A fixed lower constant proves that detuning is within fixed factors of
ζ² whenever0<ζ≤1. -/
def detuningLower (P : PhysicalConstants) : ℚ :=
  min 1 (min (P.gap/4) (min (P.gap^2/16) P.materialHeadroom)) / 2

theorem detuningLower_pos (P : PhysicalConstants) : 0 < P.detuningLower := by
  have hg := P.gap_pos
  have hh := P.materialHeadroom_pos
  unfold detuningLower
  positivity

theorem detuningWidth_lower (P : PhysicalConstants) (ζ : ℚ)
    (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) :
    P.detuningLower * ζ^2 < P.detuningWidth ζ hζ := by
  have hz : ζ^2 ≤ 1 := by nlinarith
  have hb : (2*P.detuningLower)*ζ^2 ≤ P.detuningBudget ζ := by
    have hg := P.gap_pos
    have hh := P.materialHeadroom_pos
    let c := min (1:ℚ) (min (P.gap/4) (min (P.gap^2/16) P.materialHeadroom))
    have hc1 : c ≤ 1 := min_le_left _ _
    have hcg : c ≤ P.gap/4 := (min_le_right _ _).trans (min_le_left _ _)
    have hcg2 : c ≤ P.gap^2/16 :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    have hch : c ≤ P.materialHeadroom :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
    have hc0 : 0 ≤ c := by dsimp [c]; positivity
    have hmul : c*ζ^2 ≤ c := mul_le_of_le_one_right hc0 hz
    change (2*(c/2))*ζ^2 ≤ _
    rw [mul_div_cancel₀ _ (by norm_num : (2:ℚ)≠0)]
    unfold detuningBudget
    apply le_min (hmul.trans hc1)
    apply le_min (hmul.trans hcg)
    apply le_min _ (hmul.trans hch)
    have h := mul_le_mul_of_nonneg_right hcg2 (sq_nonneg ζ)
    convert h using 1
    ring
  have hu := precisionUnit_lower (P.detuningBudget ζ) (P.detuningBudget_pos ζ hζ)
  have he : precisionBudget (P.detuningBudget ζ) = P.detuningBudget ζ := by
    apply min_eq_right
    exact min_le_left _ _
  rw [he] at hu
  change P.detuningBudget ζ / 2 < P.detuningWidth ζ hζ at hu
  linarith

def backgroundInverseBudget (P : PhysicalConstants) (ζ : ℚ) (hζ : 0 < ζ)
    (m N : ℕ) : ℚ := 16 * ((m : ℚ)+N)^2 / P.detuningWidth ζ hζ

theorem backgroundInverseBudget_pos (P : PhysicalConstants) (ζ : ℚ) (hζ : 0 < ζ)
    (m N : ℕ) (hm : 0 < m) : 0 < P.backgroundInverseBudget ζ hζ m N := by
  have hτ := P.detuningWidth_pos ζ hζ
  unfold backgroundInverseBudget
  positivity

/-- The probability theorem and the composition ledger use the identical
inverse budget at the actual final field dimension. -/
theorem backgroundInverseBudget_cast (P : PhysicalConstants) (ζ : ℚ) (hζ : 0 < ζ)
    (m N : ℕ) :
    (P.backgroundInverseBudget ζ hζ m N : ℝ) =
      Probability.inverseBudget m N (P.detuningWidth ζ hζ : ℝ) := by
  simp [backgroundInverseBudget, Probability.inverseBudget]

def modeInverseBudget (P : PhysicalConstants) (K α : ℚ) : ℚ :=
  4*(32*K/α + 2/P.defectGap)

def fullInverseBudget (P : PhysicalConstants) (K α L : ℚ) : ℚ :=
  L + L^2 * P.modeInverseBudget K α

theorem fullInverseBudget_pos (P : PhysicalConstants) (K α L : ℚ)
    (hK : 0 < K) (hα : 0 < α) (hL : 0 < L) : 0 < P.fullInverseBudget K α L := by
  have hg := P.defectGap_pos
  unfold fullInverseBudget modeInverseBudget
  positivity

def residualBudget (P : PhysicalConstants) (ε L : ℚ) : ℚ :=
  ε / (8192*P.rowBound*P.inverseWeightBound*L)

def calibrationBudget (P : PhysicalConstants) (ε α L QA : ℚ) : ℚ :=
  min (P.weightMinimum*ε / (32768*P.rowBound*L))
    (ε / (1024*P.incrementBound*α*P.rowBound*P.inverseWeightBound*QA))

def sourceBudget (α ε L : ℚ) (N : ℕ) : ℚ := α*ε / (32768*L*max 1 (N:ℚ))

def readoutBudget (P : PhysicalConstants) (ε : ℚ) (p : ℕ) : ℚ :=
  ε / (8192*max 1 P.incrementBound*max 1 (p:ℚ))

theorem residualBudget_pos (P : PhysicalConstants) (ε L : ℚ) (hε : 0 < ε) (hL : 0 < L) :
    0 < P.residualBudget ε L := by
  have hJ := P.rowBound_pos
  have hW := P.inverseWeightBound_pos
  unfold residualBudget
  positivity

theorem calibrationBudget_pos (P : PhysicalConstants) (ε α L QA : ℚ)
    (hε : 0 < ε) (hα : 0 < α) (hL : 0 < L) (hQA : 0 < QA) :
    0 < P.calibrationBudget ε α L QA := by
  have hJ := P.rowBound_pos
  have hW := P.inverseWeightBound_pos
  have hv := P.incrementBound_pos
  have hw := P.weightMinimum_pos
  unfold calibrationBudget
  positivity

theorem sourceBudget_pos (α ε L : ℚ) (N : ℕ) (hα : 0 < α) (hε : 0 < ε) (hL : 0 < L) :
    0 < sourceBudget α ε L N := by unfold sourceBudget; positivity

theorem readoutBudget_pos (P : PhysicalConstants) (ε : ℚ) (p : ℕ) (hε : 0 < ε) :
    0 < P.readoutBudget ε p := by unfold readoutBudget; positivity

/-- All scalar precision units are constructed by the same least-bit search. -/
def residualUnit (P : PhysicalConstants) (ε L : ℚ) (hε : 0 < ε) (hL : 0 < L) : ℚ :=
  precisionUnit (P.residualBudget ε L) (P.residualBudget_pos ε L hε hL)

def calibrationUnit (P : PhysicalConstants) (ε α L QA : ℚ)
    (hε : 0 < ε) (hα : 0 < α) (hL : 0 < L) (hQA : 0 < QA) : ℚ :=
  precisionUnit (P.calibrationBudget ε α L QA) (P.calibrationBudget_pos ε α L QA hε hα hL hQA)

def sourceUnit (α ε L : ℚ) (N : ℕ) (hα : 0 < α) (hε : 0 < ε) (hL : 0 < L) : ℚ :=
  precisionUnit (sourceBudget α ε L N) (sourceBudget_pos α ε L N hα hε hL)

def readoutUnit (P : PhysicalConstants) (ε : ℚ) (p : ℕ) (hε : 0 < ε) : ℚ :=
  precisionUnit (P.readoutBudget ε p) (P.readoutBudget_pos ε p hε)

/-- The two calibration requirements hold simultaneously for the selected
unit, including the actual full-Maxwell inverse scale QA. -/
theorem calibrationUnit_bounds (P : PhysicalConstants) (ε α L QA : ℚ)
    (hε : 0 < ε) (hα : 0 < α) (hL : 0 < L) (hQA : 0 < QA) :
    P.calibrationUnit ε α L QA hε hα hL hQA ≤ P.weightMinimum*ε/(32768*P.rowBound*L) ∧
    P.calibrationUnit ε α L QA hε hα hL hQA ≤
      ε/(1024*P.incrementBound*α*P.rowBound*P.inverseWeightBound*QA) := by
  have h := precisionUnit_le (P.calibrationBudget ε α L QA)
    (P.calibrationBudget_pos ε α L QA hε hα hL hQA)
  exact ⟨h.trans (min_le_left _ _), h.trans (min_le_right _ _)⟩

/-- Global source-support accounting: using the actual final dimension N
also bounds every smaller emitted support. -/
theorem sourceUnit_global_bound (α ε L : ℚ) (N p : ℕ) (hp : p ≤ N)
    (hα : 0 < α) (hε : 0 < ε) (hL : 0 < L) :
    (p : ℚ) * sourceUnit α ε L N hα hε hL ≤ α*ε/(32768*L) := by
  have h := precisionUnit_le (sourceBudget α ε L N) (sourceBudget_pos α ε L N hα hε hL)
  have hmax : (p : ℚ) ≤ max 1 (N:ℚ) := (by exact_mod_cast hp : (p:ℚ)≤N).trans (le_max_right _ _)
  have hden : 0 < 32768*L*max 1 (N:ℚ) := by positivity
  have hb := (le_div_iff₀ hden).mp h
  have hu := precisionUnit_pos (sourceBudget α ε L N) (sourceBudget_pos α ε L N hα hε hL)
  change 0 < sourceUnit α ε L N hα hε hL at hu
  change sourceUnit α ε L N hα hε hL * (32768*L*max 1 (N:ℚ)) ≤ α*ε at hb
  apply (le_div_iff₀ (by positivity : (0:ℚ)<32768*L)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hmax hu.le]

/-- The global coordinate-access count controls the complete readout error
when the calibrated mode norm is at most two. -/
theorem readoutUnit_error_bound (P : PhysicalConstants) (ε : ℚ) (p : ℕ) (hε : 0 < ε) :
    2*P.incrementBound*(p:ℚ)*P.readoutUnit ε p hε ≤ ε/4096 := by
  have h := precisionUnit_le (P.readoutBudget ε p) (P.readoutBudget_pos ε p hε)
  have hden : (0:ℚ)<8192*max 1 P.incrementBound*max 1 (p:ℚ) := by positivity
  have hb := (le_div_iff₀ hden).mp h
  have hu := precisionUnit_pos (P.readoutBudget ε p) (P.readoutBudget_pos ε p hε)
  change 0 < P.readoutUnit ε p hε at hu
  change P.readoutUnit ε p hε * (8192*max 1 P.incrementBound*max 1 (p:ℚ)) ≤ ε at hb
  have hv := P.incrementBound_pos
  have hc := mul_le_mul (le_max_right 1 P.incrementBound) (le_max_right 1 (p:ℚ))
    (by positivity : (0:ℚ)≤p) (by positivity : (0:ℚ)≤max 1 P.incrementBound)
  have hm := mul_le_mul_of_nonneg_right hc hu.le
  nlinarith

/-- The buffer is selected before materializing the box, using its cubic
volume formula in the exact rational stopping comparison. -/
def buffer (P : PhysicalConstants) (r C ζ : ℚ) (m s : ℕ)
    (hr : 0 < r) (hr1 : r < 1) (hC : 0 ≤ C) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) : ℕ :=
  Buffer.rationalChoice r P.rowBound P.gap C (P.detuningWidth ζ hζ) ζ m s
    hr hr1 P.rowBound_pos.le P.gap_pos hC (P.detuningWidth_pos ζ hζ)
    (P.detuningWidth_bounds ζ hζ).1 hζ hζ1

/-- Full finite-background approximation budget for the actual selected
buffer and actual final dimension. The only volume premise is the concrete
box's cubic counting inequality. -/
theorem buffer_error_bound (P : PhysicalConstants) (r C ζ : ℚ) (m s N : ℕ)
    (hr : 0 < r) (hr1 : r < 1) (hC : 0 ≤ C) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (μ : ℝ) (htail : Real.exp (-μ) ≤ (r : ℝ))
    (hN : (N : ℝ) ≤ (C : ℝ) * ((s : ℝ) + P.buffer r C ζ m s hr hr1 hC hζ hζ1 + 1)^3) :
    2*(P.detuningWidth ζ hζ : ℝ)/(P.gap : ℝ)^2 +
      (4*(P.rowBound : ℝ)*(P.backgroundInverseBudget ζ hζ m N : ℝ)/(P.gap : ℝ)) *
        Real.exp (-μ*P.buffer r C ζ m s hr hr1 hC hζ hζ1) ≤ (ζ : ℝ)^2 := by
  have ht := Buffer.rationalChoice_feedback_bound r P.rowBound P.gap C
    (P.detuningWidth ζ hζ) ζ m s N hr hr1 P.rowBound_pos.le P.gap_pos hC
    (P.detuningWidth_pos ζ hζ) (P.detuningWidth_bounds ζ hζ).1 hζ hζ1 μ htail hN
  have hs := Buffer.shift_error_bound (P.gap : ℝ) (P.detuningWidth ζ hζ : ℝ) (ζ : ℝ)
    (by exact_mod_cast P.gap_pos) (by exact_mod_cast (P.detuningWidth_bounds ζ hζ).2.2.1)
  change (4*(P.rowBound:ℝ)/(P.gap:ℝ))*(16*((m:ℝ)+N)^2/(P.detuningWidth ζ hζ:ℝ))*
    Real.exp (-μ*P.buffer r C ζ m s hr hr1 hC hζ hζ1) ≤ (ζ:ℝ)^2/2 at ht
  rw [P.backgroundInverseBudget_cast]
  unfold Probability.inverseBudget
  have he : 4*(P.rowBound:ℝ)*(16*((m:ℝ)+N)^2/(P.detuningWidth ζ hζ:ℝ))/(P.gap:ℝ) =
      (4*(P.rowBound:ℝ)/(P.gap:ℝ))*(16*((m:ℝ)+N)^2/(P.detuningWidth ζ hζ:ℝ)) := by ring
  rw [he]
  nlinarith [sq_nonneg (ζ:ℝ)]

/-- The selected dyadic residual tolerance is positive and satisfies the
literal all-solution residual budget. -/
theorem residualUnit_bounds (P : PhysicalConstants) (ε L : ℚ) (hε : 0 < ε) (hL : 0 < L) :
    0 < P.residualUnit ε L hε hL ∧
      P.residualUnit ε L hε hL ≤ ε/(8192*P.rowBound*P.inverseWeightBound*L) :=
  ⟨precisionUnit_pos _ _, precisionUnit_le _ _⟩

theorem calibrationUnit_le_one (P : PhysicalConstants) (ε α L QA : ℚ)
    (hε : 0 < ε) (hα : 0 < α) (hL : 0 < L) (hQA : 0 < QA) :
    P.calibrationUnit ε α L QA hε hα hL hQA ≤ 1 := precisionUnit_le_one _ _

/-- The selected detuning budget has precisely the reciprocal square scale
used in the conditioning exponent ledger. -/
theorem backgroundInverseBudget_scale (P : PhysicalConstants) (ζ : ℚ)
    (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) (m N : ℕ) :
    P.backgroundInverseBudget ζ hζ m N ≤
      (16/P.detuningLower)*((m:ℚ)+N)^2*(ζ⁻¹)^2 := by
  have hl := P.detuningWidth_lower ζ hζ hζ1
  have hlow : 0 < P.detuningLower*ζ^2 := mul_pos P.detuningLower_pos (pow_pos hζ _)
  calc
    _ ≤ 16*((m:ℚ)+N)^2 / (P.detuningLower*ζ^2) :=
      div_le_div_of_nonneg_left (by positivity) hlow hl.le
    _ = _ := by field_simp

end PhysicalConstants
end Maxwell.Realization
