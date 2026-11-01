import Maxwell.Continuum.ParameterOuterOperandBounds

namespace Maxwell.Continuum.Parameters.OuterMachine
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.SelectedParameters
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
attribute [local irreducible] SpacingMachine.formulas BufferMachine.formulas prepareTau prepareSpans tailPrepare

def stageWidthCoefficient : ℕ := 37*SpacingMachine.widthCoefficient+36*2^prepareTau.length+
  (200+144*2^prepareTau.length)+36*2^prepareSpans.length+1402*BufferMachine.widthCoefficient+
  36*2^tailPrepare.length+4

theorem stage_width_bound (D : Data) (hD : D.Positive) (e k K : ℕ)
    (hk : k ≤ K) (hd : stageSpacing (D.input hD) e k ≤ K)
    (ht : stageBuffer (D.input hD) e k ≤ K) (hL : stageLength k ≤ K) :
    stageWidth D hD e k ≤ stageWidthCoefficient*(sourceWidth D+K+1) := by
  let X := sourceWidth D+K+1
  have hX : 1 ≤ X := by unfold X;omega
  have hK : K ≤ X := by unfold X;omega
  have hb : baseWidth D hD e k ≤ 35*X := by
    have h := baseWidth_bound D hD e k
    unfold X;omega
  have hbb : bufferWidth D hD e k ≤ 1400*X := by
    have h := bufferWidth_bound D hD e k
    unfold X;omega
  have hN : tauSteps D hD e k ≤ 41*X := by
    have h := tauSteps_bound D hD e k
    unfold X;omega
  have htau : tauInputWidth (baseWidth D hD e k) ≤ (36*2^prepareTau.length)*X := by
    unfold tauInputWidth
    have h := Nat.mul_le_mul_left (2^prepareTau.length) (show baseWidth D hD e k+1 ≤ 36*X by omega)
    nlinarith only [h]
  have hspan : spanInputWidth (baseWidth D hD e k) ≤ (36*2^prepareSpans.length)*X := by
    unfold spanInputWidth
    have h := Nat.mul_le_mul_left (2^prepareSpans.length) (show baseWidth D hD e k+1 ≤ 36*X by omega)
    nlinarith only [h]
  have htail : tailInputWidth (baseWidth D hD e k) ≤ (36*2^tailPrepare.length)*X := by
    unfold tailInputWidth
    have h := Nat.mul_le_mul_left (2^tailPrepare.length) (show baseWidth D hD e k+1 ≤ 36*X by omega)
    nlinarith only [h]
  have hs : SpacingMachine.width (spacingSteps D hD e k) (baseWidth D hD e k) ≤
      (37*SpacingMachine.widthCoefficient)*X := by
    have h := SpacingMachine.width_bound (spacingSteps D hD e k) (baseWidth D hD e k)
    have he : 2^(spacingSteps D hD e k)=stageSpacing (D.input hD) e k := rfl
    rw [he] at h
    have hm := Nat.mul_le_mul_left SpacingMachine.widthCoefficient
      (show stageSpacing (D.input hD) e k+baseWidth D hD e k+1 ≤ 37*X by omega)
    nlinarith only [h,hm]
  have hbsearch : BufferMachine.width (bufferSteps D hD e k) (bufferWidth D hD e k) ≤
      (1402*BufferMachine.widthCoefficient)*X := by
    have h := BufferMachine.width_bound (bufferSteps D hD e k) (bufferWidth D hD e k)
    have he : 2^(bufferSteps D hD e k)=stageBuffer (D.input hD) e k := rfl
    rw [he] at h
    have hm := Nat.mul_le_mul_left BufferMachine.widthCoefficient
      (show stageBuffer (D.input hD) e k+bufferWidth D hD e k+1 ≤ 1402*X by omega)
    nlinarith only [h,hm]
  have hts : OuterTau.width (tauSteps D hD e k) (tauInputWidth (baseWidth D hD e k)) ≤
      (200+144*2^prepareTau.length)*X := by
    apply max_le
    · have h := GeometricAdapter.result_width_bound (tauSteps D hD e k) 2 (tauInputWidth (baseWidth D hD e k))
      nlinarith only [h,hN,htau,hX]
    · nlinarith only [hN,hX,Nat.zero_le (2^prepareTau.length*X)]
  have hu : 2^k ≤ X := (Nat.pow_le_pow_left (by decide : 2 ≤ 8) k).trans (hL.trans hK)
  dsimp only [stageWidth]
  change _ ≤ stageWidthCoefficient*X
  unfold stageWidthCoefficient
  nlinarith only [hs,htau,hts,hspan,hbsearch,htail,hu,hL,hK,hX]

theorem loop_width_bound (D : Data) (hD : D.Positive) (e base ℓ B K : ℕ) (hℓ : 0<ℓ)
    (hK : ∀n,n ≤ selectedOuterSteps (D.input hD) e base ℓ hℓ→
      let k := initialExponent base ℓ+n
      k ≤ K ∧ stageSpacing (D.input hD) e k ≤ K ∧ stageBuffer (D.input hD) e k ≤ K ∧ stageLength k ≤ K) :
    loopWidth D hD e base ℓ B hℓ ≤ B+(K+1)*stageWidthCoefficient*(sourceWidth D+K+1) := by
  have hlast := (hK _ le_rfl).1
  have hcount : selectedOuterSteps (D.input hD) e base ℓ hℓ+1 ≤ K+1 := by omega
  unfold loopWidth
  apply Nat.add_le_add_left
  calc
    _ ≤ ∑_n∈Finset.range (selectedOuterSteps (D.input hD) e base ℓ hℓ+1),
        stageWidthCoefficient*(sourceWidth D+K+1) := by
      apply Finset.sum_le_sum
      intro n hn
      obtain ⟨hk,hd,ht,hl⟩ := hK n (by have := Finset.mem_range.mp hn;omega)
      exact stage_width_bound D hD e _ K hk hd ht hl
    _ = (selectedOuterSteps (D.input hD) e base ℓ hℓ+1)*(stageWidthCoefficient*(sourceWidth D+K+1)) := by simp
    _ ≤ (K+1)*(stageWidthCoefficient*(sourceWidth D+K+1)) := Nat.mul_le_mul_right _ hcount
    _ = _ := by ring

#print axioms loop_width_bound
end Maxwell.Continuum.Parameters.OuterMachine
