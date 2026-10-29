import Maxwell.SchurBound
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Euclidean bounds for the actual rectangular sparse saddle reduction.
The Gram inverse is used only in the proof; the emitted matrix stays sparse. -/
noncomputable section
namespace Maxwell.Composition.RectangularSaddle
open scoped InnerProduct
variable {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H]

def gram (F : E →L[ℝ] H) : E →L[ℝ] E := F.adjoint.comp F

theorem gram_inner (F : E →L[ℝ] H) (x y : E) :
    inner ℝ x (gram F y) = inner ℝ (F x) (F y) :=
  F.adjoint_inner_right x (F y)

theorem gram_injective (F : E →L[ℝ] H) (hF : Function.Injective F) :
    Function.Injective (gram F) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  change gram F x = 0 at hx
  have hh : inner ℝ (F x) (F x) = 0 := by
    rw [← gram_inner, hx, inner_zero_right]
  exact hF (by simpa using (inner_self_eq_zero.mp hh))

def gramEquiv (F : E →L[ℝ] H) (hF : Function.Injective F) : E ≃L[ℝ] E :=
  (LinearEquiv.ofBijective (gram F).toLinearMap
    ⟨gram_injective F hF, LinearMap.injective_iff_surjective.mp (gram_injective F hF)⟩).toContinuousLinearEquiv

@[simp] theorem gramEquiv_apply (F : E →L[ℝ] H) (hF : Function.Injective F) (x : E) :
    gramEquiv F hF x = gram F x := rfl

theorem gramEquiv_inverse_bound (F : E →L[ℝ] H) (hF : Function.Injective F)
    (L : ℝ) (_hL : 0 ≤ L) (hlower : ∀ x, ‖x‖ ≤ L * ‖F x‖) :
    ‖((gramEquiv F hF).symm : E →L[ℝ] E)‖ ≤ L^2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (sq_nonneg L)
  intro y
  let x := (gramEquiv F hF).symm y
  have hg : gram F x = y := (gramEquiv F hF).apply_symm_apply y
  have hnorm : ‖F x‖^2 ≤ ‖x‖ * ‖y‖ := by
    rw [← real_inner_self_eq_norm_sq, ← gram_inner, hg]
    exact real_inner_le_norm _ _
  have hlow := pow_le_pow_left₀ (norm_nonneg x) (hlower x) 2
  rw [mul_pow] at hlow
  change ‖x‖ ≤ L^2 * ‖y‖
  by_cases hx : ‖x‖ = 0
  · rw [hx]; positivity
  · have hx0 : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg x) (Ne.symm hx)
    have hh := mul_le_mul_of_nonneg_left hnorm (sq_nonneg L)
    nlinarith

theorem gram_left_inverse_bound (F : E →L[ℝ] H) (hF : Function.Injective F)
    (L : ℝ) (hL : 0 ≤ L) (hlower : ∀ x, ‖x‖ ≤ L * ‖F x‖) (y : E) :
    ‖F ((gramEquiv F hF).symm y)‖ ≤ L * ‖y‖ := by
  let x := (gramEquiv F hF).symm y
  have hg : gram F x = y := (gramEquiv F hF).apply_symm_apply y
  have hn : ‖F x‖^2 ≤ ‖x‖ * ‖y‖ := by
    rw [← real_inner_self_eq_norm_sq, ← gram_inner, hg]
    exact real_inner_le_norm _ _
  have hb := mul_le_mul_of_nonneg_right (hlower x) (norm_nonneg y)
  change ‖F x‖ ≤ L * ‖y‖
  by_cases hx : ‖F x‖ = 0
  · rw [hx]; positivity
  · have hx0 : 0 < ‖F x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hx)
    nlinarith

def projection (F : E →L[ℝ] H) (hF : Function.Injective F) : H →L[ℝ] H :=
  F.comp (((gramEquiv F hF).symm : E →L[ℝ] E).comp F.adjoint)

theorem projection_residual_orthogonal (F : E →L[ℝ] H) (hF : Function.Injective F)
    (y : H) (x : E) : inner ℝ (F x) (y - projection F hF y) = 0 := by
  rw [← F.adjoint_inner_right, map_sub]
  have hg : F.adjoint (projection F hF y) = F.adjoint y :=
    (gramEquiv F hF).apply_symm_apply (F.adjoint y)
  rw [hg, sub_self, inner_zero_right]

theorem projection_eq_orthogonal (F : E →L[ℝ] H) (hF : Function.Injective F) :
    projection F hF = F.range.starProjection := by
  ext y
  symm
  apply Submodule.eq_starProjection_of_mem_orthogonal
  · exact ⟨(gramEquiv F hF).symm (F.adjoint y), rfl⟩
  · intro z hz
    obtain ⟨x, rfl⟩ := hz
    exact projection_residual_orthogonal F hF y x

theorem projection_norm_le (F : E →L[ℝ] H) (hF : Function.Injective F) :
    ‖projection F hF‖ ≤ 1 := by
  rw [projection_eq_orthogonal]
  exact Submodule.starProjection_norm_le _

theorem complement_norm_le (F : E →L[ℝ] H) (hF : Function.Injective F) :
    ‖(1 : H →L[ℝ] H) - projection F hF‖ ≤ 1 := by
  rw [projection_eq_orthogonal, ← Submodule.starProjection_orthogonal']
  exact Submodule.starProjection_norm_le _

theorem gram_right_inverse_bound (F : E →L[ℝ] H) (hF : Function.Injective F)
    (L : ℝ) (hL : 0 ≤ L) (hlower : ∀ x, ‖x‖ ≤ L * ‖F x‖) (y : H) :
    ‖(gramEquiv F hF).symm (F.adjoint y)‖ ≤ L * ‖y‖ := by
  apply (hlower _).trans
  apply mul_le_mul_of_nonneg_left _ hL
  change ‖projection F hF y‖ ≤ ‖y‖
  simpa only [one_mul] using ((projection F hF).le_opNorm y).trans
    (mul_le_mul_of_nonneg_right (projection_norm_le F hF) (norm_nonneg y))

abbrev Pair (E H : Type*) := WithLp 2 (E × H)

def saddle (F : E →L[ℝ] H) : Pair H E →L[ℝ] Pair H E :=
  ({ toFun x := WithLp.toLp 2 (x.fst + F x.snd, F.adjoint x.fst)
     map_add' x y := by
       apply WithLp.ofLp_injective 2
       apply Prod.ext
       · simp; abel
       · simp
     map_smul' a x := by apply WithLp.ofLp_injective 2; simp [smul_add] } :
    Pair H E →ₗ[ℝ] Pair H E).toContinuousLinearMap

@[simp] theorem saddle_fst (F : E →L[ℝ] H) (x : Pair H E) :
    (saddle F x).fst = x.fst + F x.snd := rfl
@[simp] theorem saddle_snd (F : E →L[ℝ] H) (x : Pair H E) :
    (saddle F x).snd = F.adjoint x.fst := rfl

def saddleInverse (F : E →L[ℝ] H) (hF : Function.Injective F) : Pair H E →L[ℝ] Pair H E :=
  ({ toFun x := WithLp.toLp 2
       (x.fst - projection F hF x.fst + F ((gramEquiv F hF).symm x.snd),
        (gramEquiv F hF).symm (F.adjoint x.fst) - (gramEquiv F hF).symm x.snd)
     map_add' x y := by
       apply WithLp.ofLp_injective 2
       apply Prod.ext
       · simp; abel
       · simp; abel
     map_smul' a x := by apply WithLp.ofLp_injective 2; simp [smul_add, smul_sub] } :
    Pair H E →ₗ[ℝ] Pair H E).toContinuousLinearMap

@[simp] theorem saddleInverse_fst (F : E →L[ℝ] H) (hF : Function.Injective F) (x : Pair H E) :
    (saddleInverse F hF x).fst =
      x.fst - projection F hF x.fst + F ((gramEquiv F hF).symm x.snd) := rfl
@[simp] theorem saddleInverse_snd (F : E →L[ℝ] H) (hF : Function.Injective F) (x : Pair H E) :
    (saddleInverse F hF x).snd =
      (gramEquiv F hF).symm (F.adjoint x.fst) - (gramEquiv F hF).symm x.snd := rfl

theorem projection_apply_map (F : E →L[ℝ] H) (hF : Function.Injective F) (x : E) :
    projection F hF (F x) = F x := by
  change F ((gramEquiv F hF).symm (gramEquiv F hF x)) = F x
  rw [ContinuousLinearEquiv.symm_apply_apply]

theorem adjoint_projection (F : E →L[ℝ] H) (hF : Function.Injective F) (x : H) :
    F.adjoint (projection F hF x) = F.adjoint x :=
  (gramEquiv F hF).apply_symm_apply _

theorem saddle_inverse_left (F : E →L[ℝ] H) (hF : Function.Injective F) (x : Pair H E) :
    saddle F (saddleInverse F hF x) = x := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · change x.fst - projection F hF x.fst + F ((gramEquiv F hF).symm x.snd) +
      F ((gramEquiv F hF).symm (F.adjoint x.fst) - (gramEquiv F hF).symm x.snd) = x.fst
    rw [map_sub]
    change x.fst - projection F hF x.fst + F ((gramEquiv F hF).symm x.snd) +
      (projection F hF x.fst - F ((gramEquiv F hF).symm x.snd)) = x.fst
    abel
  · change F.adjoint (x.fst - projection F hF x.fst + F ((gramEquiv F hF).symm x.snd)) = x.snd
    rw [map_add, map_sub, adjoint_projection, sub_self, zero_add]
    exact (gramEquiv F hF).apply_symm_apply _

theorem saddle_inverse_right (F : E →L[ℝ] H) (hF : Function.Injective F) (x : Pair H E) :
    saddleInverse F hF (saddle F x) = x := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · change (x.fst + F x.snd) - projection F hF (x.fst + F x.snd) +
      F ((gramEquiv F hF).symm (F.adjoint x.fst)) = x.fst
    rw [map_add, projection_apply_map]
    change (x.fst + F x.snd) - (projection F hF x.fst + F x.snd) +
      projection F hF x.fst = x.fst
    abel
  · change (gramEquiv F hF).symm (F.adjoint (x.fst + F x.snd)) -
      (gramEquiv F hF).symm (F.adjoint x.fst) = x.snd
    rw [map_add, map_add]
    have hg : (gramEquiv F hF).symm (F.adjoint (F x.snd)) = x.snd :=
      (gramEquiv F hF).symm_apply_apply x.snd
    rw [hg]
    abel

def saddleEquiv (F : E →L[ℝ] H) (hF : Function.Injective F) : Pair H E ≃L[ℝ] Pair H E :=
  ContinuousLinearEquiv.equivOfInverse' (saddle F) (saddleInverse F hF)
    (ContinuousLinearMap.ext (saddle_inverse_left F hF))
    (ContinuousLinearMap.ext (saddle_inverse_right F hF))

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [InnerProductSpace ℝ H] [FiniteDimensional ℝ H] in
theorem pair_norm_le_sum (x : Pair H E) : ‖x‖ ≤ ‖x.fst‖ + ‖x.snd‖ := by
  have h := WithLp.prod_norm_sq_eq_of_L2 x
  nlinarith [norm_nonneg x, norm_nonneg x.fst, norm_nonneg x.snd,
    mul_nonneg (norm_nonneg x.fst) (norm_nonneg x.snd)]

theorem saddle_inverse_norm_le (F : E →L[ℝ] H) (hF : Function.Injective F)
    (L : ℝ) (hL : 1 ≤ L) (hlower : ∀ x, ‖x‖ ≤ L * ‖F x‖) :
    ‖((saddleEquiv F hF).symm : Pair H E →L[ℝ] Pair H E)‖ ≤ 4 * L^2 := by
  change ‖saddleInverse F hF‖ ≤ 4 * L^2
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  have hL0 : 0 ≤ L := by linarith
  have hf := WithLp.norm_fst_le H x
  have hs := WithLp.norm_snd_le H x
  have hc : ‖x.fst - projection F hF x.fst‖ ≤ ‖x.fst‖ := by
    have hb := ((1 - projection F hF).le_opNorm x.fst).trans
      (mul_le_mul_of_nonneg_right (complement_norm_le F hF) (norm_nonneg x.fst))
    simpa using hb
  have hb₁ := gram_left_inverse_bound F hF L hL0 hlower x.snd
  have hb₂ := gram_right_inverse_bound F hF L hL0 hlower x.fst
  have hb₃ := (((gramEquiv F hF).symm : E →L[ℝ] E).le_opNorm x.snd).trans
    (mul_le_mul_of_nonneg_right (gramEquiv_inverse_bound F hF L hL0 hlower) (norm_nonneg x.snd))
  change ‖(gramEquiv F hF).symm x.snd‖ ≤ L^2 * ‖x.snd‖ at hb₃
  have hfirst : ‖(saddleInverse F hF x).fst‖ ≤ (1+L)*‖x‖ := by
    rw [saddleInverse_fst]
    apply (norm_add_le _ _).trans
    have hb := mul_le_mul_of_nonneg_left hs hL0
    linarith
  have hsecond : ‖(saddleInverse F hF x).snd‖ ≤ (L+L^2)*‖x‖ := by
    rw [saddleInverse_snd]
    apply (norm_sub_le _ _).trans
    have hb := mul_le_mul_of_nonneg_left hf hL0
    have hb' := mul_le_mul_of_nonneg_left hs (sq_nonneg L)
    linarith
  apply (pair_norm_le_sum _).trans
  have hcoeff : (1+L)+(L+L^2) ≤ 4*L^2 := by nlinarith
  have hprod := mul_le_mul_of_nonneg_right hcoeff (norm_nonneg x)
  nlinarith

theorem saddle_norm_le (F : E →L[ℝ] H) (hF : ‖F‖ ≤ 1) : ‖saddle F‖ ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  let v : Pair H E := WithLp.toLp 2 (F x.snd, F.adjoint x.fst)
  have h1 : ‖F x.snd‖ ≤ ‖x.snd‖ := by
    simpa using (F.le_opNorm x.snd).trans
      (mul_le_mul_of_nonneg_right hF (norm_nonneg x.snd))
  have h2 : ‖F.adjoint x.fst‖ ≤ ‖x.fst‖ := by
    have hn : ‖F.adjoint‖ ≤ 1 := by simpa using hF
    simpa using (F.adjoint.le_opNorm x.fst).trans
      (mul_le_mul_of_nonneg_right hn (norm_nonneg x.fst))
  have hv : ‖v‖ ≤ ‖x‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2]
    change ‖F x.snd‖^2 + ‖F.adjoint x.fst‖^2 ≤ ‖x.fst‖^2 + ‖x.snd‖^2
    nlinarith [pow_le_pow_left₀ (norm_nonneg _) h1 2, pow_le_pow_left₀ (norm_nonneg _) h2 2]
  have heq : saddle F x = WithLp.toLp 2 (x.fst, (0 : E)) + v := by
    apply WithLp.ofLp_injective 2
    simp [saddle, v]
  rw [heq]
  apply (norm_add_le _ _).trans
  rw [WithLp.norm_toLp_fst]
  linarith [WithLp.norm_fst_le H x]

theorem projected_residual_identity (F : E →L[ℝ] H) (hF : Function.Injective F)
    (y : H) (z zstar q : E) (hstar : gram F zstar = q) :
    F (z-zstar) = projection F hF (y+F z) - F ((gramEquiv F hF).symm (F.adjoint y+q)) := by
  have hz : (gramEquiv F hF).symm (gram F z) = z := (gramEquiv F hF).symm_apply_apply z
  have hzs : (gramEquiv F hF).symm q = zstar := by
    rw [← hstar]
    exact (gramEquiv F hF).symm_apply_apply zstar
  simp only [projection, ContinuousLinearMap.comp_apply, map_add, map_sub, hzs]
  change F z - F zstar =
    F ((gramEquiv F hF).symm (F.adjoint y)) + F ((gramEquiv F hF).symm (gram F z)) -
      (F ((gramEquiv F hF).symm (F.adjoint y)) + F zstar)
  rw [hz]
  abel

theorem projected_residual_bound (F : E →L[ℝ] H) (hF : Function.Injective F)
    (L : ℝ) (hL : 1 ≤ L) (hlower : ∀ x, ‖x‖ ≤ L*‖F x‖)
    (y : H) (z zstar q : E) (hstar : gram F zstar = q) :
    ‖F (z-zstar)‖ ≤ 2*L*‖WithLp.toLp 2 (y+F z, F.adjoint y+q)‖ := by
  rw [projected_residual_identity F hF y z zstar q hstar]
  let r : Pair H E := WithLp.toLp 2 (y+F z, F.adjoint y+q)
  have h1 : ‖projection F hF r.fst‖ ≤ ‖r.fst‖ := by
    simpa using ((projection F hF).le_opNorm r.fst).trans
      (mul_le_mul_of_nonneg_right (projection_norm_le F hF) (norm_nonneg r.fst))
  have h2 := gram_left_inverse_bound F hF L (by linarith) hlower r.snd
  apply (norm_sub_le _ _).trans
  have hf := WithLp.norm_fst_le H r
  have hs := mul_le_mul_of_nonneg_left (WithLp.norm_snd_le H r) (by linarith : 0 ≤ L)
  have hl := mul_le_mul_of_nonneg_right hL (norm_nonneg r)
  change ‖projection F hF r.fst‖ + ‖F ((gramEquiv F hF).symm r.snd)‖ ≤ 2*L*‖r‖
  linarith

theorem projected_relative_residual (F : E →L[ℝ] H) (hF : Function.Injective F)
    (hnorm : ‖F‖ ≤ 1) (L η : ℝ) (hL : 1 ≤ L) (hη : 0 ≤ η)
    (hlower : ∀ x, ‖x‖ ≤ L*‖F x‖)
    (y : H) (z zstar q : E) (hstar : gram F zstar = q)
    (hres : ‖WithLp.toLp 2 (y+F z, F.adjoint y+q)‖ ≤ η*‖q‖) :
    ‖F (z-zstar)‖ ≤ (2*L*η)*‖F zstar‖ := by
  have hn : ‖F.adjoint‖ ≤ 1 := by simpa using hnorm
  have hq : ‖q‖ ≤ ‖F zstar‖ := by
    rw [← hstar]
    exact (F.adjoint.le_opNorm _).trans (by simpa using mul_le_mul_of_nonneg_right hn (norm_nonneg (F zstar)))
  apply (projected_residual_bound F hF L hL hlower y z zstar q hstar).trans
  have hh := mul_le_mul_of_nonneg_left (hres.trans (mul_le_mul_of_nonneg_left hq hη))
    (by linarith : 0 ≤ 2*L)
  simpa only [mul_assoc] using hh

end Maxwell.Composition.RectangularSaddle
