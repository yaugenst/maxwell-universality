import Maxwell.Composition.PhysicalBright
import Maxwell.Composition.PhysicalDiagonal
import Maxwell.Composition.ModeSchur

/-! Construction of the full actual weighted-core inverse. The target inverse
comes from the routed source theorem; all complementary and mixed estimates
come from the physical platform and the same finite-background good event. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
namespace Maxwell.Composition.PhysicalCoreInverse
open Maxwell.Spectral Maxwell.Spectral.Lattice

/-- The fixed physical floor also bounds the products of a complementary
inverse and either mixed block by one. -/
theorem mixed_product_small (P : PhysicalPlatform) (d : ℕ) (hd : P.coreFloor ≤ d) :
    (2 / (P.defectGap : ℝ)) *
      ((64 * (P.greenConstant : ℝ) + 1) * (P.spacing.zeta d : ℝ)) ≤ 1 := by
  have hz := (P.coreFloor_zeta d hd).trans
    ((min_le_right _ _).trans (min_le_right _ _))
  have hC := P.greenConstant_nonneg
  have hpos : (0 : ℚ) < 8 * (64 * P.greenConstant + 2) := by positivity
  have hmul := (le_div_iff₀ hpos).mp hz
  have hmulR : (P.spacing.zeta d : ℝ) * (8 * (64 * (P.greenConstant : ℝ) + 2)) ≤
      (P.defectGap : ℝ) := by exact_mod_cast hmul
  have hζR : (0 : ℝ) ≤ P.spacing.zeta d := by exact_mod_cast (P.spacing.zeta_pos d).le
  have hg : (0 : ℝ) < P.defectGap := by exact_mod_cast P.defectGap_pos
  have hsmall : 2 * ((64 * (P.greenConstant : ℝ) + 1) * (P.spacing.zeta d : ℝ)) ≤
      (P.defectGap : ℝ) := by
    have hCR : (0 : ℝ) ≤ P.greenConstant := by exact_mod_cast hC
    nlinarith
  rw [div_mul_eq_mul_div]
  exact (div_le_iff₀ hg).mpr (by simpa only [one_mul] using hsmall)

variable (P : PhysicalPlatform) (S : Source.SparseSystem) (precision d : ℕ)
variable (ζ : ℚ) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
variable (hd : P.spacing.minimumDistance ≤ d) (hm : 0 < S.nnz)
variable (J : ℕ) (j : Fin J) (hj : j.val ∉ PhysicalGram.bad P S precision d ζ hζ hζ1 J)
local instance : DecidableEq (SourceIncidence.V S precision) := Classical.decEq _

/-- Construct the actual complement, bright Schur, and full weighted core
inverses, retaining their exact identities for later residual recovery. -/
theorem exists_core_inverse
    (hunit : IsUnit (Source.realMatrix S)) (hm2 : 2 ≤ S.nnz) (hp : 1 ≤ precision)
    (hsource : ((S.nnz : ℝ) * Maxwell.condition₂ (Source.realMatrix S)) *
      ((S.nnz : ℝ) / (2 * 2 ^ precision)) ≤ 1 / 2)
    (L ε : ℝ) (hL : 1 ≤ L) (hε : ε ≤ 1 / 2)
    (hcondition : (S.nnz : ℝ) * Maxwell.condition₂ (Source.realMatrix S) ≤ L)
    (hfloor : P.coreFloor ≤ d) (hzeta : ζ = P.spacing.zeta d)
    (β : Direction → ℚ)
    (hβlower : ∀ k, 3 * (P.spacing.alpha d : ℝ) ≤ |(β k : ℝ)|)
    (hβupper : ∀ k, |(β k : ℝ)| ≤ ((P.greenConstant + 1) * P.spacing.zeta d : ℚ))
    (hβerror : ∀ k, |(β k : ℝ) + PhysicalBright.axial P d k| ≤ (ζ : ℝ)^2)
    (v : SourceDecoration.Vertex S precision → ℚ)
    (hv : ∀ i, |(v i : ℝ)⁻¹ - (P.eigenvalue +
      (PhysicalDiagonal.diagonal S precision (P.spacing.alpha d) β i : ℝ))| ≤ (ζ : ℝ)^2)
    (hbudget : (P.spacing.errorConstant : ℝ) * (ζ : ℝ)^2 ≤
      (P.spacing.alpha d : ℝ) * ε / (4096 * SourceMediator.inverseBudget S precision L)) :
    ∃ Dc : ModeComplement (ι := SourceDecoration.Vertex S precision) P.mode ≃L[ℝ]
        ModeComplement (ι := SourceDecoration.Vertex S precision) P.mode,
    ∃ Bc : EuclideanSpace ℝ (SourceDecoration.Vertex S precision) ≃L[ℝ]
        EuclideanSpace ℝ (SourceDecoration.Vertex S precision),
    ∃ Mc : EuclideanSpace ℝ (SourceDecoration.Vertex S precision × PhysicalCore.K P) ≃L[ℝ]
        EuclideanSpace ℝ (SourceDecoration.Vertex S precision × PhysicalCore.K P),
      (Dc : ModeComplement (ι := SourceDecoration.Vertex S precision) P.mode →L[ℝ]
        ModeComplement (ι := SourceDecoration.Vertex S precision) P.mode) =
          (modeComplementProjection P.mode).comp
            ((PhysicalCore.core P S precision d ζ hζ hζ1 hd hm J j hj v).comp
              (modeComplementInclusion P.mode)) ∧
      ‖(Dc.symm : ModeComplement (ι := SourceDecoration.Vertex S precision) P.mode →L[ℝ]
        ModeComplement (ι := SourceDecoration.Vertex S precision) P.mode)‖ ≤ 2 / (P.defectGap : ℝ) ∧
      (Bc : EuclideanSpace ℝ (SourceDecoration.Vertex S precision) →L[ℝ]
        EuclideanSpace ℝ (SourceDecoration.Vertex S precision)) =
          modeSchur P.mode (PhysicalCore.core P S precision d ζ hζ hζ1 hd hm J j hj v) Dc ∧
      ‖(Bc.symm : EuclideanSpace ℝ (SourceDecoration.Vertex S precision) →L[ℝ]
        EuclideanSpace ℝ (SourceDecoration.Vertex S precision))‖ ≤
          32 * SourceMediator.inverseBudget S precision L / (P.spacing.alpha d : ℝ) ∧
      ‖modeSchur P.mode (PhysicalCore.core P S precision d ζ hζ hζ1 hd hm J j hj v) Dc -
        SourceMediator.operator S precision (P.spacing.alpha d : ℝ)
          (fun e => (β (SourceIncidence.axis S precision e) : ℝ))‖ ≤
          (P.spacing.alpha d : ℝ) * ε / (4096 * SourceMediator.inverseBudget S precision L) ∧
      (Mc : EuclideanSpace ℝ (SourceDecoration.Vertex S precision × PhysicalCore.K P) →L[ℝ]
        EuclideanSpace ℝ (SourceDecoration.Vertex S precision × PhysicalCore.K P)) =
          PhysicalCore.core P S precision d ζ hζ hζ1 hd hm J j hj v ∧
      ‖(Mc.symm : EuclideanSpace ℝ (SourceDecoration.Vertex S precision × PhysicalCore.K P) →L[ℝ]
        EuclideanSpace ℝ (SourceDecoration.Vertex S precision × PhysicalCore.K P))‖ ≤
          4 * (32 * SourceMediator.inverseBudget S precision L / (P.spacing.alpha d : ℝ) +
            2 / (P.defectGap : ℝ)) := by
  let K := SourceMediator.inverseBudget S precision L
  let α : ℝ := P.spacing.alpha d
  let M := PhysicalCore.core P S precision d ζ hζ hζ1 hd hm J j hj v
  let U := blockInjection (ι := SourceDecoration.Vertex S precision) P.mode
  let Z := modeComplementInclusion (ι := SourceDecoration.Vertex S precision) P.mode
  let Q := modeComplementProjection (ι := SourceDecoration.Vertex S precision) P.mode
  have hα : 0 < α := by
    dsimp only [α]
    exact_mod_cast P.spacing.alpha_pos d
  have hK : 0 < K := lt_of_lt_of_le (by norm_num) (SourceMediator.inverseBudget_ge_one S precision L hL)
  have hg : (0 : ℝ) < P.defectGap := by exact_mod_cast P.defectGap_pos
  have hC : (0 : ℝ) ≤ P.greenConstant := by exact_mod_cast P.greenConstant_nonneg
  have hζR : (0 : ℝ) ≤ ζ := by exact_mod_cast hζ.le
  have hhalf : (ζ : ℝ) ≤ 1/2 := by
    rw [hzeta]
    have hf : P.spacing.zeta d ≤ (1/2 : ℚ) := (P.coreFloor_small d hfloor).1
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr hf
  have hζd : (ζ : ℝ) = (P.spacing.r : ℝ)^d := by
    rw [hzeta]
    simp [Realization.SpacingPlatform.zeta]
  have hv' : ∀ i, |(v i : ℝ)⁻¹ - (P.eigenvalue +
      (PhysicalDiagonal.diagonal S precision (P.spacing.alpha d) β i : ℝ))| ≤
        (P.spacing.zeta d : ℝ)^2 := by simpa only [hzeta] using hv
  obtain ⟨hstrength, hsmall⟩ := PhysicalDiagonal.inverse_strength_budget S precision P d hfloor β hβupper v hv'
  have hstrength' : ∀ i, |(v i : ℝ)⁻¹ - P.eigenvalue| ≤
      (P.tuningMargin : ℝ) + (ζ : ℝ)^2 := by simpa only [hzeta] using hstrength
  have hsmall' : ((P.tuningMargin : ℝ) + (ζ : ℝ)^2) +
      64*(P.greenConstant : ℝ)*(ζ : ℝ) + (ζ : ℝ)^2 ≤ (P.defectGap : ℝ)/2 := by
    simpa only [hzeta] using hsmall
  obtain ⟨Dc, hDc, hDnorm⟩ := PhysicalCore.exists_complement_inverse P S precision d ζ hζ hζ1
    hd hm J j hj v hζd hhalf ((P.tuningMargin : ℝ) + (ζ : ℝ)^2)
    (by
      have ht : (0 : ℝ) < P.tuningMargin := by exact_mod_cast P.tuningMargin_pos
      exact add_nonneg ht.le (sq_nonneg _))
    hstrength' hsmall'
  have hraw := PhysicalBright.raw_bright_error_bound P S precision d ζ hζ hζ1 hd hm J j hj v
    α β hζd hhalf hβerror (fun i => by
      simpa only [PhysicalDiagonal.diagonal_cast, PhysicalBright.targetMatrix] using hv i)
  have hupper := PhysicalCore.bright_complement_bound P S precision d ζ hζ hζ1 hd hm J j hj v hζd hhalf
  have hlower := PhysicalCore.complement_bright_bound P S precision d ζ hζ hζ1 hd hm J j hj v hζd hhalf
  have hschur : ‖modeSchur P.mode M Dc - SourceMediator.operator S precision α
      (fun e => (β (SourceIncidence.axis S precision e) : ℝ))‖ ≤ α * ε / (4096 * K) := by
    have he := bright_schur_error_bound M U Z U.adjoint Q Dc
      (SourceMediator.operator S precision α (fun e => (β (SourceIncidence.axis S precision e) : ℝ)))
      (P.greenConstant : ℝ) (2 / (P.defectGap : ℝ)) (ζ : ℝ)
      hC (by positivity) hζR hraw hupper hlower hDnorm
    exact he.trans ((mul_le_mul_of_nonneg_right P.error_constant (sq_nonneg _)).trans hbudget)
  obtain ⟨T, hTop, hTnorm⟩ := SourceMediator.exists_equiv S precision hunit hm2 hp hsource
    L α hL hα hcondition (fun e => (β (SourceIncidence.axis S precision e) : ℝ))
    (fun e => hβlower (SourceIncidence.axis S precision e))
  let Δ := modeSchur P.mode M Dc - (T : EuclideanSpace ℝ (SourceDecoration.Vertex S precision) →L[ℝ]
    EuclideanSpace ℝ (SourceDecoration.Vertex S precision))
  have hΔ : ‖Δ‖ ≤ α * ε / (4096 * K) := by simpa only [Δ, hTop] using hschur
  have hprod := bright_perturbation_product_bound T Δ α ε K hα hK hTnorm hΔ
  have hpert : ‖(T.symm : EuclideanSpace ℝ (SourceDecoration.Vertex S precision) →L[ℝ]
      EuclideanSpace ℝ (SourceDecoration.Vertex S precision))‖ * ‖Δ‖ < 1 := by linarith
  let Bc := perturbationEquiv T Δ hpert
  have hBc : (Bc : EuclideanSpace ℝ (SourceDecoration.Vertex S precision) →L[ℝ]
      EuclideanSpace ℝ (SourceDecoration.Vertex S precision)) = modeSchur P.mode M Dc := by
    rw [perturbationEquiv_toContinuousLinearMap]
    dsimp only [Δ]
    abel
  have hBnorm : ‖(Bc.symm : EuclideanSpace ℝ (SourceDecoration.Vertex S precision) →L[ℝ]
      EuclideanSpace ℝ (SourceDecoration.Vertex S precision))‖ ≤ 32*K/α :=
    bright_inverse_norm_le T Δ α ε K hα hK hε hTnorm hΔ hpert
  have hmixed : (2/(P.defectGap : ℝ)) * ((64*(P.greenConstant : ℝ)+1)*(ζ : ℝ)) ≤ 1 := by
    simpa only [hzeta] using mixed_product_small P d hfloor
  have hleft : ‖(Dc.symm : ModeComplement (ι := SourceDecoration.Vertex S precision) P.mode →L[ℝ]
      ModeComplement (ι := SourceDecoration.Vertex S precision) P.mode).comp (Q.comp (M.comp U))‖ ≤ 1 :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul hDnorm hlower (norm_nonneg (Q.comp (M.comp U))) (by positivity)).trans hmixed)
  have hright : ‖(U.adjoint.comp (M.comp Z)).comp
      (Dc.symm : ModeComplement (ι := SourceDecoration.Vertex S precision) P.mode →L[ℝ]
        ModeComplement (ι := SourceDecoration.Vertex S precision) P.mode)‖ ≤ 1 := by
    apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
    apply (mul_le_mul hupper hDnorm
      (norm_nonneg (Dc.symm : ModeComplement (ι := SourceDecoration.Vertex S precision) P.mode →L[ℝ]
        ModeComplement (ι := SourceDecoration.Vertex S precision) P.mode)) (by positivity)).trans
    simpa only [mul_comm] using hmixed
  have hDapply : ∀ c, Q (M (Z c)) = Dc c := by
    intro c
    exact (congrArg (fun A : ModeComplement (ι := SourceDecoration.Vertex S precision) P.mode →L[ℝ]
      ModeComplement (ι := SourceDecoration.Vertex S precision) P.mode => A c) hDc).symm
  let Mc := modeComplementaryEquiv P.mode P.mode_unit M Dc Bc hDapply hBc
  refine ⟨Dc, Bc, Mc, hDc, hDnorm, hBc, hBnorm, hschur, rfl, ?_⟩
  exact (modeComplementaryEquiv_inverse_norm_le P.mode P.mode_unit M Dc Bc hDapply hBc hleft hright).trans
    (mul_le_mul_of_nonneg_left (add_le_add hBnorm hDnorm) (by norm_num))

end Maxwell.Composition.PhysicalCoreInverse
