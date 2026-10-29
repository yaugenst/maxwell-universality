import Maxwell.Composition.PhysicalResidual
import Maxwell.Composition.PhysicalWoodbury

/-! Full-operator conditioning and every-complex-output source recovery for
the literal scalar-cell instance. The hypotheses are scalar precision and
calibration budgets; neither an inverse nor a recovery theorem is assumed. -/
noncomputable section
namespace Maxwell.Composition.PhysicalSoundness
open Maxwell.Composition.PhysicalGram
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option quotPrecheck false

variable (P : PhysicalPlatform) (S : Source.SparseSystem) (precision d : ℕ)
variable (ζ : ℚ) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) (hd : P.spacing.minimumDistance ≤ d)
variable (J : ℕ) (j : Fin J) (hm : 0 < S.nnz)
variable (hj : j.val ∉ bad P S precision d ζ hζ hζ1 J)
variable (ε L : ℚ) (hε : 0 < ε) (hL : 0 < L)
variable (q : PhysicalSource.Local P → ℚ)
variable (v : SourceDecoration.Vertex S precision → ℚ)
variable (hv : ∀ i, 0 ≤ v i ∧ v i ≤ P.incrementBound) (hv0 : ∀ i, v i ≠ 0)
variable (δ : ℚ) (hδ : 0 < δ) (format : Target.FixedPointFormat)
local instance : DecidableEq (SourceDecoration.Vertex S precision) := Classical.decEq _

local notation "αq" => P.spacing.alpha d
local notation "hαq" => P.spacing.alpha_pos d
local notation "Iout" => PhysicalInstance.target P S precision d ζ hζ hζ1 hd J j αq ε L hαq hε hL q v hv δ hδ format
local notation "Efield" => EuclideanSpace ℝ (box P S precision d ζ hζ hζ1).Edge
local notation "g" => PhysicalSource.exactLogicalSource S precision
local notation "G" => ‖g‖
local notation "Bmode" => EuclideanSpace ℝ (SourceDecoration.Vertex S precision)

def coreBudget (Ls : ℝ) : ℝ :=
  4*(32*SourceMediator.inverseBudget S precision Ls / (P.spacing.alpha d : ℝ)+2/(P.defectGap : ℝ))

def fullBudget (Ls : ℝ) : ℝ := PhysicalWoodbury.inverseBudget P S precision d ζ hζ hζ1
  (coreBudget P S precision d Ls)

include hm hj hv0 in
theorem sound (hunit : IsUnit (Source.realMatrix S)) (hm2 : 2 ≤ S.nnz) (hb : S.source ≠ 0)
    (hp : 1 ≤ precision) (Ls eta : ℝ) (hLs : 1 ≤ Ls) (heta : 0 ≤ eta) (heta1 : eta ≤ 1)
    (hcondition : (S.nnz : ℝ)*condition₂ (Source.realMatrix S) ≤ Ls)
    (hprecision : (S.nnz : ℝ)/(2*2^precision) ≤ eta/(64*Ls))
    (hrow : 16 ≤ P.rowBound) (hL1 : 1 ≤ L) (hεhalf : ε ≤ 1/2)
    (hLb : P.constants.backgroundInverseBudget ζ hζ S.nnz
      (Fintype.card (box P S precision d ζ hζ hζ1).Edge) ≤ L)
    (hfloor : P.coreFloor ≤ d) (hzeta : ζ = P.spacing.zeta d)
    (β : Maxwell.Spectral.Lattice.Direction → ℚ)
    (hβlower : ∀ k, 3*(αq : ℝ) ≤ |(β k : ℝ)|)
    (hβupper : ∀ k, |(β k : ℝ)| ≤ (((P.greenConstant+1)*P.spacing.zeta d : ℚ) : ℝ))
    (hβerror : ∀ k, |(β k : ℝ)+PhysicalBright.axial P d k| ≤ (ζ : ℝ)^2)
    (hvcal : ∀ i, |(v i : ℝ)⁻¹-(P.eigenvalue+
      (PhysicalDiagonal.diagonal S precision αq β i : ℝ))| ≤ (ζ : ℝ)^2)
    (hspacing : (P.spacing.errorConstant : ℝ)*(ζ : ℝ)^2 ≤
      (αq : ℝ)*ε/(4096*SourceMediator.inverseBudget S precision Ls))
    (hqnorm : ‖PhysicalSource.realVector q‖ ≤ 2)
    (hqsource : ‖PhysicalSource.realVector q-P.weightedMode‖ ≤
      (1/4 : ℝ)*ε/(32768*P.rowBound*L))
    (hqread : ‖PhysicalSource.realVector q-P.weightedMode‖ ≤
      (ε : ℝ)/(1024*P.incrementBound*αq*P.rowBound*2*fullBudget P S precision d ζ hζ hζ1 Ls))
    (htol : δ ≤ ε/(8192*P.rowBound*2*L)) (htolhalf : δ ≤ 1/2)
    (haccess : 2*(P.incrementBound : ℝ)*((S.n : ℝ)*
      ((Maxwell.Defect.ScalarDefect.edges P.defect).card : ℝ))/(2 : ℝ)^format.fractionalBits ≤ (ε : ℝ)/4096)
    (hrange : 6*(αq : ℝ)*P.rowBound*fullBudget P S precision d ζ hζ hζ1 Ls*G <
      (2 : ℝ)^format.integerBits)
    (hlogical : (SourceRecovery.residualFactor S precision : ℝ)*ε ≤ eta)
    (hread : (ε : ℝ)*G*S.nnz ≤ eta) :
    IsUnit (Iout).realMatrix ∧ condition₂ (Iout).realMatrix ≤
      16*fullBudget P S precision d ζ hζ hζ1 Ls ∧
      ∀ y : EuclideanSpace ℂ (Iout).box.Edge, (Iout).Admissible y →
        (Iout).decoder.Fits (fun e => (y e).re) ∧
        (∃ w : (Iout).decoder.Messages, (Iout).decoder.Accurate w (fun e => (y e).re)) ∧
        ∀ w : (Iout).decoder.Messages, (Iout).decoder.Accurate w (fun e => (y e).re) →
          Source.ResidualTarget S (eta/4) ((Iout).decoder.decode w) := by
  have hα : (0:ℝ) < αq := by exact_mod_cast hαq
  have hεR : (0:ℝ) ≤ ε := by exact_mod_cast hε.le
  have hεhalfR : (ε : ℝ) ≤ 1/2 := by
    have h : (ε : ℝ) ≤ ((1/2 : ℚ) : ℝ) := Rat.cast_le.mpr hεhalf
    norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at h
    exact h
  have hε1 : ε ≤ 1 := hεhalf.trans (by norm_num)
  have hδR : (δ : ℝ) ≤ 1/2 := by
    have h : (δ : ℝ) ≤ ((1/2 : ℚ) : ℝ) := Rat.cast_le.mpr htolhalf
    norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at h
    exact h
  have hJpos : (0:ℝ) < P.rowBound := by exact_mod_cast P.rowBound_pos
  have hG1 : 1 ≤ G := by
    rw [PhysicalSource.exactLogicalSource_norm]
    exact (SourceSubdivision.source_norm_bounds S hb precision).1
  have hsmall := SourceSubdivision.rounding_small S precision Ls eta hLs heta1 hcondition hprecision
  obtain ⟨Dc,Bc,Mc,hDc,hDi,hBc,hBi,hpert,hMc,hMi⟩ :=
    PhysicalCoreInverse.exists_core_inverse P S precision d ζ hζ hζ1 hd hm J j hj
      hunit hm2 hp hsmall Ls (ε : ℝ) hLs hεhalfR hcondition hfloor hzeta
      β hβlower hβupper hβerror v hvcal hspacing
  let A := PhysicalWoodbury.fullEquiv P S precision d ζ hζ hζ1 hd hm J j hj v hv0 Mc hMc
  have hA : (A : Efield →L[ℝ] Efield) = (Iout).realOperator :=
    PhysicalWoodbury.fullEquiv_operator P S precision d ζ hζ hζ1 hd hm J j hj v hv hv0 Mc hMc
  have hAi : ‖(A.symm : Efield →L[ℝ] Efield)‖ ≤ fullBudget P S precision d ζ hζ hζ1 Ls :=
    PhysicalWoodbury.fullEquiv_inverse_bound P S precision d ζ hζ hζ1 hd hm J j hj v hv0 Mc hMc
      (coreBudget P S precision d Ls) hMi
  have hcond := PhysicalWoodbury.full_conditioning P S precision d ζ hζ hζ1 hd hm J j hj
    v hv hv0 Mc hMc (coreBudget P S precision d Ls) hMi
  have hQA : 0 < fullBudget P S precision d ζ hζ hζ1 Ls := by
    have hLbpos := P.constants.backgroundInverseBudget_pos ζ hζ S.nnz
      (Fintype.card (box P S precision d ζ hζ hζ1).Edge) hm
    have hLbR : (0:ℝ) < P.constants.backgroundInverseBudget ζ hζ S.nnz
      (Fintype.card (box P S precision d ζ hζ hζ1).Edge) := by exact_mod_cast hLbpos
    have hKs := SourceMediator.inverseBudget_ge_one S precision Ls hLs
    have hg : (0:ℝ) < P.defectGap := by exact_mod_cast P.defectGap_pos
    unfold fullBudget PhysicalWoodbury.inverseBudget coreBudget
    positivity
  have hsource := PhysicalResidual.source_norm P S precision d ζ hζ hζ1 hd J j hm hj
    αq ε L hαq hε hL q v hv δ hδ format hb hrow hL1 hε1 hqsource
  refine ⟨hcond.1,hcond.2,?_⟩
  intro y hy
  have hyamp := target_admissible_amplitude Iout A hA
    (fullBudget P S precision d ζ hζ hζ1 Ls) (4*(αq : ℝ)*P.rowBound*G) hAi hsource
    hδR y hy
  have hyamp' : ‖euclideanRealPart y‖ ≤
      3*(αq : ℝ)*P.rowBound*2*fullBudget P S precision d ζ hζ hζ1 Ls*G := by
    convert hyamp using 1; ring
  have hfit := target_admissible_finite_access Iout A hA
    (fullBudget P S precision d ζ hζ hζ1 Ls) (4*(αq : ℝ)*P.rowBound*G) hAi hsource
    hδR (by
      change 3*fullBudget P S precision d ζ hζ hζ1 Ls*(4*(αq : ℝ)*P.rowBound*G)/2 <
        (2 : ℝ)^format.integerBits
      convert hrange using 1; ring) y hy
  refine ⟨hfit.1,hfit.2,?_⟩
  intro w hw
  let z := SourcePhysicalDecoder.bright P S precision d ζ hζ hζ1 hd v hv0 (euclideanRealPart y)
  have hbright := PhysicalResidual.admissible_bright P S precision d ζ hζ hζ1 hd J j hm hj
    αq ε L hαq hε hL q v hv hv0 δ hδ format hb hrow hL1 hε1 hLb hfloor hzeta hqsource htol
    Dc hDc hDi y hy
  have hBres : ‖Bc z-(αq : ℝ) • g‖ ≤ 3*(αq : ℝ)*ε*G/4096 := by
    change ‖(Bc : Bmode →L[ℝ] Bmode) z-(αq : ℝ) • g‖ ≤ _
    rw [hBc]
    exact hbright
  have hKpos : 0 < SourceMediator.inverseBudget S precision Ls :=
    lt_of_lt_of_le zero_lt_one (SourceMediator.inverseBudget_ge_one S precision Ls hLs)
  have hz := bright_amplitude_budget Bc z g (αq : ℝ) (ε : ℝ) G
    (SourceMediator.inverseBudget S precision Ls) hα hεhalfR (norm_nonneg _) hKpos.le le_rfl hBi hBres
  have ht := target_residual_budget (Bc : Bmode →L[ℝ] Bmode)
    (SourceMediator.operator S precision (αq : ℝ) (fun e => (β (SourceIncidence.axis S precision e) : ℝ)))
    z ((αq : ℝ) • g) (αq : ℝ) (ε : ℝ) G (SourceMediator.inverseBudget S precision Ls)
    hKpos hBres (by rwa [hBc]) hz
  have htarget : ‖SourceMediator.operator S precision (αq : ℝ)
      (fun e => (β (SourceIncidence.axis S precision e) : ℝ)) z-SourceMediator.source S precision (αq : ℝ)‖ ≤
      (αq : ℝ)*ε*‖SourceSubdivision.source S precision‖/64 := by
    rw [SourceMediator.source,← PhysicalSource.exactLogicalSource_eq]
    rw [← PhysicalSource.exactLogicalSource_norm]
    apply ht.trans
    nlinarith [mul_nonneg (mul_nonneg hα.le hεR) (norm_nonneg g)]
  have hcoord := SourcePhysicalDecoder.finite_coordinate_error P S precision d ζ hζ hζ1 hd q v format hv0
    (euclideanRealPart y) w hw (P.incrementBound : ℝ) (αq : ℝ) (P.rowBound : ℝ) 2
    (fullBudget P S precision d ζ hζ hζ1 Ls) (ε : ℝ) G
    (by exact_mod_cast P.incrementBound_pos) hα hJpos (by norm_num) hQA hG1
    (fun i => ⟨by exact_mod_cast (hv i).1,by exact_mod_cast (hv i).2⟩)
    hqnorm hqread hyamp' haccess
  change Source.ResidualTarget S (eta/4)
    ((SourcePhysicalDecoder.decoder P S precision d ζ hζ hζ1 hd q v format).decode w)
  rw [SourcePhysicalDecoder.decode P S precision d ζ hζ hζ1 hd q v format w]
  apply SourceRecovery.source_output_residual S hunit hm2 hb precision hp Ls eta (αq : ℝ) (ε : ℝ)
    hLs heta heta1 hα hcondition hprecision (fun e => (β (SourceIncidence.axis S precision e) : ℝ))
    (fun e => hβlower _) z _ htarget hlogical
  intro i
  apply (hcoord i).trans
  have hmR : (0:ℝ) < S.nnz := by exact_mod_cast hm
  apply (le_div_iff₀ (by positivity : (0:ℝ) < 16*S.nnz)).mpr
  have hnonneg : 0 ≤ (ε : ℝ)*G*S.nnz := by positivity
  nlinarith

end Maxwell.Composition.PhysicalSoundness
