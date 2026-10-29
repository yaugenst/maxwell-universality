import Maxwell.Continuum.CellBandFourierReality
import Maxwell.Continuum.CellBandFourierL1Sharp

/-! The selected eight-alias state reconstructs to the explicit real
sine/cosine reference field used for calibration. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.CellBandFourier

open FreeFiber ClusterComplement CornerBridge FiberNormalization

def halfAngle (x : Space) (j : Fin 3) : ℝ := Real.pi * x j / 2

def signPhase (x : Space) (j : Fin 3) (b : Bool) : ℂ :=
  Complex.exp (((Corner.sign b * halfAngle x j : ℝ) : ℂ) * Complex.I)

theorem phase_cubeAlias (s : Corner.Parity) (x : Space) :
    spatialPhase (aliasMomentum 0 (cubeAlias s)) x =
      signPhase x 0 s.1 * signPhase x 1 s.2.1 * signPhase x 2 s.2.2 := by
  rw [central_momentum_decomposition, alias_signs]
  simp [spatialPhase, realMomentum, Fin.sum_univ_three, Corner.waveSigns, signPhase,
    halfAngle]
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  ring

theorem signPhase_false (x : Space) (j : Fin 3) :
    signPhase x j false = Complex.cos (halfAngle x j) - Complex.sin (halfAngle x j) * Complex.I := by
  simpa [signPhase, Corner.sign] using (Complex.cos_sub_sin_I (halfAngle x j)).symm

theorem signPhase_true (x : Space) (j : Fin 3) :
    signPhase x j true = Complex.cos (halfAngle x j) + Complex.sin (halfAngle x j) * Complex.I := by
  simpa [signPhase, Corner.sign] using Complex.exp_mul_I (halfAngle x j)

theorem sum_bool_complex (f : Bool → ℂ) : ∑ b, f b = f false + f true := by
  have hu : (Finset.univ : Finset Bool) = {false,true} := by decide
  rw [hu]
  simp

def trigField (v : Corner.Vec) (x : Space) : Polarization :=
  WithLp.toLp 2 ![
    ((v 0 * Real.sin (halfAngle x 0) * Real.sin (halfAngle x 1) * Real.sin (halfAngle x 2) : ℝ) : ℂ),
    ((-v 1 * Real.cos (halfAngle x 0) * Real.cos (halfAngle x 1) * Real.sin (halfAngle x 2) : ℝ) : ℂ),
    ((-v 2 * Real.cos (halfAngle x 0) * Real.sin (halfAngle x 1) * Real.cos (halfAngle x 2) : ℝ) : ℂ)]

theorem selected_fourier_sum (v : Corner.Vec) (x : Space) :
    Complex.I • (∑ s : Corner.Parity, spatialPhase (aliasMomentum 0 (cubeAlias s)) x •
      momentumVector (realMomentum (Corner.embedding Corner.selectedParity v s))) =
      (8 : ℂ) • trigField v x := by
  apply PiLp.ext
  intro j
  simp only [WithLp.ofLp_smul, WithLp.ofLp_sum, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, momentumVector, realMomentum, phase_cubeAlias,
    Fintype.sum_prod_type, sum_bool_complex]
  fin_cases j <;>
    simp [Corner.embedding, Corner.reflect, Corner.character, Corner.selectedParity,
      Corner.waveSigns, Corner.sign, signPhase_false, signPhase_true, trigField,
      Complex.ofReal_mul, Complex.ofReal_neg, ← Complex.ofReal_sin, ← Complex.ofReal_cos] <;>
    ring_nf <;> simp [Complex.I_sq]

theorem topState_summable_norm : Summable (fun ν => ‖topState.val ν‖) := by
  have h := FiberL1.summable_norm (FiberL1.clusterLift topState.val)
  have hP := (mem_clusterSpace_iff _).mp topState.property
  change Summable (fun ν => ‖clusterProjection topState.val ν‖) at h
  rwa [hP] at h

theorem topState_fourier_sum (x : Space) :
    antiperiodicField topState.val x =
      ∑ s : Corner.Parity, spatialPhase (aliasMomentum 0 (cubeAlias s)) x •
        momentumVector (realMomentum (Corner.normalizedClusterVector s)) := by
  have hs : Function.support (fun ν => spatialPhase (aliasMomentum 0 ν) x • topState.val ν) ⊆
      {ν | IsCentralAlias ν} := by
    intro ν hν
    by_contra hn
    apply hν
    change spatialPhase (aliasMomentum 0 ν) x • pack (realCube Corner.normalizedClusterVector) ν = 0
    rw [pack_noncentral _ _ hn, smul_zero]
  calc
    _ = ∑' ν, spatialPhase (aliasMomentum 0 ν) x • topState.val ν :=
      (antiperiodicField_hasSum _ topState_summable_norm x).tsum_eq.symm
    _ = ∑' ν : CentralAlias, spatialPhase (aliasMomentum 0 ν.val) x • topState.val ν.val :=
      (tsum_subtype_eq_of_support_subset hs).symm
    _ = ∑' s : Corner.Parity, spatialPhase (aliasMomentum 0 (cubeAlias s)) x •
        topState.val (cubeAlias s) :=
      (parityAliasEquiv.tsum_eq (fun ν : CentralAlias =>
        spatialPhase (aliasMomentum 0 ν.val) x • topState.val ν.val)).symm
    _ = _ := by simp only [tsum_fintype, topState, packReal, pack_alias, realCube]

def referenceField (x : Space) : Polarization :=
  (Real.sqrt 8 : ℂ) • trigField Corner.normalizedTopVector x

theorem referenceField_eq_fourier (x : Space) :
    referenceField x = Complex.I • antiperiodicField topState.val x := by
  rw [topState_fourier_sum]
  have hscale (s : Corner.Parity) :
      momentumVector (realMomentum (Corner.normalizedClusterVector s)) =
        ((Real.sqrt 8 : ℝ) : ℂ)⁻¹ •
          momentumVector (realMomentum (Corner.embedding Corner.selectedParity Corner.normalizedTopVector s)) := by
    apply PiLp.ext
    intro j
    simp [Corner.normalizedClusterVector, momentumVector, realMomentum]
  simp_rw [hscale, smul_comm (spatialPhase _ x)]
  rw [← Finset.smul_sum, smul_comm Complex.I, selected_fourier_sum, smul_smul]
  have hs : ((Real.sqrt 8 : ℝ) : ℂ)⁻¹ * 8 = (Real.sqrt 8 : ℂ) := by
    have hn : ((Real.sqrt 8 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast Real.sqrt_ne_zero'.mpr (by norm_num : (0:ℝ)<8)
    have hsq : ((Real.sqrt 8 : ℝ) : ℂ)^2 = 8 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ)≤8)
    rw [← hsq, pow_two, ← mul_assoc, inv_mul_cancel₀ hn, one_mul]
  rw [hs]
  rfl

#print axioms referenceField_eq_fourier

end Maxwell.Continuum.CellBandFourier
