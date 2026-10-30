import Maxwell.Continuum.CalibrationSupercellPointwise
import Maxwell.Continuum.CalibrationSupercellTranslation
import Maxwell.Continuum.CalibrationSupercellTranslatedRange

/-! Fourier translation is literal physical translation on well-supported
supercell fields. The support condition prevents any wrap at the torus cut. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048
set_option maxHeartbeats 1000000

namespace Maxwell.Continuum.Calibration.Supercell

open FreeFiber CellGauge CellBandFourier UnitAddTorus MeasureTheory Set EffectiveMass
open Bloch (fieldTranslation fieldTranslation_ae integerVector integerVector_apply)

variable (M : ℕ) [NeZero M]

theorem radius_neg (a : Alias) : imageRadius (-a)=imageRadius a := by
  simp only [imageRadius,Pi.neg_apply,Int.natAbs_neg]

theorem phase_character (a n : Alias) :
    exactPhase M a n=mFourier n (torusPoint M (latticeShift a)) := by
  rw [character_phase,exactPhase_exp]
  simp only [spatialPhase,realMomentum,latticeShift,PiLp.smul_apply,integerVector_apply,
    smul_eq_mul,Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_natCast,
    Complex.ofReal_ofNat,Complex.ofReal_intCast,Fin.sum_univ_three,
    Int.cast_add,Int.cast_mul]
  congr 1
  ring

theorem character_sub_lattice (a n : Alias) (x : Space) :
    mFourier n (torusPoint M (x-latticeShift a))=
      star (exactPhase M a n)*mFourier n (torusPoint M x) := by
  have hp : spatialPhase (realMomentum (fun i => Real.pi*(n i : ℝ)/(M : ℝ)))
      (-latticeShift a)=(exactPhase M a n)⁻¹ := by
    rw [phase_character,character_phase]
    simp only [spatialPhase,PiLp.neg_apply,Complex.ofReal_neg,mul_neg,
      Finset.sum_neg_distrib,Complex.exp_neg]
  rw [character_phase,sub_eq_add_neg,spatialPhase_space_add,hp,
    Complex.inv_eq_conj (exactPhase_norm M a n),← Complex.star_def,
    ← character_phase,mul_comm]

theorem Qh_translated_single (hEven : Even M) {L : ℝ} (hL : 1≤L) (a n : Alias)
    (hM : 16*(L+(imageRadius a : ℝ)+1)≤(M : ℝ)) (v : Polarization) :
    Qh L⁻¹ (fieldTranslation (-latticeShift a) (embedding M (lp.single 2 n v)))=
      star (exactPhase M a n) • Qh L⁻¹ (embedding M (lp.single 2 n v)) := by
  have hM0 : 16*(L+1)≤(M : ℝ) := by
    have hrad : (0 : ℝ) ≤ (imageRadius a : ℝ) := by positivity
    linarith only [hM,hrad]
  have hMa : 16*(L+(imageRadius (-a) : ℝ)+1)≤(M : ℝ) := by rwa [radius_neg]
  apply PiLp.ext
  intro i
  apply Lp.ext
  have ht := (measurePreserving_add_right volume (-latticeShift a)).quasiMeasurePreserving.ae_eq_comp
    (embedding_single_indicator M hEven n v i)
  filter_upwards [Qh_ae L⁻¹ (fieldTranslation (-latticeShift a)
      (embedding M (lp.single 2 n v))) i,
    fieldTranslation_ae (-latticeShift a) (embedding M (lp.single 2 n v)) i,
    ht,Qh_ae L⁻¹ (embedding M (lp.single 2 n v)) i,
    embedding_single_indicator M hEven n v i,
    Lp.coeFn_smul (star (exactPhase M a n)) (Qh L⁻¹ (embedding M (lp.single 2 n v)) i)]
      with x hq htr ht hqu he hs
  change _=(star (exactPhase M a n) • (Qh L⁻¹ (embedding M (lp.single 2 n v)) i)) x
  dsimp only [Function.comp_apply] at ht
  rw [hq,htr,ht,hs]
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [hqu,he]
  by_cases hx : ‖x‖≤L
  · have hc : cellIndex x∈representedCells M :=
      ballCells_subset_represented M hL hM0 (cellIndex_mem_ballCells hx)
    have hca : cellIndex (x+-latticeShift a)∈representedCells M := by
      apply wellCells_subset_represented M hL (-a) hMa
      apply cellIndex_mem_wellCells (-a)
      have hn : latticeShift (-a)=-latticeShift a := by
        apply PiLp.ext
        intro j
        simp only [latticeShift,PiLp.smul_apply,integerVector_apply,Pi.neg_apply,
          Int.cast_neg,PiLp.neg_apply,smul_eq_mul,mul_neg]
      simpa only [hn,add_sub_cancel_right] using hx
    rw [ite_eq_left hc,ite_eq_left hca]
    rw [← sub_eq_add_neg,character_sub_lattice]
    ring
  · have hz : Well.qw (L⁻¹ • x)=0 := by
      apply (Well.qw_zero_iff _).mpr
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (by linarith : 0<L))]
      apply (le_inv_mul_iff₀ (by linarith : 0<L)).mpr
      simpa only [mul_one] using (le_of_not_ge hx)
    rw [hz,Complex.ofReal_zero,zero_mul,zero_mul,mul_zero]

#print axioms Qh_translated_single

end Maxwell.Continuum.Calibration.Supercell
