import Maxwell.Continuum.CalibrationSupercellPointwise
import Maxwell.Continuum.TemplateFrequencyScaling
import Maxwell.Continuum.FiniteAuxiliarySite

/-! Exact physical representatives for finite supercell Fourier arrays.
The tensor-template frequencies use cycles per unit length, hence the
factor `2M` in the supercell frequency. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048
set_option maxHeartbeats 800000

namespace Maxwell.Continuum.Calibration.Supercell

open FreeFiber CellGauge CellBandFourier UnitAddTorus MeasureTheory Set
open EffectiveMass FiniteAuxiliary Profile

variable (M : ℕ) [NeZero M]

def templateFrequency (L : ℚ) (n : Alias) (i : Fin 3) : ℚ :=
  L*(n i : ℚ)/(2*(M : ℚ))

theorem templateFrequency_bound (L : ℚ) (R Q : ℕ)
    (hRQ : |L| * (R : ℚ)≤2*(M : ℚ)*Q) {n : Alias}
    (hn : n∈PeriodicSampling.Product.frequencyCube R) (i : Fin 3) :
    |templateFrequency M L n i|≤Q := by
  have hm₀ : (0 : ℚ)<M := by exact_mod_cast NeZero.pos M
  have hm : (0 : ℚ)<2*(M : ℚ) := by positivity
  rw [templateFrequency,abs_div,abs_mul,abs_of_pos hm]
  apply (div_le_iff₀ hm).mpr
  have hn' : |(n i : ℚ)|≤(R : ℚ) := by
    exact_mod_cast (PeriodicSampling.Product.mem_frequencyCube R n).mp hn i
  exact (mul_le_mul_of_nonneg_left hn' (abs_nonneg L)).trans (by simpa [mul_comm] using hRQ)

theorem templateFrequency_character (L : ℚ) (hL : L≠0) (n : Alias) (x : Space) :
    spatialPlaneWave (templateFrequency M L n) (fun i => (L : ℝ)⁻¹*x i)=
      mFourier n (torusPoint M x) := by
  rw [character_phase]
  unfold spatialPlaneWave templateFrequency spatialPhase realMomentum
  congr 1
  simp only [Rat.cast_div,Rat.cast_mul,Rat.cast_intCast,Rat.cast_ofNat,Rat.cast_natCast,
    Fin.sum_univ_three]
  push_cast
  field_simp [show (L : ℂ)≠0 by exact_mod_cast hL,show (M : ℂ)≠0 by exact_mod_cast NeZero.ne M]

theorem sum_single_eq (s : Finset Alias) (u : FiberSpace)
    (hu : ∀n∉s, u n=0) : (∑n∈s, lp.single 2 n (u n) : FiberSpace)=u := by
  classical
  apply lp.ext
  funext n
  simp only [lp.coeFn_sum,Finset.sum_apply,lp.coeFn_single,Pi.single_apply]
  by_cases hn : n∈s
  · simpa only [eq_comm,hn,ite_eq_left] using Finset.sum_ite_eq s n (fun k => u k)
  · rw [Finset.sum_eq_zero]
    · exact (hu n hn).symm
    · intro k hk
      exact ite_eq_right (show n≠k from fun h => hn (h ▸ hk))

theorem embedding_finite_ae (hEven : Even M) (s : Finset Alias) (u : FiberSpace)
    (hu : ∀n∉s, u n=0) (i : Fin 3) :
    embedding M u i =ᵐ[volume] fun x =>
      if cellIndex x∈representedCells M then
        (physicalFactor M : ℂ)*∑n∈s, mFourier n (torusPoint M x)*u n i else 0 := by
  classical
  have he : embedding M u i =∑n∈s, embedding M (lp.single 2 n (u n)) i := by
    calc
      _ = embedding M (∑n∈s,lp.single 2 n (u n)) i :=
        congrArg (fun v : FiberSpace => embedding M v i) (sum_single_eq s u hu).symm
      _ = _ := by rw [map_sum,WithLp.ofLp_sum,Finset.sum_apply]
  rw [he]
  filter_upwards [Lp.coeFn_finsetSum s (fun n => embedding M (lp.single 2 n (u n)) i),
    ae_all_iff.mpr (fun n => embedding_single_indicator M hEven n (u n) i)] with x hs hx
  rw [hs]
  simp only [Finset.sum_apply]
  simp_rw [hx]
  by_cases hc : cellIndex x∈representedCells M
  · simp only [ite_eq_left hc,Finset.mul_sum,mul_assoc]
  · simp only [ite_eq_right hc,Finset.sum_const_zero]

theorem Qh_embedding_finite_ae (hEven : Even M) {L : ℝ} (hL : 1≤L)
    (hM : 16*(L+1)≤(M : ℝ)) (s : Finset Alias) (u : FiberSpace)
    (hu : ∀n∉s, u n=0) (i : Fin 3) :
    Qh L⁻¹ (embedding M u) i =ᵐ[volume] fun x =>
      (Well.qw (L⁻¹ • x) : ℂ)*(physicalFactor M : ℂ)*
        ∑n∈s, mFourier n (torusPoint M x)*u n i := by
  filter_upwards [Qh_ae L⁻¹ (embedding M u) i,embedding_finite_ae M hEven s u hu i]
    with x hq he
  rw [hq,he]
  by_cases hx : cellIndex x∈representedCells M
  · rw [ite_eq_left hx]
    ring
  · rw [ite_eq_right hx,mul_zero]
    have ho : L≤‖x‖ := by
      by_contra hn
      apply hx
      apply ballCells_subset_represented M hL hM
      exact cellIndex_mem_ballCells (lt_of_not_ge hn).le
    have hw : Well.qw (L⁻¹ • x)=0 :=
      (Well.qw_zero_iff _).mpr (by
        simpa only [sub_zero] using scaled_outside_unit (zero_lt_one.trans_le hL) 0 x
          (by simpa only [sub_zero] using ho))
    rw [hw,Complex.ofReal_zero,zero_mul,zero_mul]

theorem siteInsertion_embedding_finite_ae (hEven : Even M) {L : ℝ} (hL : 1≤L)
    (hM : 16*(L+1)≤(M : ℝ)) (s : Finset Alias) (u : FiberSpace)
    (hu : ∀n∉s, u n=0) (r : Space) (i : Fin 3) :
    siteInsertion L⁻¹ r (embedding M u) i =ᵐ[volume] fun x =>
      (Well.qw (L⁻¹ • (x-r)) : ℂ)*(physicalFactor M : ℂ)*
        ∑n∈s, mFourier n (torusPoint M (x-r))*u n i := by
  have he := (measurePreserving_add_right volume (-r)).quasiMeasurePreserving.ae_eq_comp
    (Qh_embedding_finite_ae M hEven hL hM s u hu i)
  filter_upwards [Bloch.fieldTranslation_ae (-r) (Qh L⁻¹ (embedding M u)) i,he]
    with x ht he
  change Bloch.fieldTranslation (-r) (Qh L⁻¹ (embedding M u)) i x=_
  simpa only [Function.comp_apply,sub_eq_add_neg] using ht.trans he

#print axioms templateFrequency_character
#print axioms siteInsertion_embedding_finite_ae

end Maxwell.Continuum.Calibration.Supercell
