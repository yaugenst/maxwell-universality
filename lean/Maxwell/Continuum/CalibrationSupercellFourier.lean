import Maxwell.Continuum.CalibrationSupercellEmbedding
import Maxwell.Continuum.CellBlochWave

/-! The physical supercell embedding sends each complete alias to the
literal Fourier character of period `2M`, on exactly its selected cells. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048

namespace Maxwell.Continuum.Calibration.Supercell

open FreeFiber CellGauge CellBandFourier UnitAddTorus MeasureTheory Set

variable (M : ℕ) [NeZero M]

def torusPoint (x : Space) : Torus := fun i => ((x i/(2*(M : ℝ)) : ℝ) : UnitAddCircle)

omit [NeZero M] in
theorem torusPoint_measurable : Measurable (torusPoint M) := by
  apply Measurable.of_eval
  intro i
  exact (AddCircle.continuous_mk' (1 : ℝ)).measurable.comp
    (((measurable_pi_apply i).comp (WithLp.measurable_ofLp 2 (Fin 3 → ℝ))).div_const _)

omit [NeZero M] in
theorem character_phase (n : Alias) (x : Space) :
    mFourier n (torusPoint M x)=
      spatialPhase (realMomentum (fun i => Real.pi*(n i : ℝ)/(M : ℝ))) x := by
  simp only [mFourier, ContinuousMap.coe_mk, torusPoint, fourier_coe_apply,
    Fin.prod_univ_three, spatialPhase, realMomentum, Fin.sum_univ_three,
    Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_ofNat,
    Complex.ofReal_intCast, Complex.ofReal_one]
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  field_simp

omit [NeZero M] in
theorem embedCell_function_ae (f : CellFieldL2) (g : Space → ℂ) (i : Fin 3)
    (hf : f i =ᵐ[torusMeasure] fun t => g (spatialEquiv t).val) :
    embedCell f i =ᵐ[volume] physicalCell.indicator g := by
  have h₁ := spatialEquiv_measurePreserving.symm.quasiMeasurePreserving.ae_eq_comp
    (spatialUnitary_ae (spatialUnitary.symm f) i)
  have h₂ := spatialEquiv_measurePreserving.symm.quasiMeasurePreserving.ae_eq_comp hf
  have he : spatialUnitary.symm f i =ᵐ[cellMeanMeasure] fun x => g x.val := by
    filter_upwards [h₁,h₂] with x h₁ h₂
    simp only [Function.comp_apply,spatialUnitary.apply_symm_apply,
      spatialEquiv.apply_symm_apply] at h₁ h₂
    exact h₁.symm.trans h₂
  filter_upwards [extendField_ae (spatialUnitary.symm f) i,
    extendFunction_ae_congr he] with x hx he
  change extendField (spatialUnitary.symm f) i x=_
  rw [hx,he]
  by_cases hc : x∈physicalCell
  · rw [indicator_of_mem hc]
    exact extendFunction_coe (fun y : physicalCell => g y.val) ⟨x,hc⟩
  · rw [indicator_of_notMem hc,extendFunction_zero _ hc]

omit [NeZero M] in
theorem embedLatticeCell_function_ae (a : Alias) (f : CellFieldL2)
    (g : Space → ℂ) (i : Fin 3)
    (hf : f i =ᵐ[torusMeasure] fun t => g (spatialEquiv t).val) :
    embedLatticeCell a f i =ᵐ[volume]
      (spatialBox a).indicator (fun x => g (x-latticeShift a)) := by
  have he := (measurePreserving_add_right volume (-latticeShift a)).quasiMeasurePreserving.ae_eq_comp
    (embedCell_function_ae f g i hf)
  filter_upwards [Bloch.fieldTranslation_ae (-latticeShift a) (embedCell f) i,he] with x hx he
  change Bloch.fieldTranslation (-latticeShift a) (embedCell f) i x=_
  dsimp only [Function.comp_apply] at he
  rw [hx,he]
  by_cases hc : x∈spatialBox a
  · rw [indicator_of_mem hc,indicator_of_mem (show x + -latticeShift a∈physicalCell from hc)]
    rfl
  · rw [indicator_of_notMem hc,
      indicator_of_notMem (show x + -latticeShift a∉physicalCell from hc)]

theorem single_summable (n : Alias) (v : Polarization) :
    Summable (fun k => ‖(lp.single 2 n v : FiberSpace) k‖) := by
  classical
  apply summable_of_ne_finset_zero (s := {n})
  intro k hk
  simp only [Finset.mem_singleton] at hk
  simp [hk]

theorem blochField_single (q : Momentum) (n : Alias) (v : Polarization) (x : Space) :
    blochField q (lp.single 2 n v) x=
      (spatialPhase q x*(carrier x*mFourier n (CellBandFourier.torusPoint x))) • v := by
  classical
  unfold blochField antiperiodicField periodicField
  rw [periodicSeries_apply_tsum _ (single_summable n v)]
  simp only [lp.coeFn_single,Pi.single_apply,smul_ite,smul_zero,tsum_ite_eq,
    smul_smul]

theorem unitary_single (j : Grid M) (n : Alias) (v : Polarization) :
    unitary M (lp.single 2 (join M (j,n)) v)=PiLp.single 2 j (lp.single 2 n v) := by
  classical
  apply PiLp.ext
  intro k
  apply lp.ext
  funext ν
  rw [unitary_apply]
  by_cases hk : k=j
  · subst k
    have he : join M (j,ν)=join M (j,n) ↔ ν=n := by
      constructor
      · intro h
        exact congrArg Prod.snd ((indexEquiv M).injective h)
      · intro h
        rw [h]
    simp only [PiLp.single_apply,ite_true,lp.coeFn_single,Pi.single_apply,he]
  · have he : join M (k,ν)≠join M (j,n) := by
      intro h
      exact hk (congrArg Prod.fst ((indexEquiv M).injective h))
    simp only [PiLp.single_apply,ite_eq_right hk,lp.coeFn_single,Pi.single_apply,
      ite_eq_right he,lp.coeFn_zero,Pi.zero_apply]

theorem embedding_single_join (j : Grid M) (n : Alias) (v : Polarization) :
    embedding M (lp.single 2 (join M (j,n)) v)=
      (physicalFactor M : ℂ) • ∑ a : Grid M,
        cellPhase M j (representative M a) •
          embedLatticeCell (representative M a) (cellUnitary M j (lp.single 2 n v)) := by
  classical
  rw [embedding_apply,unitary_single,blockEmbedding_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_eq_single j]
  · simp only [PiLp.single_apply,ite_true]
  · intro b _ hbj
    simp only [PiLp.single_apply,ite_eq_right hbj,map_zero,smul_zero]
  · simp

theorem embedding_single_ae (hEven : Even M) (n : Alias) (v : Polarization) (i : Fin 3) :
    embedding M (lp.single 2 n v) i =ᵐ[volume] fun x =>
      (physicalFactor M : ℂ) * ∑ a : Grid M,
        (spatialBox (representative M a)).indicator
          (fun x => mFourier n (torusPoint M x)*v i) x := by
  classical
  obtain ⟨⟨j,ν⟩,rfl⟩ := (indexEquiv M).surjective n
  change embedding M (lp.single 2 (join M (j,ν)) v) i =ᵐ[volume] fun x =>
    (physicalFactor M : ℂ) * ∑ a : Grid M,
      (spatialBox (representative M a)).indicator
        (fun x => mFourier (join M (j,ν)) (torusPoint M x)*v i) x
  rw [embedding_single_join]
  have hf (a : Grid M) := embedLatticeCell_function_ae (representative M a)
    (cellUnitary M j (lp.single 2 ν v)) (fun x => blochField (momentum M j) (lp.single 2 ν v) x i) i
    (gauged_unitary_ae (momentum M j) (lp.single 2 ν v) (single_summable ν v) i)
  have hs : (∑ a : Grid M, cellPhase M j (representative M a) •
      embedLatticeCell (representative M a) (cellUnitary M j (lp.single 2 ν v))) i =
      ∑ a : Grid M, cellPhase M j (representative M a) •
        (embedLatticeCell (representative M a) (cellUnitary M j (lp.single 2 ν v)) i) := by
    rw [WithLp.ofLp_sum,Finset.sum_apply]
    rfl
  simp only [PiLp.smul_apply,hs]
  filter_upwards [Lp.coeFn_smul (physicalFactor M : ℂ)
    (∑ a : Grid M, cellPhase M j (representative M a) •
      (embedLatticeCell (representative M a) (cellUnitary M j (lp.single 2 ν v)) i)),
    Lp.coeFn_finsetSum Finset.univ (fun a : Grid M =>
      cellPhase M j (representative M a) •
        (embedLatticeCell (representative M a) (cellUnitary M j (lp.single 2 ν v)) i)),
    ae_all_iff.mpr hf,
    ae_all_iff.mpr (fun a : Grid M => Lp.coeFn_smul
      (cellPhase M j (representative M a))
      (embedLatticeCell (representative M a) (cellUnitary M j (lp.single 2 ν v)) i))]
      with x hsm hsum he hc
  rw [hsm]
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [hsum]
  simp only [Finset.sum_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  rw [hc a]
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [he a]
  by_cases hx : x∈spatialBox (representative M a)
  · rw [indicator_of_mem hx,indicator_of_mem hx,blochField_single]
    simp only [PiLp.smul_apply,smul_eq_mul]
    have hp := join_cell_phase M hEven j ν (representative M a)
      (x-latticeShift (representative M a))
    rw [show latticeShift (representative M a)+(x-latticeShift (representative M a))=x by abel] at hp
    rw [character_phase,hp]
    ring
  · rw [indicator_of_notMem hx,indicator_of_notMem hx,mul_zero]

#print axioms embedding_single_ae

end Maxwell.Continuum.Calibration.Supercell
