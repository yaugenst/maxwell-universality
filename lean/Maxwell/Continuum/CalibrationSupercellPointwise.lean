import Maxwell.Continuum.CalibrationSupercellFourier
import Maxwell.Continuum.CalibrationSupercellRange
import Maxwell.Continuum.CalibrationFiniteSeed

/-! Literal pointwise representatives for the selected supercell and
for a full Fourier field injected into any one Bloch-grid block. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048

namespace Maxwell.Continuum.Calibration.Supercell

open FreeFiber CellGauge CellBandFourier UnitAddTorus MeasureTheory Set PeriodicSampling

variable (M : ℕ) [NeZero M]

theorem represented_sum_indicator (g : Space → ℂ) (x : Space) :
    (∑ a : Grid M, (spatialBox (representative M a)).indicator g x)=
      if cellIndex x∈representedCells M then g x else 0 := by
  classical
  calc
    _ = ∑ a ∈ representedCells M, (spatialBox a).indicator g x := by
      rw [representedCells,Finset.sum_map]
      rfl
    _ = _ := by
      simp only [Set.indicator_apply,spatialBox_iff_index]
      exact Finset.sum_ite_eq _ _ _

theorem embedding_single_indicator (hEven : Even M) (n : Alias) (v : Polarization) (i : Fin 3) :
    embedding M (lp.single 2 n v) i =ᵐ[volume] fun x =>
      if cellIndex x∈representedCells M then
        (physicalFactor M : ℂ)*mFourier n (torusPoint M x)*v i else 0 := by
  filter_upwards [embedding_single_ae M hEven n v i] with x hx
  rw [hx,represented_sum_indicator]
  split_ifs <;> simp only [mul_zero,mul_assoc]

theorem embedding_injection (j : Grid M) (u : FiberSpace) :
    embedding M (injection M j u)=(physicalFactor M : ℂ) • ∑ a : Grid M,
      cellPhase M j (representative M a) • embedLatticeCell (representative M a) (cellUnitary M j u) := by
  classical
  rw [embedding_apply,injection,LinearIsometryEquiv.apply_symm_apply,blockEmbedding_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_eq_single j]
  · simp only [PiLp.single_apply,ite_true]
  · intro b _ hbj
    simp only [PiLp.single_apply,ite_eq_right hbj,map_zero,smul_zero]
  · simp

theorem embedding_injection_ae (j : Grid M) (u : FiberSpace)
    (hu : Summable (fun n => ‖u n‖)) (i : Fin 3) :
    embedding M (injection M j u) i =ᵐ[volume] fun x =>
      (physicalFactor M : ℂ) * ∑ a : Grid M,
        (spatialBox (representative M a)).indicator
          (fun x => cellPhase M j (representative M a)*
            blochField (momentum M j) u (x-latticeShift (representative M a)) i) x := by
  classical
  rw [embedding_injection]
  have hf (a : Grid M) := embedLatticeCell_function_ae (representative M a)
    (cellUnitary M j u) (fun x => blochField (momentum M j) u x i) i
    (gauged_unitary_ae (momentum M j) u hu i)
  have hs : (∑ a : Grid M, cellPhase M j (representative M a) •
      embedLatticeCell (representative M a) (cellUnitary M j u)) i =
      ∑ a : Grid M, cellPhase M j (representative M a) •
        (embedLatticeCell (representative M a) (cellUnitary M j u) i) := by
    rw [WithLp.ofLp_sum,Finset.sum_apply]
    rfl
  simp only [PiLp.smul_apply,hs]
  filter_upwards [Lp.coeFn_smul (physicalFactor M : ℂ)
    (∑ a : Grid M, cellPhase M j (representative M a) •
      (embedLatticeCell (representative M a) (cellUnitary M j u) i)),
    Lp.coeFn_finsetSum Finset.univ (fun a : Grid M =>
      cellPhase M j (representative M a) •
        (embedLatticeCell (representative M a) (cellUnitary M j u) i)),
    ae_all_iff.mpr hf,
    ae_all_iff.mpr (fun a : Grid M => Lp.coeFn_smul
      (cellPhase M j (representative M a))
      (embedLatticeCell (representative M a) (cellUnitary M j u) i))]
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
  · rw [indicator_of_mem hx,indicator_of_mem hx]
  · rw [indicator_of_notMem hx,indicator_of_notMem hx,mul_zero]

omit [NeZero M] in
theorem momentum_zero : momentum M 0=0 := by
  funext i
  simp [momentum,realMomentum,centeredGrid,gridTurn]

theorem cellPhase_zero (a : Alias) : cellPhase M 0 a=carrier (latticeShift a) := by
  rw [cellPhase,character_comm,character_zero,mul_one]

theorem antiperiodicField_lattice (u : FiberSpace) (x : Space) (a : Alias) :
    antiperiodicField u (x+latticeShift a)=carrier (latticeShift a) • antiperiodicField u x := by
  rw [antiperiodicField,carrier_add,
    show periodicField u (x+latticeShift a)=periodicField u x from periodicField_period u x a]
  simp only [antiperiodicField,smul_smul,mul_comm]

theorem embedding_injection_zero_ae (u : FiberSpace)
    (hu : Summable (fun n => ‖u n‖)) (i : Fin 3) :
    embedding M (injection M 0 u) i =ᵐ[volume] fun x =>
      if cellIndex x∈representedCells M then
        (physicalFactor M : ℂ)*antiperiodicField u x i else 0 := by
  filter_upwards [embedding_injection_ae M 0 u hu i] with x hx
  rw [hx]
  have hp (a : Grid M) (y : Space) :
      cellPhase M 0 (representative M a)*blochField (momentum M 0) u
        (y-latticeShift (representative M a)) i=antiperiodicField u y i := by
    rw [cellPhase_zero,momentum_zero,blochField]
    have hz : spatialPhase 0 (y-latticeShift (representative M a))=1 := by
      simp [spatialPhase]
    rw [hz,one_smul]
    have he := congrArg (fun v : Polarization => v i)
      (antiperiodicField_lattice u (y-latticeShift (representative M a)) (representative M a))
    rw [sub_add_cancel] at he
    exact he.symm
  simp_rw [hp]
  rw [represented_sum_indicator]
  split_ifs <;> simp only [mul_zero]

#print axioms embedding_injection_zero_ae

end Maxwell.Continuum.Calibration.Supercell
