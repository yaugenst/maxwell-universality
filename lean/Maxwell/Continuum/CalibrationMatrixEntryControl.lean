import Maxwell.Continuum.CalibrationMatrixEntryGuard
import Maxwell.Continuum.CalibrationNeighborSum
import Maxwell.Continuum.CalibrationRawFreePreservation

/-! One fixed scalar program evaluates the literal cached transition
matrix entry. All alias tests, polarization choices, and inverse domains
are discharged from the coordinate inputs and calibration box. -/

namespace Maxwell.Continuum.Calibration.RawFree

open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow FreeFiber
set_option maxHeartbeats 4500000
set_option maxRecDepth 16384

def matrixFinish : Control := .step (.literal 37 rationalAmplitude)
  (.step (.binary .mul 12 12 36) (.step (.binary .mul 12 37 12) .done))
def matrixYes : Control := indexedFreeControl.andThen (neighborSumControl.andThen matrixFinish)
def matrixTail : Control := .positive 39 matrixYes (.step (.literal 12 0) .done)
def matrixControl : Control := matrixTail.prepend matrixGuardInstructions

theorem stage_subset_neighbors : stageRegisters ⊆ neighborRegisters := by
  intro k hk
  simp only [stageRegisters,Finset.mem_range] at hk
  simpa only [neighborRegisters,Finset.mem_range] using (by omega : k<41)

theorem matrixFinish_valid : matrixFinish.Valid neighborRegisters := by
  simp [matrixFinish,Control.Valid,Instruction.Valid,neighborRegisters]
theorem matrixFinish_admissible (v : ℕ → Parts) : matrixFinish.AdmissibleTrace v := by
  simp [matrixFinish,Control.AdmissibleTrace,Instruction.Admissible]
theorem matrixFinish_output (v : ℕ → Parts) : matrixFinish.evaluate v 12=
    (Parts.literal rationalAmplitude).mul ((v 12).mul (v 36)) := by
  simp [matrixFinish,Control.evaluate,Instruction.update,BinaryOp.eval]

theorem matrixYes_valid : matrixYes.Valid neighborRegisters :=
  Control.andThen_valid _ _ _ (indexedFree_valid.mono stage_subset_neighbors)
    (Control.andThen_valid _ _ _ neighborSum_valid matrixFinish_valid)

theorem matrixYes_contract (v : ℕ → Parts) (hg : Good neighborRegisters v)
    (ν μ : Alias) (hν : ∀ k, (coordinates v k).value=(ν k : ℚ))
    (hμ : ∀ k, (columnCoordinates v k).value=(μ k : ℚ))
    (htbox : (3 : ℝ) ≤ (v 0).value)
    (hEbox : (7 : ℝ) ≤ (v 1).value ∧ ((v 1).value : ℝ) ≤ 8)
    (hrbox : ∀ k, |((quasiParts v k).value : ℝ)| ≤ 1/16)
    (i j : Fin 3) (hi : (v 23).value=(i.val : ℚ)) (hj : (v 24).value=(j.val : ℚ)) :
    matrixYes.AdmissibleTrace v ∧
      (matrixYes.evaluate v 12).value=rationalAmplitude*
        rationalFreeInverseMatrix (v 0).value (v 1).value (fun k => (quasiParts v k).value) ν i j*
          neighborWeight ν μ := by
  obtain ⟨fa,fvalue⟩ := indexedFree_contract v (fun k hk => hg k (stage_subset_neighbors hk))
    ν hν htbox hEbox hrbox i j hi hj
  let w := indexedFreeControl.evaluate v
  have gw : Good neighborRegisters w := indexedFreeControl.evaluate_good neighborRegisters
    (indexedFree_valid.mono stage_subset_neighbors) v hg fa
  have hνw (k : Fin 3) : (coordinates w k).value=(ν k : ℚ) := by
    have he : coordinates w k=coordinates v k := by fin_cases k <;> exact indexedFree_other v _ (by omega)
    rw [he]; exact hν k
  have hμw (k : Fin 3) : (columnCoordinates w k).value=(μ k : ℚ) := by
    have he : columnCoordinates w k=columnCoordinates v k := by fin_cases k <;> exact indexedFree_other v _ (by omega)
    rw [he]; exact hμ k
  have nv := neighborSum_value w gw ν μ hνw hμw
  have nk : neighborSumControl.evaluate w 12=w 12 := neighborSum_other w 12 (by omega)
  refine ⟨Control.andThen_admissible _ _ v fa
    (Control.andThen_admissible _ _ w (neighborSum_admissible w) (matrixFinish_admissible _)),?_⟩
  rw [matrixYes,Control.andThen_evaluate,Control.andThen_evaluate,matrixFinish_output,
    Parts.mul_value,Parts.mul_value,Parts.literal_value]
  change rationalAmplitude*((neighborSumControl.evaluate w 12).value*
    (neighborSumControl.evaluate w 36).value)=_
  rw [nk,nv]
  change rationalAmplitude*((indexedFreeControl.evaluate v 12).value*neighborWeight ν μ)=_
  rw [fvalue]
  ring

theorem matrixControl_valid : matrixControl.Valid neighborRegisters :=
  Control.prepend_valid _ _ _ matrixGuard_valid
    ⟨by change 39∈Finset.range 41; decide,matrixYes_valid,
      ⟨by change 12∈Finset.range 41; decide,trivial⟩⟩

theorem matrixControl_steps : matrixControl.steps=180 := by
  rw [matrixControl,Control.prepend_steps]
  simp only [matrixTail,Control.steps,matrixYes,Control.andThen_steps,indexedFree_steps,
    neighborSum_steps,matrixFinish]
  rfl

theorem matrixControl_contract (v : ℕ → Parts) (hg : Good neighborRegisters v)
    (ν μ : Alias) (hν : ∀ k, (coordinates v k).value=(ν k : ℚ))
    (hμ : ∀ k, (columnCoordinates v k).value=(μ k : ℚ))
    (htbox : (3 : ℝ) ≤ (v 0).value)
    (hEbox : (7 : ℝ) ≤ (v 1).value ∧ ((v 1).value : ℝ) ≤ 8)
    (hrbox : ∀ k, |((quasiParts v k).value : ℝ)| ≤ 1/16)
    (i j : Fin 3) (hi : (v 23).value=(i.val : ℚ)) (hj : (v 24).value=(j.val : ℚ)) :
    matrixControl.AdmissibleTrace v ∧
      (matrixControl.evaluate v 12).value=stencilEntry (v 0).value (v 1).value
        (fun k => (quasiParts v k).value) ν i μ j := by
  let w := matrixGuard v
  have gw := matrixGuard_good v hg
  have keep (k : ℕ) (hk : k≠20 ∧ k≠21 ∧ k≠22 ∧ k≠37 ∧ k≠38 ∧ k≠39) : w k=v k := matrixGuard_keep v k hk
  have hνw (k : Fin 3) : (coordinates w k).value=(ν k : ℚ) := by
    have he : coordinates w k=coordinates v k := by
      fin_cases k
      · exact keep 13 (by decide)
      · exact keep 14 (by decide)
      · exact keep 15 (by decide)
    rw [he]; exact hν k
  have hμw (k : Fin 3) : (columnCoordinates w k).value=(μ k : ℚ) := by
    have he : columnCoordinates w k=columnCoordinates v k := by
      fin_cases k
      · exact keep 28 (by decide)
      · exact keep 29 (by decide)
      · exact keep 30 (by decide)
    rw [he]; exact hμ k
  have hrw : quasiParts w=quasiParts v := by
    funext k
    fin_cases k
    · exact keep 16 (by decide)
    · exact keep 17 (by decide)
    · exact keep 18 (by decide)
  have h0 := keep 0 (by omega)
  have h1 := keep 1 (by omega)
  obtain ⟨ya,yv⟩ := matrixYes_contract w gw ν μ hνw hμw
    (by simpa only [h0] using htbox) (by simpa only [h1] using hEbox)
    (by simpa only [hrw] using hrbox) i j
    (by simpa only [keep 23 (by omega)] using hi) (by simpa only [keep 24 (by omega)] using hj)
  have gadm : matrixTail.AdmissibleTrace w := by
    simp only [matrixTail,Control.AdmissibleTrace]
    split_ifs
    · exact ya
    · trivial
  refine ⟨Control.prepend_admissibleTrace _ _ v (matrixGuard_admissible v) gadm,?_⟩
  rw [matrixControl,Control.prepend_evaluate,stencilEntry_factor]
  change (matrixTail.evaluate w 12).value=_
  have hp := matrixGuard_noncentral v hg ν μ hν hμ
  by_cases ht : 0<(w 39).value
  · obtain ⟨hn,hm⟩ := hp.mp ht
    have hnb : rationalCentralCheck ν=false := Bool.eq_false_iff.mpr (fun h => hn ((rationalCentralCheck_true ν).mp h))
    have hmb : rationalCentralCheck μ=false := Bool.eq_false_iff.mpr (fun h => hm ((rationalCentralCheck_true μ).mp h))
    rw [matrixTail,Control.evaluate,ite_eq_left ht]
    simpa only [hnb,hmb,Bool.false_or,Bool.false_eq_true,ite_false,h0,h1,hrw] using yv
  · have hcentral : (rationalCentralCheck ν || rationalCentralCheck μ)=true := by
      by_contra hb
      have hboth : rationalCentralCheck ν=false ∧ rationalCentralCheck μ=false := by
        simpa only [Bool.or_eq_true,not_or,Bool.not_eq_true] using hb
      apply ht
      exact hp.mpr ⟨fun h => by have := (rationalCentralCheck_true ν).mpr h; simp [hboth.1] at this,
        fun h => by have := (rationalCentralCheck_true μ).mpr h; simp [hboth.2] at this⟩
    rw [matrixTail,Control.evaluate,ite_eq_right ht]
    simp only [Control.evaluate,Instruction.update,Function.update_self,Parts.literal_value,hcentral,ite_true]

#print axioms matrixControl_contract

end Maxwell.Continuum.Calibration.RawFree
