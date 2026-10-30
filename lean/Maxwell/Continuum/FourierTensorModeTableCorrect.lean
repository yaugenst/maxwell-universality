import Maxwell.Continuum.FourierTensorModeTableData

/-! The generated table satisfies the existing tensor compiler's literal
FourierRows contract. Its slot-width requirements follow from the actual
normalized mode bound, independently of raw calibration denominators. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime.ModePrepare
open Maxwell.Cost RationalDataflow PartArray Calibration
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

theorem fields_width (M A P R W Z : ℕ) [NeZero M]
    (a : Table (2*aliasArraySize R)) (j : Fin 3) (r : Fin (RowArithmetic.rowCount R)) (v : ℕ→Parts)
    (hnorm : (v 0).value=Supercell.physicalFactorApprox M A)
    (hmode : ‖(GlobalPower.tableData R a).value‖≤2) (hscale : (v 1).Width W)
    (hfrequency : W+R.bits.length+3≤Z) (hamplitude : P+6≤Z) (k : Fin 5) :
    (fields P R a j r v k).Width Z := by
  have frequency (i : Fin 3) := (RowArithmetic.output_frequency_width P R W a j r v hscale i).mono hfrequency
  have amplitude := ModeDecode.output_row_amplitude_width M A P R a j r v hnorm hmode
  fin_cases k
  · exact (fields_frequency P R a j r v 0) ▸ frequency 0
  · exact (fields_frequency P R a j r v 1) ▸ frequency 1
  · exact (fields_frequency P R a j r v 2) ▸ frequency 2
  · exact amplitude.1.mono hamplitude
  · exact amplitude.2.mono hamplitude

theorem entries_width (P R Z : ℕ) (a : Table (2*aliasArraySize R)) (j : Fin 3) (v : ℕ→Parts)
    (hfit : ∀r k,(fields P R a j r v k).Width Z) (i : Fin (5*RowArithmetic.rowCount R)) :
    (entries P R a j v i).Width Z := hfit _ _

theorem writePlan_fit (P R Z : ℕ) (a : Table (2*aliasArraySize R)) (j : Fin 3)
    (r : Fin (RowArithmetic.rowCount R)) (v : ℕ→Parts)
    (hfit : ∀k,(fields P R a j r v k).Width Z) :
    ∀x∈writePlan,(values P R a j r v x.2).Width Z := by
  intro x hx
  simp only [writePlan,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl|rfl|rfl|rfl|rfl
  · exact hfit 4
  · exact hfit 3
  · exact hfit 2
  · exact hfit 1
  · exact hfit 0

theorem generated_fourierRows (M A P R : ℕ) (L : ℚ)
    (a : Table (2*aliasArraySize R)) (b : Table (5*RowArithmetic.rowCount R)) (j : Fin 3)
    (v : ℕ→Parts) (hnorm : (v 0).value=Supercell.physicalFactorApprox M A)
    (hscale : (v 1).value=L/(2*M)) (hv : Good RowArithmetic.bank v)
    (hav : ∀i,(a.get i).Valid)
    (hfit : ∀r k,(fields P R a j r v k).Width (addressValue b.width)) :
    FourierRows (b.filled (entries P R a j v) 0)
      (fun r => Supercell.templateFrequency M L (RowArithmetic.rowAlias R r))
      (fun r => roundFourierCoefficient P (Supercell.physicalCoefficientData M A (GlobalPower.tableData R a))
        (RowArithmetic.rowAlias R r) j) := by
  have fit := entries_width P R (addressValue b.width) a j v hfit
  intro r
  have hg := RowArithmetic.output_good P (RowArithmetic.loaded R a j r v)
    (RowArithmetic.loaded_good R a j r v hv hav)
  have amps := RowArithmetic.output_mode_amplitudes M A P R a j r v hnorm
  refine ⟨?_,?_,?_⟩
  · intro k
    rw [Table.filled_get b _ fit,entries_row P R a j r v ⟨k.val,by omega⟩,
      fields_frequency P R a j r v k]
    exact ⟨RowArithmetic.output_mode_frequency M P R L a j r v hscale k,
      hg (4+k.val) (Finset.mem_range.mpr (by omega))⟩
  · rw [Table.filled_get b _ fit,entries_row P R a j r v ⟨3,by decide⟩]
    change values P R a j r v 9=_
    rw [values,ModeDecode.output_row P R a j r v 9 (by decide)]
    exact amps.1
  · rw [Table.filled_get b _ fit,entries_row P R a j r v ⟨4,by decide⟩]
    change values P R a j r v 10=_
    rw [values,ModeDecode.output_row P R a j r v 10 (by decide)]
    exact amps.2

#print axioms fields_width
#print axioms generated_fourierRows
end Maxwell.Continuum.Profile.WaveMachine.Runtime.ModePrepare
