import Maxwell.Continuum.CalibrationRootGridSample

/-! The raw width of a newly computed summand depends only on its grid,
scale, phase and precision, not on the existing DFT accumulator. -/
namespace Maxwell.Continuum.RationalDataflow
open Maxwell.Cost
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

namespace RootProduct

theorem values_argument (N : ℕ) (v : ℕ→Parts) :
    values N v 3=RootSample.rawArgument (RootSample.coordinates v) := by
  simp only [values,multiply,Control.prepend,List.foldr_cons,List.foldr_nil,Control.evaluate,
    Instruction.update,Function.update_of_ne (by decide : (3:ℕ)≠6),
    Function.update_of_ne (by decide : (3:ℕ)≠7),afterSin,afterCos,RootSample.values,
    Function.update_of_ne (by decide : (3:ℕ)≠4),RootSample.argument_output]

theorem values_root (N : ℕ) (v : ℕ→Parts) : values N v 4=RootSample.values N v 4 := by
  simp only [values,multiply,Control.prepend,List.foldr_cons,List.foldr_nil,Control.evaluate,
    Instruction.update,Function.update_of_ne (by decide : (4:ℕ)≠6),
    Function.update_of_ne (by decide : (4:ℕ)≠7),afterSin,afterCos]

theorem values_active_width (N B : ℕ) (v : ℕ→Parts)
    (hv : ∀i,(RootSample.coordinates v i).Width B) (hp : (v 5).Width B)
    (i : ℕ) (hi : i<8) : (values N v i).Width (workWidth N B) := by
  by_cases h3 : i=3
  · subst i
    rw [values_argument]
    exact (RootSample.rawArgument_width _ B hv).mono (argumentWidth_le N B)
  by_cases h4 : i=4
  · subst i
    rw [values_root]
    exact (RootSample.values_width N B v hv).mono (root_width_le N B)
  by_cases h6 : i=6
  · subst i
    exact (values_coefficient_width N B v hv hp).1.mono (by unfold workWidth;omega)
  by_cases h7 : i=7
  · subst i
    exact (values_coefficient_width N B v hv hp).2.mono (by unfold workWidth;omega)
  rw [values_unchanged N v i ⟨h3,h4,h6,h7⟩]
  by_cases h5 : i=5
  · subst i
    exact hp.mono (workWidth_ge N B)
  have hsmall : i<3 := by omega
  exact (hv ⟨i,hsmall⟩).mono (workWidth_ge N B)

end RootProduct

namespace RootGrid

def coefficientInputWidth (B : ℕ) : ℕ := 2*(2^8*(B+1))+3
def coefficientBankWidth (N B : ℕ) : ℕ := RootProduct.workWidth N (coefficientInputWidth B)

theorem loaded_width (n : ℕ→ℕ) (v : ℕ→Parts) (B : ℕ)
    (hn : ∀i∈ids,(n i).bits.length≤B) (i : Fin 3) :
    (loadParts (values n) v i).Width (2^8*(B+1)) := by
  rw [loadParts_coordinate]
  have hh := values_width n B hn
  fin_cases i
  · exact part_width (values n) 333 _ (hh 333 (by decide)) (hh 331 (by decide))
  · exact part_width (values n) 334 _ (hh 334 (by decide)) (hh 331 (by decide))
  · exact part_width (values n) 335 _ (hh 335 (by decide)) (hh 331 (by decide))

theorem centered_width (n : ℕ→ℕ) (v : ℕ→Parts) (B : ℕ)
    (hn : ∀i∈ids,(n i).bits.length≤B) (hg : 0<n 331) (hv : (v 9).Width B)
    (i : Fin 3) : (RootGridCenter.values (loadParts (values n) v) i).Width (coefficientInputWidth B) := by
  rw [RootGridCenter.values_coordinates _ (loaded_coordinate_valid n v hg) i,
    loadParts_other _ _ 9 (by omega)]
  have hsmall : B≤2^8*(B+1) := by omega
  exact ((RootGridCenter.centeredPart_width _ _ (loaded_width n v B hn i)).mul
    (hv.mono hsmall)).mono (by unfold coefficientInputWidth;omega)

theorem centered_phase_width (n : ℕ→ℕ) (v : ℕ→Parts) (B : ℕ)
    (hn : ∀i∈ids,(n i).bits.length≤B) :
    (RootGridCenter.values (loadParts (values n) v) 5).Width (coefficientInputWidth B) := by
  rw [RootGridCenter.values_other _ 5 (by omega),loadParts_phase]
  have hh := values_width n B hn
  exact (part_width (values n) 341 _ (hh 341 (by decide)) (hh 331 (by decide))).mono
    (by unfold coefficientInputWidth;omega)

theorem sampleParts_width (S : Finset ℕ) (N B W : ℕ) (n : ℕ→ℕ) (v : ℕ→Parts)
    (hn : ∀i∈ids,(n i).bits.length≤B) (hg : 0<n 331) (hv : (v 9).Width B)
    (hw : WidthBank S W v) : WidthBank S (max W (coefficientBankWidth N B)) (sampleParts N n v) := by
  intro i hi
  by_cases hs : i<8
  · exact (RootProduct.values_active_width N (coefficientInputWidth B)
      (RootGridCenter.values (loadParts (values n) v)) (centered_width n v B hn hg hv)
      (centered_phase_width n v B hn) i hs).mono (Nat.le_max_right _ _)
  · rw [sampleParts_other N n v i (by omega)]
    exact (hw i hi).mono (Nat.le_max_left _ _)

#print axioms sampleParts_width
end RootGrid
end Maxwell.Continuum.RationalDataflow
