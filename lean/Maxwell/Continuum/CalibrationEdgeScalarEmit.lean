import Maxwell.Continuum.CalibrationEdgeScalarPrepare

namespace Maxwell.Continuum.Calibration.EdgeScalar
open Maxwell.Cost Maxwell.Cost.Structured RationalAccumulator RationalDataflow
set_option maxHeartbeats 2200000
set_option maxRecDepth 16384

def inputWidth (N B : ℕ) : ℕ := 3+Machin.finalWidth (N+7)+B

theorem output_range (i : ℕ) (hi : i∈outputPorts) : 1696≤ i ∧ i≤1710 := by
  simp only [outputPorts,ports,Finset.mem_biUnion,saved,Finset.mem_insert,Finset.mem_singleton] at hi
  obtain ⟨j,hj,cell⟩:=hi
  simp only [cellPorts,positivePort,negativePort,denominatorPort,Finset.mem_insert,Finset.mem_singleton] at cell
  omega

theorem emit_input_bank (N : ℕ) (p : Parts) (old : ℕ→Parts) (s : BitRAMState)
    (machin : NatAssign.Bank Machin.allIds (Machin.finalValues (N+7)) s)
    (previous : Cells saved old s) (midpoint : StoredParts.Stored (positivePort 2302) p s) :
    NatAssign.Bank emitIds (emitInput N p old) s := by
  intro i hi
  by_cases hm : i∈Machin.allIds
  · simpa only [emitInput,ite_eq_left hm] using machin i hm
  · simp only [emitInput,ite_eq_right hm]
    by_cases hp : i=7906
    · subst i;simpa only [ite_true,positivePort] using midpoint.1
    by_cases hn : i=7907
    · subst i;simpa only [ite_false,ite_true,positivePort,show (7907:ℕ)≠7906 from by decide] using midpoint.2.1
    by_cases hd : i=7908
    · subst i;simpa only [ite_false,ite_true,positivePort,show (7908:ℕ)≠7906 from by decide,
        show (7908:ℕ)≠7907 from by decide] using midpoint.2.2
    simp only [ite_eq_right hp,ite_eq_right hn,ite_eq_right hd]
    apply previous.bank
    rcases Finset.mem_union.mp hi with left|mid
    · exact (Finset.mem_union.mp left).resolve_left hm
    · simp only [midpointPorts,cellPorts,positivePort,negativePort,denominatorPort,
        Finset.mem_insert,Finset.mem_singleton] at mid
      omega

theorem emit_input_width (N B : ℕ) (p : Parts) (old : ℕ→Parts)
    (midWidth : p.Width B) (oldWidth : WidthBank saved B old) :
    ∀i∈emitIds,(emitInput N p old i).bits.length≤ inputWidth N B := by
  intro i hi
  by_cases hm : i∈Machin.allIds
  · simp only [emitInput,ite_eq_left hm]
    exact (Machin.finalValues_width _ i hm).trans (by unfold inputWidth;omega)
  · simp only [emitInput,ite_eq_right hm]
    by_cases hp : i=7906
    · simp only [ite_eq_left hp]
      exact midWidth.1.trans (by unfold inputWidth;omega)
    by_cases hn : i=7907
    · simp only [ite_eq_right hp,ite_eq_left hn]
      exact midWidth.2.1.trans (by unfold inputWidth;omega)
    by_cases hd : i=7908
    · simp only [ite_eq_right hp,ite_eq_right hn,ite_eq_left hd]
      exact midWidth.2.2.trans (by unfold inputWidth;omega)
    simp only [ite_eq_right hp,ite_eq_right hn,ite_eq_right hd]
    have output : i∈outputPorts := by
      rcases Finset.mem_union.mp hi with left|mid
      · exact (Finset.mem_union.mp left).resolve_left hm
      · simp only [midpointPorts,cellPorts,positivePort,negativePort,denominatorPort,
          Finset.mem_insert,Finset.mem_singleton] at mid
        omega
    exact (dataValues_width saved old B oldWidth i (Finset.mem_union_left _ output)).trans
      (by unfold inputWidth;omega)

theorem output_machine_disjoint : Disjoint outputPorts machineSet := by
  apply Finset.disjoint_left.mpr
  intro i hi hm
  have := output_range i hi
  have := (machine_member i).mp hm
  omega

#print axioms emit_input_bank
end Maxwell.Continuum.Calibration.EdgeScalar
