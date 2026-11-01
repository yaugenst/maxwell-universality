import Maxwell.Continuum.CalibrationEdgeScalarRelocation

/-! The produced scalar width depends on precision and midpoint width. Old
scalar words affect the charged overwrite cost, but do not enlarge the result. -/
namespace Maxwell.Continuum.Calibration.EdgeScalar
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384

theorem result_width (N B : ℕ) (p : Parts) (positive : 1≤B) (width : p.Width B) :
    WidthBank saved (resultWidth N B) (result N p) := by
  let old : ℕ→Parts:=fun _=>Parts.literal 0
  have previous : WidthBank saved B old :=
    fun _ _=>(Parts.literal_width RationalWords.width_zero').mono positive
  have words:=NatAssign.values_width emitIds emitPlan emit_valid (emitInput N p old)
    (inputWidth N B) (emit_input_width N B p old width previous)
    (fun a ha=>(emit_literals a ha).trans (by unfold inputWidth;omega))
  have member (i : ℕ) (hi : i∈saved) (k : ℕ) (hk : k∈cellPorts i) : k∈emitIds :=
    Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i,hi,hk⟩))
  intro i hi
  have meaning:=emit_result N p old i hi
  exact ⟨meaning.1 ▸ Nat.le_of_succ_le (words _ (member i hi _ (by simp [cellPorts]))),
    meaning.2.1 ▸ Nat.le_of_succ_le (words _ (member i hi _ (by simp [cellPorts]))),
    meaning.2.2 ▸ Nat.le_of_succ_le (words _ (member i hi _ (by simp [cellPorts])))⟩

#print axioms result_width
end Maxwell.Continuum.Calibration.EdgeScalar
