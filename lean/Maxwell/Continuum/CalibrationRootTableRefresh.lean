import Maxwell.Continuum.CalibrationRootTableEmission

/-! Returning a coefficient call to its actual uniform-width input state. -/
namespace Maxwell.Continuum.RationalDataflow.RootTable
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 3500000
set_option maxRecDepth 8192

def refreshCode : Code := .seq RootReset.control.code (NatAssign.code RootReset.naturalPlan)
def refreshCost (grid N B I : ℕ) : ℕ :=
  12*operationCost (4096*(entryWidth grid N B I+1))+1+
    stageCost (returnWidth grid (RootIndexed.decodedWidth B))

theorem Emitted.refresh_executes {T : ℕ} {a : PartArray.Table T} {target : Fin T}
    {grid N B I : ℕ} [NeZero grid] {scale : Parts}
    (hI : 1≤I) (hscale : scale.Width I)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (h : Emitted a target RootReset.bank grid N B I scale s) :
    ∃cost t,Executes input tape refreshCode cost s t ∧ cost≤refreshCost grid N B I ∧
      Context RootReset.bank N (RootReset.naturals grid) (RootReset.parts scale) t ∧
      (a.set target h.entry).OutputReady t ∧
      BinaryPrecision.Frame (RootGrid.coefficientWorkspace RootReset.bank) s.val t.val := by
  have hwpos : 1≤entryWidth grid N B I := by unfold entryWidth RootComponent.width;omega
  have hsc : (h.parts 9).Width I := by rw [h.scale_eq];exact hscale
  obtain ⟨c0,s0,e0,h0,r0,g0,w0,f0⟩ := RootReset.rational_executes h.parts (entryWidth grid N B I)
    I hwpos hI h.width h.good hsc input tape s h.context.rational
  have ctx0 := h.context.arithmetic_frame f0 r0
  have f0' : BinaryPrecision.Frame (RootGrid.coefficientWorkspace RootReset.bank) s.val s0.val :=
    f0.mono ((Finset.subset_union_right : workspace RootReset.bank⊆RootGrid.startWorkspace RootReset.bank).trans
    Finset.subset_union_left)
  have a0 := RootGrid.coefficient_outputReady (a.set target h.entry) h.output_table f0' r0
  obtain ⟨c1,t,e1,h1,b1,z1,f1⟩ := RootReset.natural_executes h.naturals
    (returnWidth grid (RootIndexed.decodedWidth B)) h.natural_width h.work_zero
    input tape s0 ctx0.natural ctx0.scratch
  have ctx1 := ctx0.natural_frame f1 b1 z1
  have finalContext : Context RootReset.bank N (RootReset.naturals grid) (RootReset.parts scale) t := by
    simpa only [h.grid_eq,h.scale_eq] using ctx1
  have f1' := f1.mono ((Finset.subset_union_left : RootFrequency.changed⊆RootFrequency.workspace RootReset.bank).trans
    (RootIndexed.workspace_subset RootReset.bank))
  exact ⟨c0+c1,t,e0.seq e1,by unfold refreshCost;omega,finalContext,
    RootFrequency.output_frame a0 f1 z1,f0'.trans f1'⟩

#print axioms Emitted.refresh_executes
end Maxwell.Continuum.RationalDataflow.RootTable
