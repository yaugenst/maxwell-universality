import Maxwell.Continuum.StoredAmbientRelocated
import Maxwell.Continuum.ContinuumDecoderSelectorData

/-! The ambient iterator emits exactly the source-selected physical box,
using the same retained outer words as decoder selector generation. -/
noncomputable section
namespace Maxwell.Continuum.StoredAmbient
open Maxwell.Cost Maxwell.Cost.Structured RealizationParameters
set_option maxHeartbeats 1000000
set_option maxRecDepth 16384
attribute [local irreducible] Parameters.sourceInput Parameters.sourceMagnitude MasterConstants.exponent

theorem side_physical {p : Source.Parameters} {S : Source.SparseSystem} {hm : 0<S.nnz}
    {v : ℕ→ℕ} (h : DecoderSelectors.Inputs p S hm v) (j : Fin 3) :
    side v j=Parameters.sourcePhysicalLengths p S hm j := by
  unfold side
  rw [h.span,h.length_eq,h.buffer_eq]
  rfl

theorem physical_executes {p : Source.Parameters} {S : Source.SparseSystem} {hm : 0<S.nnz}
    {v : ℕ→ℕ} (h : DecoderSelectors.Inputs p S hm v)
    (B H : ℕ) (hB : 3≤B) (width : ∀i∈inputs,(v i).bits.length≤B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank inputs v s.val) (scratch : NatAssign.Scratch s.val)
    (old : WordCleanup.Bounded relocatedOld H s.val) :
    ∃steps t,Executes input tape relocatedCode steps s t ∧steps≤relocatedCost v B H ∧
      t.val.output=(ambientBits p S hm).reverse++s.val.output ∧NatAssign.Scratch t.val ∧
      GeometryOutput.OutputFrame relocatedWork s.val t.val := by
  obtain ⟨c,t,e,hc,out,z,f⟩:=relocated_executes v B H hB width input tape s bank scratch old
  refine ⟨c,t,e,hc,?_,z,f⟩
  simpa only [side_physical h,ambientBits] using out

#print axioms physical_executes
end Maxwell.Continuum.StoredAmbient
