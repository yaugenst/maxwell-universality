import Maxwell.Continuum.ContinuumDecoderSelectorInitialize
import Maxwell.Continuum.StoredDescriptionSuffixInputs

/-! Charged selector installation produces the exact bank consumed by the
complete physical decoder serializer, including the retained source count. -/
noncomputable section
namespace Maxwell.Continuum.DecoderSelectors
open Maxwell.Cost Maxwell.Cost.Structured RationalAccumulator
open RealizationParameters WellStrengthInitialization
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384

theorem physical_selectors_executes {p : Source.Parameters} {S : Source.SparseSystem} {hm : 0<S.nnz}
    {v : ℕ→ℕ} (h : Inputs p S hm v) (dimension : v 500=S.n)
    (B H : ℕ) (hB : 10≤B) (width : ∀i∈inputs,(v i).bits.length≤B)
    (spectral : 0<v 2245) (tau : 0<v 2237)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank inputs v s.val) (scratch : NatAssign.Scratch s.val)
    (count : Word s.val 500 (v 500)) (old : WordCleanup.Bounded outputList H s.val) :
    ∃cost t,Executes input tape initializeCode cost s t ∧cost ≤ initializeCost B H ∧
      NatAssign.Bank suffixSelectorPorts (result (initial v)) t.val ∧NatAssign.Scratch t.val ∧
      result (initial v) 500=S.n ∧
      result (initial v) 4701=(gridReportFormat p S hm).integerBits ∧
      result (initial v) 4702=(gridReportFormat p S hm).fractionalBits ∧
      result (initial v) 4703=gridCount p S hm ∧
      result (initial v) 4705=gridSide p S hm 1 ∧result (initial v) 4706=gridSide p S hm 2 ∧
      (result (initial v) 4707:ℚ)/(result (initial v) 4708)=normalizationScale S ∧
      BinaryPrecision.Frame ({0,1,2,3}∪outputs) s.val t.val := by
  obtain ⟨c,t,e,hc,stored,blank,_,frame⟩:=initialize_executes v B H hB width
    (h.nonzeros.symm ▸ hm) spectral tau input tape s bank scratch old
  have count_eq : result (initial v) 500=v 500:=by
    rw [result_outside _ 500 (by decide)]
    exact ite_eq_right (by decide : 500∉outputs)
  refine ⟨c,t,e,hc,?_,blank,count_eq.trans dimension,h.initial.integerBits,h.initial.fractionalBits,
    h.initial.samples,h.initial.sides 1,h.initial.sides 2,h.initial.normalization,frame⟩
  intro i hi
  by_cases count_port:i=500
  · subst i
    rw [count_eq]
    exact word_of_eq (frame.tapes 500 (by decide)) count
  · apply stored i
    have members : suffixSelectorPorts⊆insert 500 ids := by decide +kernel
    exact (Finset.mem_insert.mp (members hi)).resolve_left count_port

#print axioms physical_selectors_executes
end Maxwell.Continuum.DecoderSelectors
