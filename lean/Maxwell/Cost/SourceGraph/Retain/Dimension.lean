import Maxwell.Cost.PositiveGraph.Metadata.Dimension

namespace Maxwell.Cost.SourceGraph.Retain
open Structured
open RationalAccumulator (Word Blank)

def dimensionCode : Code := .seq (.call (WordTransfer.clone 95 503))
  (.call (NormalizeWord.program 503))

theorem dimension (input : List Bool) (tape : ℕ → Bool) (width d : ℕ)
    (hd : d < 2^width) (s : Store)
    (h95 : BankArray.Word s.val 95 (SourceCircuit.fixedWidth width d)) (h503 : Blank s.val 503) :
    ∃ cost t, Executes input tape dimensionCode cost s t ∧ cost ≤ 31*width+35 ∧
      Word t.val 503 d ∧ BinaryPrecision.Frame {503} s.val t.val := by
  obtain ⟨source,hs⟩ := h95
  obtain ⟨dest,ht⟩ := h503
  obtain ⟨a,ea,atapes,af⟩ := WordCall.clone 95 503 (by decide) input tape
    (SourceCircuit.fixedWidth width d) source dest s hs ht
  obtain ⟨cost,u,hcost,hu,hpc,hw,_,uf⟩ := NormalizeWord.simulation 503 dest input tape
    (SourceCircuit.fixedWidth width d) a.val a.property (by simp [atapes])
  let t := Store.ofState u
  have et : Executes input tape (.call (NormalizeWord.program 503)) (cost+1) a t :=
    .call _ _ _ _ hu (by rw [hpc]; rfl)
  have fa : BinaryPrecision.Frame {503} s.val a.val :=
    ⟨af.1,af.2.1,af.2.2.1,af.2.2.2.1,af.2.2.2.2.1,by
      intro i hi
      have hne : i ≠ 503 := by simpa using hi
      simp [atapes,hne]⟩
  have ft : BinaryPrecision.Frame {503} a.val t.val :=
    ⟨uf.1,uf.2.1,uf.2.2.1,uf.2.2.2.1,uf.2.2.2.2.1,by
      intro i hi
      exact uf.2.2.2.2.2.1 i (by simpa using hi)⟩
  refine ⟨_,t,ea.seq et,?_,⟨dest,?_⟩,fa.trans ft⟩
  · simpa only [SourceCircuit.fixedWidth_length] using (show
        15*(SourceCircuit.fixedWidth width d).length+17+(cost+1) ≤
          31*(SourceCircuit.fixedWidth width d).length+35 by omega)
  · simpa only [t,Store.ofState,SourceCircuit.fixedWidth_value width d hd] using hw

end Maxwell.Cost.SourceGraph.Retain
