import Maxwell.Cost.Decoder
import Maxwell.Main

namespace Maxwell.Cost.Decoder

/-- The concrete uniform decoder inhabits the manuscript's public finite-code
contract on every target and every fixed-width message. -/
theorem decodes {n : ℕ} (I : Target.Instance n) :
    Realization.Decodes program (DecoderParser.decoderWidth I.decoder+2) I (costCap I+1) := by
  intro messages
  obtain ⟨stop,hstop,_,houtput,hrandom⟩ := run I messages (fun _ => false)
  exact ⟨stop,hstop,houtput,hrandom⟩

/-- Constant-size stencils and logarithmic stored coefficient/access widths
produce logarithmic raw-rational output widths, with the literal bound shown. -/
theorem decodes_bounded {n : ℕ} (I : Target.Instance n) (B K : ℕ)
    (hoffset : ∀ i, Source.ShortRational B (I.decoder.offset i))
    (hweight : ∀ i j, j ∈ I.decoder.support i → Source.ShortRational B (I.decoder.weight i j))
    (hsupport : ∀ i, (I.decoder.support i).card ≤ K) :
    Realization.Decodes program (2*B+K*(3*I.decoder.format.width+2*B+5)+2) I (costCap I+1) := by
  intro messages
  obtain ⟨stop,hstop,houtput,hrandom⟩ := decodes I messages
  obtain ⟨pairs,hbytes,hvalue,hshort⟩ := houtput
  refine ⟨stop,hstop,⟨pairs,hbytes,hvalue,?_⟩,hrandom⟩
  intro i
  have hb := DecoderParser.decoderWidth_bound I.decoder B K hoffset hweight hsupport
  exact ⟨(hshort i).1.trans (by omega),(hshort i).2.trans (by omega)⟩

end Maxwell.Cost.Decoder
