import Maxwell.Continuum.RationalDataflowArrayOutput
import Maxwell.Continuum.RationalDataflowArrayCost

/-! Raw-array metadata is invariant under entry updates. These statements use
only the table representation, independently of calibration execution. -/
namespace Maxwell.Continuum.Calibration.ArrayDecodeMachine
open RationalDataflow

def sameMetadata {T : ℕ} (a b : PartArray.Table T) : Prop :=
  b.width=a.width ∧ b.basePositive=a.basePositive ∧ b.baseNegative=a.baseNegative ∧
    b.baseDenominator=a.baseDenominator ∧ b.clock=a.clock

theorem sameMetadata_refl {T : ℕ} (a : PartArray.Table T) : sameMetadata a a :=
  ⟨rfl,rfl,rfl,rfl,rfl⟩
theorem sameMetadata_set {T : ℕ} (a b : PartArray.Table T) (i : Fin T) (x : Parts)
    (h : sameMetadata a b) : sameMetadata a (b.set i x) := h
theorem sameMetadata_width {T : ℕ} (a b : PartArray.Table T) (h : sameMetadata a b)
    (W : ℕ) (ha : a.MetadataWidth W) : b.MetadataWidth W :=
  ⟨by simpa only [h.1] using ha.width,by simpa only [h.2.1] using ha.basePositive,
    by simpa only [h.2.2.1] using ha.baseNegative,by simpa only [h.2.2.2.1] using ha.baseDenominator,
    by simpa only [h.2.2.2.2] using ha.clock⟩
theorem sameMetadata_separated {T : ℕ} (a b : PartArray.Table T) (h : sameMetadata a b)
    (ha : a.Separated) : b.Separated := by
  simpa only [PartArray.Table.Separated,h.1,h.2.1,h.2.2.1,h.2.2.2.1] using ha

end Maxwell.Continuum.Calibration.ArrayDecodeMachine
