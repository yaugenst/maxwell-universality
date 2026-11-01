import Maxwell.Continuum.RationalDataflowRowPlan
import Maxwell.Continuum.RationalDataflowNaturalChannels
import Maxwell.Cost.BankArray.Unique

/-! Bounds obtained from the actual canonical natural words of rational
registers and array descriptors. These are independent of the producer. -/
namespace Maxwell.Continuum.RationalDataflow
open Maxwell.Cost Maxwell.Cost.Structured

theorem raw_width_of_bank (S ids : Finset ℕ) (n : ℕ→ℕ) (v : ℕ→Parts) (W : ℕ)
    (included : ports S⊆ids) (width : ∀i∈ids,(n i).bits.length≤W) (s : Store)
    (bank : NatAssign.Bank ids n s.val) (ready : Ready S v s) : WidthBank S W v := by
  intro i hi
  have get (channel : NaturalChannel.Channel) :
      (dataValues v (NaturalChannel.port channel i)).bits.length≤W := by
    have cell : NaturalChannel.port channel i∈cellPorts i := by
      cases channel <;> simp [NaturalChannel.port,cellPorts]
    have member := included (Finset.mem_biUnion.mpr ⟨i,hi,cell⟩)
    have eq:=BankArray.word_unique (ready.1 _ (cell_mem hi cell)) (bank _ member)
    rw [eq]
    exact width _ member
  exact ⟨by simpa only [NaturalChannel.port,dataValues_positive] using get .positive,
    by simpa only [NaturalChannel.port,dataValues_negative] using get .negative,
    by simpa only [NaturalChannel.port,dataValues_denominator] using get .denominator⟩

namespace PartArray
theorem Table.words_of_bank {T : ℕ} (a : Table T) (ids : Finset ℕ) (n : ℕ→ℕ)
    (included : ({200,202,203,204}:Finset ℕ)⊆ids) (s : Store)
    (bank : NatAssign.Bank ids n s.val) (ready : a.Ready s) :
    a.width=(n 200).bits ∧ a.basePositive=(n 202).bits ∧
    a.baseNegative=(n 203).bits ∧ a.baseDenominator=(n 204).bits :=
  ⟨BankArray.word_unique ready.width (bank 200 (included (by decide))),
    BankArray.word_unique ready.basePositive (bank 202 (included (by decide))),
    BankArray.word_unique ready.baseNegative (bank 203 (included (by decide))),
    BankArray.word_unique ready.baseDenominator (bank 204 (included (by decide)))⟩

theorem Table.metadata_of_bank {T : ℕ} (a : Table T) (ids : Finset ℕ) (n : ℕ→ℕ) (W : ℕ)
    (included : ({200,202,203,204}:Finset ℕ)⊆ids) (width : ∀i∈ids,(n i).bits.length≤W)
    (clock : n 200≤W) (s : Store) (bank : NatAssign.Bank ids n s.val) (ready : a.Ready s) :
    a.MetadataWidth W := by
  obtain ⟨w,p,q,d⟩:=a.words_of_bank ids n included s bank ready
  exact ⟨by rw [w];exact width 200 (included (by decide)),
    by rw [p];exact width 202 (included (by decide)),
    by rw [q];exact width 203 (included (by decide)),
    by rw [d];exact width 204 (included (by decide)),
    by rw [a.clock_length,w,addressValue_bits];exact clock⟩
end PartArray
#print axioms raw_width_of_bank
#print axioms PartArray.Table.metadata_of_bank
end Maxwell.Continuum.RationalDataflow
