import Maxwell.Cost.CalibrationMatrix.GeneratedCoordinates
import Maxwell.Cost.CalibrationMatrix.MaterialEntry

namespace Maxwell.Cost.CalibrationMatrix.GeneratedCoordinates
open Structured BankArray WordSchedule
open RationalAccumulator (Blank)

/-- Convert the decoded operands and genuinely empty comparison banks into
the finite raw-word bank contract of the comparison preparation program. -/
theorem initial_banks (clockWord : List Bool) (raw : Fin 7 → List Bool)
    (direction : List Bool) (s : Store) (hclock : Word s.val 101 clockWord)
    (hoperands : Operands s.val raw direction)
    (hblank : ∀ i ∈ TestInputs.domain, i ≠ 101 → i ∉ rawBanks → Blank s.val i) :
    Banks TestInputs.domain s (TestInputs.initial clockWord raw) := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,_⟩ := hoperands
  intro i hi
  by_cases h101 : i = 101
  · subst i; simpa [TestInputs.initial] using hclock
  by_cases h150 : i = 150
  · subst i; simpa [TestInputs.initial] using h0
  by_cases h151 : i = 151
  · subst i; simpa [TestInputs.initial] using h1
  by_cases h152 : i = 152
  · subst i; simpa [TestInputs.initial] using h2
  by_cases h153 : i = 153
  · subst i; simpa [TestInputs.initial] using h3
  by_cases h171 : i = 171
  · subst i; simpa [TestInputs.initial] using h4
  by_cases h172 : i = 172
  · subst i; simpa [TestInputs.initial] using h5
  by_cases h173 : i = 173
  · subst i; simpa [TestInputs.initial] using h6
  have h170 : i ≠ 170 := by
    have h : ∀ j ∈ TestInputs.domain, j ≠ 170 := by decide
    exact h i hi
  have hb := hblank i hi h101 (by simp [rawBanks,h150,h151,h152,h153,h170,h171,h172,h173])
  simpa [TestInputs.initial,h101,h150,h151,h152,h153,h171,h172,h173,Word,Blank] using hb

end Maxwell.Cost.CalibrationMatrix.GeneratedCoordinates

namespace Maxwell.Cost.CalibrationMatrix.MaterialEntry
open Maxwell.Defect.FiniteStencil Maxwell.Spectral.Lattice

/-- The fixed table bounds the actual emitted canonical channel lengths. -/
theorem channel_lengths (material : Cell20 → ℚ) (z : ℚ) (D : ℕ) (key : StencilKey) :
    (entryChannels material z D key).1.bits.length+(entryChannels material z D key).2.bits.length ≤
      MaterialTable.outputBits 34 (table material z D) := by
  have h := MaterialTable.outputBits_bound (TableKey.encode key) (table material z D)
  simpa only [TableKey.encode_length,table,TableKey.decode_encode,Nat.size_eq_bits_len] using h

end Maxwell.Cost.CalibrationMatrix.MaterialEntry
