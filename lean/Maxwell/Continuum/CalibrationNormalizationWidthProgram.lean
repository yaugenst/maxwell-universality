import Maxwell.Continuum.CalibrationNormalizationWidths
import Maxwell.Continuum.StoredWordLength
import Maxwell.Continuum.NatAssignOutputWidth

/-! The output width is itself computed by a fixed runtime program from
the original dimension, power count, precision and buffer-width bound. -/

namespace Maxwell.Continuum.Calibration.PowerMachine.BufferNorm.Allocation

open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

def widthIds : Finset ℕ := {304,544,570,571,572,573,574,575}
def widthInputs (n K P B heap i : ℕ) : ℕ :=
  if i=304 then K else if i=544 then P else if i=570 then n
  else if i=572 then heap else if i=575 then B else 0
def widthScanned (n K P B heap : ℕ) : ℕ → ℕ :=
  Function.update (widthInputs n K P B heap) 574 P.bits.length
def widthPlan : List NatAssign.Instruction :=
  [.copy 304 571,.literal 573 1,.add 573 571,.multiply 575 571,
   .add 575 571,.add 575 571,.add 570 571,.add 574 571,.literal 573 6,.add 573 571,
   .literal 573 32,.multiply 573 571,.copy 544 573,.literal 574 32,.multiply 574 573,
   .add 573 571,.literal 573 64,.add 573 571,.literal 573 0]
def widthValues (n K P B heap : ℕ) : ℕ → ℕ := NatAssign.values widthPlan (widthScanned n K P B heap)
def widthCode : Code := .seq (WordLength.code 544 574) (NatAssign.code widthPlan)
def widthChanged : Finset ℕ := {0,1,2,3,571,573,574}

theorem widthIds_ge (i : ℕ) (hi : i∈widthIds) : 4 ≤ i := by
  simp only [widthIds,Finset.mem_insert,Finset.mem_singleton] at hi
  omega

theorem widthPlan_valid : ∀ a∈widthPlan, a.Valid widthIds := by
  simp [widthPlan,NatAssign.Instruction.Valid,widthIds]

theorem widthValues_width (n K P B heap : ℕ) : widthValues n K P B heap 571=outputWidth n K P B := by
  simp [widthValues,widthPlan,widthScanned,widthInputs,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.target,NatAssign.Instruction.value,outputWidth,normalizationWidth,
    NeumannMachine.StoredPairing.workWidth]
  ring

theorem widthValues_inputs (n K P B heap : ℕ) :
    widthValues n K P B heap 570=n ∧ widthValues n K P B heap 572=heap ∧
    widthValues n K P B heap 573=0 := by
  simp [widthValues,widthPlan,widthScanned,widthInputs,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.target,NatAssign.Instruction.value]

theorem width_executes (n K P B heap W : ℕ) (hW : 7≤W)
    (hv : ∀ i∈widthIds, (widthInputs n K P B heap i).bits.length≤W)
    (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (hb : NatAssign.Bank widthIds (widthInputs n K P B heap) s.val) (hz : NatAssign.Scratch s.val) :
    ∃ cost t, Executes input tape widthCode cost s t ∧ cost≤2^100*(W+2)^2 ∧
      NatAssign.Bank widthIds (widthValues n K P B heap) t.val ∧ NatAssign.Scratch t.val ∧
      BinaryPrecision.Frame widthChanged s.val t.val := by
  have hP : P.bits.length≤W := by simpa [widthInputs] using hv 544 (by decide)
  obtain ⟨c0,u,e0,hc0,b0,z0,f0⟩ := NatAssign.stored_length widthIds 544 574 (by decide)
    (by decide) (by decide) (by decide) (widthInputs n K P B heap) (by simp [widthInputs])
    input tape s hb hz
  change NatAssign.Bank widthIds (widthScanned n K P B heap) u.val at b0
  have small : P.bits.length.bits.length≤P.bits.length := by
    rw [Nat.size_eq_bits_len,Nat.size_le]
    exact Nat.lt_two_pow_self
  have scanned : ∀ i∈widthIds, (widthScanned n K P B heap i).bits.length≤W := by
    intro i hi
    by_cases he : i=574
    · subst i;simpa [widthScanned] using small.trans hP
    · simpa [widthScanned,he] using hv i hi
  obtain ⟨c1,t,e1,hc1,b1,z1,f1⟩ := NatAssign.executes widthIds widthIds_ge widthPlan widthPlan_valid
    (widthScanned n K P B heap) input tape u b0 z0
  have literals : ∀ a∈widthPlan, a.literalWidth≤W := by
    simp only [widthPlan,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,
      forall_eq,NatAssign.Instruction.literalWidth,
      show (0:ℕ).bits.length=0 from rfl,show (1:ℕ).bits.length=1 from rfl,
      show (6:ℕ).bits.length=3 from rfl,show (32:ℕ).bits.length=6 from rfl,
      show (64:ℕ).bits.length=7 from rfl]
    omega
  have price := hc1.trans (NatAssign.price_bound widthIds widthPlan widthPlan_valid
    (widthScanned n K P B heap) W scanned literals)
  refine ⟨c0+c1,t,e0.seq e1,?_,b1,z1,(f0.mono (by decide)).trans (f1.mono (by decide))⟩
  · change c0≤48*(P.bits.length+1)^2+1 at hc0
    have hpow : (P.bits.length+1)^2≤(W+2)^2 := Nat.pow_le_pow_left (by omega) 2
    have hsq : 1≤(W+2)^2 := by nlinarith only [Nat.zero_le W]
    norm_num only [widthPlan,List.length_cons,List.length_nil] at price
    nlinarith only [hc0,price,hpow,hsq]

#print axioms widthValues_width
#print axioms width_executes

end Maxwell.Continuum.Calibration.PowerMachine.BufferNorm.Allocation
