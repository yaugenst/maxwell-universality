import Maxwell.Continuum.CalibrationBufferCross
import Maxwell.Continuum.NatAssignOutputWidth

/-! The exact rational quadratic value is emitted as raw signed numerator
channels and an executed common denominator cube. -/

namespace Maxwell.Continuum.Calibration.PowerMachine.BufferCross

open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.CalibrationMatrix
open RationalDataflow
open RationalAccumulator (Word Blank)
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384

def denominatorIds : Finset ℕ := {126,576}
def denominatorPlan : List NatAssign.Instruction := [.copy 126 576,.multiply 126 576,.multiply 126 576]
def denominatorInput (D i : ℕ) : ℕ := if i=126 then D else 0
def quadraticCode : Code := .seq code (NatAssign.code denominatorPlan)
def quadraticCost (n B : ℕ) : ℕ := costBound n B+2^40*(B+2)^2
def quadraticParts {n : ℕ} (b : Buffers n) (D : ℕ) : Parts :=
  ⟨Pairing.positive (left b) (bufferChannels b),Pairing.negative (left b) (bufferChannels b),D^3⟩

theorem quadraticParts_value {n : ℕ} (b : Buffers n) (D : ℕ) :
    (quadraticParts b D).value=
      ∑ i, (((left b).value i:ℚ)/(D:ℚ))*(((bufferChannels b).value i:ℚ)/(D:ℚ)^2) := by
  have h := rational_value b (D:ℚ) ((D:ℚ)^2)
  simpa only [quadraticParts,Parts.value,Nat.cast_pow,show (D:ℚ)*(D:ℚ)^2=(D:ℚ)^3 by ring] using h

theorem quadratic_executes {n B : ℕ} (b : Buffers n) (D : ℕ) (count : List Bool)
    (hsize : b.Sized B) (hcount : addressValue count=n) (hcl : count.length≤B)
    (hD : D.bits.length≤B) (hDpos : 0<D)
    (input : List Bool) (tape : ℕ → Bool) (s : Store) (hb : b.Ready count B s.val)
    (hd : Word s.val 126 D) (h576 : Blank s.val 576) :
    ∃ cost t, Executes input tape quadraticCode cost s t ∧ cost≤quadraticCost n B ∧
      Word t.val 30 (quadraticParts b D).positive ∧ Word t.val 31 (quadraticParts b D).negative ∧
      Word t.val 576 (quadraticParts b D).denominator ∧
      (quadraticParts b D).Valid ∧ (quadraticParts b D).Width (NeumannMachine.StoredPairing.workWidth n B+3*B) ∧
      t.val.memory=s.val.memory := by
  obtain ⟨vi,hvi,hvl,cal,stored,indices,out,rest⟩ := hb
  have bound := represented_width b hsize stored out
  obtain ⟨c0,u,e0,hc0,wp,wm,cal0,_,_,f0⟩ := executes b count hsize hcount hcl
    input tape s ⟨vi,hvi,hvl,cal,stored,indices,out,rest⟩
  have hd0 : Word u.val 126 D := RationalAccumulator.word_of_eq
    (f0.2.2.2.2 126 (Or.inr (by decide)) (Or.inr (by decide))
      (by decide) (by decide) (by decide) (by decide) (by decide)) hd
  have blank0 : Blank u.val 576 := RationalAccumulator.blank_of_eq
    (f0.2.2.2.2 576 (Or.inr (by decide)) (Or.inr (by decide))
      (by decide) (by decide) (by decide) (by decide) (by decide)) h576
  have bank : NatAssign.Bank denominatorIds (denominatorInput D) u.val := by
    intro i hi
    simp only [denominatorIds,Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl|rfl
    · simpa [denominatorInput] using hd0
    · simpa [denominatorInput] using (RationalAccumulator.zero_word_iff_blank _ _).mpr blank0
  have widths : ∀ i∈denominatorIds, (denominatorInput D i).bits.length≤B := by
    intro i _
    unfold denominatorInput
    split_ifs
    · exact hD
    · simp
  have valid : ∀ a∈denominatorPlan, a.Valid denominatorIds := by
    simp [denominatorPlan,NatAssign.Instruction.Valid,denominatorIds]
  have ge (i : ℕ) (hi : i∈denominatorIds) : 4 ≤ i := by
    simp only [denominatorIds,Finset.mem_insert,Finset.mem_singleton] at hi
    omega
  have z0 : NatAssign.Scratch u.val := by
    intro i hi
    interval_cases i
    · exact cal0.2.1.1
    · exact cal0.2.1.2.1
    · exact cal0.2.1.2.2.1
    · exact cal0.2.1.2.2.2.1
  obtain ⟨c1,t,e1,hc1,b1,_,f1⟩ := NatAssign.executes denominatorIds ge denominatorPlan valid
    (denominatorInput D) input tape u bank z0
  have price := hc1.trans (NatAssign.price_bound denominatorIds denominatorPlan valid
    (denominatorInput D) B widths (by simp [denominatorPlan,NatAssign.Instruction.literalWidth]))
  have wd := b1 576 (by decide)
  have denominator : NatAssign.values denominatorPlan (denominatorInput D) 576=D^3 := by
    simp [denominatorPlan,denominatorInput,NatAssign.values,NatAssign.Instruction.update,
      NatAssign.Instruction.target,NatAssign.Instruction.value,pow_succ]
    ring
  rw [denominator] at wd
  have cubeBits : (D^3).bits.length≤3*B := by
    have h2 := RationalAccumulator.bits_mul_le D D
    have h3 := RationalAccumulator.bits_mul_le (D*D) D
    rw [show D^3=(D*D)*D by ring]
    omega
  refine ⟨c0+c1,t,e0.seq e1,?_,
    RationalAccumulator.word_of_eq (f1.tapes 30 (by decide)) wp,
    RationalAccumulator.word_of_eq (f1.tapes 31 (by decide)) wm,wd,
    by exact Nat.pow_pos hDpos,⟨?_,?_,?_⟩,f1.memory.trans f0.1⟩
  · unfold quadraticCost
    norm_num only [denominatorPlan,List.length_cons,List.length_nil] at price
    have hbound : c1≤2^40*(B+2)^2 := by nlinarith only [price]
    omega
  · exact bound.1.trans (Nat.le_add_right _ _)
  · exact bound.2.trans (Nat.le_add_right _ _)
  · exact cubeBits.trans (Nat.le_add_left _ _)

#print axioms quadraticParts_value
#print axioms quadratic_executes

end Maxwell.Continuum.Calibration.PowerMachine.BufferCross
