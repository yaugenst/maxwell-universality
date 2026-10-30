import Maxwell.Continuum.ChebyshevWaveMachineSumCorrect
import Maxwell.Continuum.ChebyshevWaveProductSmallWidths

/-! The actual Fourier accumulator grows additively in the number of samples.
The exact integer counter has logarithmic width and never inherits the sum width. -/
namespace Maxwell.Continuum.Profile.WaveMachine
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow RationalTaylor
set_option maxHeartbeats 3500000
set_option maxRecDepth 8192

theorem sumStep_unchanged_high (Q P : ℕ) (v : ℕ→Parts) (i : ℕ) (hi : 10 ≤ i) (hne : i≠13) :
    sumStep Q P v i=v i := by
  simp only [sumStep,accumulateInstructions,evaluate,RationalDataflow.Instruction.update,
    Function.update_of_ne (by omega : i≠8),Function.update_of_ne (by omega : i≠9),
    Function.update_of_ne hne]
  exact summand_unchanged Q P v i (by omega)

theorem sumValues_unchanged_high (Q P : ℕ) (v : ℕ→Parts) (i : ℕ) (hi : 10 ≤ i) (hne : i≠13) (k : ℕ) :
    sumValues Q P v k i=v i := by
  induction k with
  | zero => rfl
  | succ k ih => exact (sumStep_unchanged_high Q P _ i hi hne).trans ih

theorem sumStep_counter (Q P k : ℕ) (v : ℕ→Parts)
    (hcount : v 13=⟨k,0,1⟩) (hone : v 15=⟨1,0,1⟩) : sumStep Q P v 13=⟨k+1,0,1⟩ := by
  simp only [sumStep,accumulateInstructions,evaluate,RationalDataflow.Instruction.update,BinaryOp.eval,
    Function.update_self,Function.update_of_ne (by decide : (13:ℕ)≠9),
    Function.update_of_ne (by decide : (13:ℕ)≠8),Function.update_of_ne (by decide : (15:ℕ)≠9),
    Function.update_of_ne (by decide : (15:ℕ)≠8)]
  rw [summand_unchanged Q P v 13 (by decide),summand_unchanged Q P v 15 (by decide),hcount,hone]
  simp [Parts.add]

theorem sumValues_counter (Q P : ℕ) (v : ℕ→Parts)
    (hcount : v 13=⟨0,0,1⟩) (hone : v 15=⟨1,0,1⟩) (k : ℕ) :
    sumValues Q P v k 13=⟨k,0,1⟩ := by
  induction k with
  | zero => exact hcount
  | succ k ih =>
    exact sumStep_counter Q P k _ ih ((sumValues_unchanged_high Q P v 15 (by decide) (by decide) k).trans hone)

theorem sumValues_metadata_width (Q P grid W : ℕ) (v : ℕ→Parts) (hw : WidthBank ids W v)
    (hW : 1≤W) (hgrid : grid.bits.length≤W) (hcount : v 13=⟨0,0,1⟩) (hone : v 15=⟨1,0,1⟩)
    (k : ℕ) (hk : k≤grid) (i : ℕ) (hi : 10 ≤ i) (hi' : i<16) :
    (sumValues Q P v k i).Width W := by
  by_cases he : i=13
  · subst i
    rw [sumValues_counter Q P v hcount hone k]
    exact ⟨(RationalWords.bits_mono hk).trans hgrid,by simp,by simpa only [show (1:ℕ).bits.length=1 by decide] using hW⟩
  · rw [sumValues_unchanged_high Q P v i hi he k]
    exact hw i (Finset.mem_range.mpr hi')

theorem prepared_operands_width (W : ℕ) (v : ℕ→Parts)
    (hm : ∀i,10 ≤ i → i<16 → (v i).Width W) :
    (prepared v 0).Width (5*(W+1)) ∧ (prepared v 1).Width (5*(W+1)) ∧
    (prepared v 5).Width (5*(W+1)) := by
  have h0 := (hm 10 (by decide) (by decide)).mul (hm 15 (by decide) (by decide))
  have h1 := (hm 13 (by decide) (by decide)).mul (hm 11 (by decide) (by decide))
  have h5 := (h1.mul (hm 12 (by decide) (by decide))).mul (hm 14 (by decide) (by decide))
  refine ⟨?_,?_,?_⟩
  · simpa [prepared,prepareInstructions,evaluate,RationalDataflow.Instruction.update,BinaryOp.eval]
      using h0.mono (show W+W+1≤5*(W+1) by omega)
  · simpa [prepared,prepareInstructions,evaluate,RationalDataflow.Instruction.update,BinaryOp.eval]
      using h1.mono (show W+W+1≤5*(W+1) by omega)
  · simpa [prepared,prepareInstructions,evaluate,RationalDataflow.Instruction.update,BinaryOp.eval]
      using h5.mono (show ((W+W+1)+W+1)+W+1≤5*(W+1) by omega)

theorem sumStep_low (Q P : ℕ) (v : ℕ→Parts) (i : ℕ) (hi : i<8) :
    sumStep Q P v i=summand Q P v i := by
  simp only [sumStep,accumulateInstructions,evaluate,RationalDataflow.Instruction.update,
    Function.update_of_ne (by omega : i≠8),Function.update_of_ne (by omega : i≠9),
    Function.update_of_ne (by omega : i≠13)]

theorem sumStep_accumulators (Q P : ℕ) (v : ℕ→Parts) :
    sumStep Q P v 8=(v 8).add (summand Q P v 0) ∧
    sumStep Q P v 9=(v 9).add (summand Q P v 1) := by
  simp only [sumStep,accumulateInstructions,evaluate,RationalDataflow.Instruction.update,BinaryOp.eval,
    Function.update_self,Function.update_of_ne (by decide : (8:ℕ)≠13),
    Function.update_of_ne (by decide : (8:ℕ)≠9),Function.update_of_ne (by decide : (9:ℕ)≠13),
    Function.update_of_ne (by decide : (9:ℕ)≠8),Function.update_of_ne (by decide : (1:ℕ)≠8)]
  rw [summand_unchanged Q P v 8 (by decide),summand_unchanged Q P v 9 (by decide)]
  exact ⟨rfl,rfl⟩

def sumBankWidth (Q P W k : ℕ) : ℕ := W+(k+1)*(productWorkWidth Q P (5*(W+1))+1)

theorem sumValues_width (Q P grid W : ℕ) (v : ℕ→Parts) (hw : WidthBank ids W v)
    (hW : 1≤W) (hgrid : grid.bits.length≤W) (hcount : v 13=⟨0,0,1⟩) (hone : v 15=⟨1,0,1⟩)
    (k : ℕ) (hk : k≤grid) : WidthBank ids (sumBankWidth Q P W k) (sumValues Q P v k) := by
  induction k with
  | zero => exact hw.mono (by unfold sumBankWidth;omega)
  | succ k ih =>
    have hk' : k≤grid := by omega
    have old := ih hk'
    have hm := sumValues_metadata_width Q P grid W v hw hW hgrid hcount hone k hk'
    have hp := prepared_operands_width W _ hm
    have hsmall := product_small_width Q P (5*(W+1)) (prepared (sumValues Q P v k)) hp.1 hp.2.1 hp.2.2
    change WidthBank (Finset.range 8) (productWorkWidth Q P (5*(W+1)))
      (summand Q P (sumValues Q P v k)) at hsmall
    have hnext : sumBankWidth Q P W k+productWorkWidth Q P (5*(W+1))+1=sumBankWidth Q P W (k+1) := by
      unfold sumBankWidth
      ring
    have hlow : productWorkWidth Q P (5*(W+1))≤sumBankWidth Q P W (k+1) := by
      have hpos : 1≤k+1+1 := by omega
      have h := Nat.mul_le_mul_right (productWorkWidth Q P (5*(W+1))+1) hpos
      unfold sumBankWidth
      omega
    intro i hi
    have hi' : i<16 := Finset.mem_range.mp hi
    change (sumStep Q P (sumValues Q P v k) i).Width _
    by_cases h8 : i<8
    · rw [sumStep_low Q P _ i h8]
      exact (hsmall i (Finset.mem_range.mpr h8)).mono hlow
    by_cases he8 : i=8
    · subst i
      rw [(sumStep_accumulators Q P _).1]
      exact hnext ▸ (old 8 (by decide)).add (hsmall 0 (by decide))
    by_cases he9 : i=9
    · subst i
      rw [(sumStep_accumulators Q P _).2]
      exact hnext ▸ (old 9 (by decide)).add (hsmall 1 (by decide))
    have hmeta := sumValues_metadata_width Q P grid W v hw hW hgrid hcount hone (k+1) hk i (by omega) hi'
    exact hmeta.mono (by unfold sumBankWidth;omega)

#print axioms sumValues_counter
#print axioms sumValues_width
end Maxwell.Continuum.Profile.WaveMachine
