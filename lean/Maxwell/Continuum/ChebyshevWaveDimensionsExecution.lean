import Maxwell.Continuum.ChebyshevWaveDimensions
import Maxwell.Continuum.NatAssignOutputWidth

/-! Charged execution of the wave dimensions from represented runtime words. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 3500000
set_option maxRecDepth 8192

def degreeWidth (W : ℕ) : ℕ := 2^8*(W+1)
def dimensionWidth (W : ℕ) : ℕ := 2^28*(W+2)

theorem initialDimensions_width (Q N W : ℕ) (hQ : Q.bits.length≤W) (hN : N.bits.length≤W)
    (i : ℕ) : (initialDimensions Q N i).bits.length≤W := by
  unfold initialDimensions
  split_ifs <;> first | exact hQ | exact hN | simp

theorem degreeValues_width (Q N W : ℕ) (hQ : Q.bits.length≤W) (hN : N.bits.length≤W)
    (hW : 6≤W) (i : ℕ) (hi : i∈dimensionIds) :
    (degreeValues Q N i).bits.length≤degreeWidth W := by
  have hw := NatAssign.values_width_bound dimensionIds degreeSetup degreeSetup_valid (initialDimensions Q N) W
    (fun i _ => initialDimensions_width Q N W hQ hN i) (by
      simp [degreeSetup,NatAssign.Instruction.literalWidth,
        show (8:ℕ).bits.length=4 from rfl,show (16:ℕ).bits.length=5 from rfl]
      omega) i hi
  exact (Nat.le_succ _).trans hw

theorem scannedValues_width (Q N W : ℕ) (hQ : Q.bits.length≤W) (hN : N.bits.length≤W)
    (hW : 6≤W) (i : ℕ) (hi : i∈dimensionIds) :
    (scannedValues Q N i).bits.length≤degreeWidth W := by
  by_cases he : i=713
  · subst i
    simp only [scannedValues,Function.update_self]
    have hn : (waveDegree (8*Q) N).bits.length.bits.length≤(waveDegree (8*Q) N).bits.length := by
      rw [Nat.size_eq_bits_len,Nat.size_le]
      exact Nat.lt_two_pow_self
    have hd := degreeValues_width Q N W hQ hN hW 712 (by decide)
    rw [degreeValues_eq,ite_eq_left rfl] at hd
    exact hn.trans hd
  · simpa only [scannedValues,Function.update_of_ne he] using degreeValues_width Q N W hQ hN hW i hi

theorem gridSetup_literalWidth (W : ℕ) (hW : 6≤W) :
    ∀a∈gridSetup,a.literalWidth≤degreeWidth W := by
  have hw : 6≤degreeWidth W := by unfold degreeWidth;omega
  simp [gridSetup,NatAssign.Instruction.literalWidth,
    show (8:ℕ).bits.length=4 from rfl,show (16:ℕ).bits.length=5 from rfl,
    show (32:ℕ).bits.length=6 from rfl]
  omega

theorem finalDimensions_width (Q N W : ℕ) (hQ : Q.bits.length≤W) (hN : N.bits.length≤W)
    (hW : 6≤W) (i : ℕ) (hi : i∈dimensionIds) :
    (finalDimensions Q N i).bits.length≤dimensionWidth W := by
  have hw := NatAssign.values_width_bound dimensionIds gridSetup gridSetup_valid (scannedValues Q N)
    (degreeWidth W) (scannedValues_width Q N W hQ hN hW) (gridSetup_literalWidth W hW) i hi
  apply ((Nat.le_succ _).trans hw).trans
  change 2^17*(degreeWidth W+1)≤dimensionWidth W
  unfold degreeWidth dimensionWidth
  omega

theorem dimensions_executes (Q N W : ℕ) (hQ : Q.bits.length≤W) (hN : N.bits.length≤W)
    (hW : 6≤W) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : NatAssign.Bank dimensionIds (initialDimensions Q N) s.val) (hz : NatAssign.Scratch s.val) :
    ∃cost t,Executes input tape dimensionCode cost s t ∧ cost≤2^120*(W+2)^2 ∧
      NatAssign.Bank dimensionIds (finalDimensions Q N) t.val ∧ NatAssign.Scratch t.val ∧
      BinaryPrecision.Frame dimensionWorkspace s.val t.val ∧
      Word t.val 710 Q ∧ Word t.val 711 N ∧ Word t.val 712 (waveDegree (8*Q) N) ∧
      Word t.val 714 (waveWorkBits (8*Q) N) ∧ Word t.val 715 (waveGrid (8*Q) N) ∧
      Word t.val 716 (waveDegree (8*Q) N+1) := by
  obtain ⟨c0,s0,e0,h0,b0,z0,f0⟩ := RationalDataflow.fixedBankStage_executes dimensionIds dimensionIds_ge
    degreeSetup degreeSetup_valid (by simp [degreeSetup]) (initialDimensions Q N) W
    (fun i _ => initialDimensions_width Q N W hQ hN i)
    (by
      simp [degreeSetup,NatAssign.Instruction.literalWidth,
        show (8:ℕ).bits.length=4 from rfl,show (16:ℕ).bits.length=5 from rfl]
      omega) input tape s hs hz
  change NatAssign.Bank dimensionIds (degreeValues Q N) s0.val at b0
  obtain ⟨c1,s1,e1,h1,b1,z1,f1⟩ := NatAssign.stored_length dimensionIds 712 713 (by decide)
    (by decide) (by decide) (by decide) (degreeValues Q N)
    (by simp [degreeValues_eq,initialDimensions]) input tape s0 b0 z0
  rw [degreeValues_eq,ite_eq_left rfl] at b1
  change NatAssign.Bank dimensionIds (scannedValues Q N) s1.val at b1
  obtain ⟨c2,t,e2,h2,b2,z2,f2⟩ := RationalDataflow.fixedBankStage_executes dimensionIds dimensionIds_ge
    gridSetup gridSetup_valid (by simp [gridSetup]) (scannedValues Q N) (degreeWidth W)
    (scannedValues_width Q N W hQ hN hW) (gridSetup_literalWidth W hW) input tape s1 b1 z1
  change NatAssign.Bank dimensionIds (finalDimensions Q N) t.val at b2
  refine ⟨c0+(c1+c2),t,e0.seq (e1.seq e2),?_,b2,z2,f0.trans ((f1.mono ?_).trans f2),?_,?_,?_,?_,?_,?_⟩
  · have hd := degreeValues_width Q N W hQ hN hW 712 (by decide)
    have hscan : 48*((degreeValues Q N 712).bits.length+1)^2+1≤2^24*(W+2)^2 := by
      have hbase : (degreeValues Q N 712).bits.length+1≤2^9*(W+2) := by unfold degreeWidth at hd;omega
      have hsquare := Nat.pow_le_pow_left hbase 2
      have hone : 1≤(W+2)^2 := one_le_pow₀ (by omega)
      nlinarith only [hsquare,hone]
    have hlast : RationalDataflow.stageCost (degreeWidth W)≤2^114*(W+2)^2 := by
      have hb : degreeWidth W+2≤2^9*(W+2) := by unfold degreeWidth;omega
      unfold RationalDataflow.stageCost
      calc
        _≤2^96*(2^9*(W+2))^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hb 2)
        _=2^114*(W+2)^2 := by ring
    have hfirst : c0≤2^96*(W+2)^2 := h0
    have hmiddle := h1.trans hscan
    have hfinish := h2.trans hlast
    nlinarith only [hfirst,hmiddle,hfinish,Nat.zero_le ((W+2)^2)]
  · decide
  · simpa [finalDimensions_eq,scannedValues,degreeValues_eq,initialDimensions] using b2 710 (by decide)
  · simpa [finalDimensions_eq,scannedValues,degreeValues_eq,initialDimensions] using b2 711 (by decide)
  · simpa [finalDimensions_eq,scannedValues,degreeValues_eq] using b2 712 (by decide)
  · simpa only [finalDimensions_work] using b2 714 (by decide)
  · simpa only [finalDimensions_grid] using b2 715 (by decide)
  · simpa only [finalDimensions_count] using b2 716 (by decide)

#print axioms dimensions_executes
#print axioms finalDimensions_width
end Maxwell.Continuum.Profile.WaveMachine.Runtime
