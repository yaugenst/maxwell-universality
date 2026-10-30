import Maxwell.Continuum.ProfileRuntimeDimensions
import Maxwell.Continuum.NatAssignOutputWidth

/-! Charged execution of the actual profile dimensions, including the
binary-length scan used by the precision formula. -/
namespace Maxwell.Continuum.Profile.Runtime
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 3500000
set_option maxRecDepth 8192

def degreeWidth (W : ℕ) : ℕ := 2^9*(W+1)
def dimensionWidth (W : ℕ) : ℕ := 2^30*(W+2)

theorem initialDimensions_width (N W : ℕ) (hN : N.bits.length≤W) (i : ℕ) :
    (initialDimensions N i).bits.length≤W := by
  unfold initialDimensions
  split_ifs <;> first | exact hN | simp

theorem degreeValues_width (N W : ℕ) (hN : N.bits.length≤W) (hW : 9≤W)
    (i : ℕ) (hi : i∈dimensionIds) : (degreeValues N i).bits.length≤degreeWidth W := by
  have hw := NatAssign.values_width_bound dimensionIds degreeSetup degreeSetup_valid (initialDimensions N) W
    (fun i _ => initialDimensions_width N W hN i) (by
      simp [degreeSetup,NatAssign.Instruction.literalWidth,
        show (256:ℕ).bits.length=9 from rfl,show (128:ℕ).bits.length=8 from rfl]
      omega) i hi
  exact (Nat.le_succ _).trans hw

theorem scannedValues_width (N W : ℕ) (hN : N.bits.length≤W) (hW : 9≤W)
    (i : ℕ) (hi : i∈dimensionIds) : (scannedValues N i).bits.length≤degreeWidth W := by
  by_cases he : i=662
  · subst i
    simp only [scannedValues,Function.update_self]
    have hn : (profileDegree N).bits.length.bits.length≤(profileDegree N).bits.length := by
      rw [Nat.size_eq_bits_len,Nat.size_le];exact Nat.lt_two_pow_self
    have hd := degreeValues_width N W hN hW 661 (by decide)
    rw [degreeValues_eq,ite_eq_left rfl] at hd
    exact hn.trans hd
  · simpa only [scannedValues,Function.update_of_ne he] using degreeValues_width N W hN hW i hi

theorem gridSetup_literalWidth (W : ℕ) (hW : 9≤W) :
    ∀a∈gridSetup,a.literalWidth≤degreeWidth W := by
  have hw : 9≤degreeWidth W := by unfold degreeWidth;omega
  simp [gridSetup,NatAssign.Instruction.literalWidth,
    show (256:ℕ).bits.length=9 from rfl,show (128:ℕ).bits.length=8 from rfl,
    show (32:ℕ).bits.length=6 from rfl,show (3:ℕ).bits.length=2 from rfl]
  omega

theorem finalDimensions_width (N W : ℕ) (hN : N.bits.length≤W) (hW : 9≤W)
    (i : ℕ) (hi : i∈dimensionIds) : (finalDimensions N i).bits.length≤dimensionWidth W := by
  have hw := NatAssign.values_width_bound dimensionIds gridSetup gridSetup_valid (scannedValues N)
    (degreeWidth W) (scannedValues_width N W hN hW) (gridSetup_literalWidth W hW) i hi
  apply ((Nat.le_succ _).trans hw).trans
  change 2^19*(degreeWidth W+1)≤dimensionWidth W
  unfold degreeWidth dimensionWidth
  omega

theorem dimensions_executes (N W : ℕ) (hN : N.bits.length≤W) (hW : 9≤W)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : NatAssign.Bank dimensionIds (initialDimensions N) s.val) (hz : NatAssign.Scratch s.val) :
    ∃ cost t,Executes input tape dimensionCode cost s t ∧ cost≤2^120*(W+2)^2 ∧
      NatAssign.Bank dimensionIds (finalDimensions N) t.val ∧ NatAssign.Scratch t.val ∧
      BinaryPrecision.Frame dimensionWorkspace s.val t.val ∧
      Word t.val 660 N ∧ Word t.val 661 (profileDegree N) ∧
      Word t.val 663 (profileWorkBits N) ∧ Word t.val 664 (profileGrid N) := by
  obtain ⟨c0,s0,e0,h0,b0,z0,f0⟩ := RationalDataflow.fixedBankStage_executes dimensionIds dimensionIds_ge
    degreeSetup degreeSetup_valid (by simp [degreeSetup]) (initialDimensions N) W
    (fun i _ => initialDimensions_width N W hN i)
    (by
      simp [degreeSetup,NatAssign.Instruction.literalWidth,
        show (256:ℕ).bits.length=9 from rfl,show (128:ℕ).bits.length=8 from rfl]
      omega) input tape s hs hz
  change NatAssign.Bank dimensionIds (degreeValues N) s0.val at b0
  obtain ⟨c1,s1,e1,h1,b1,z1,f1⟩ := NatAssign.stored_length dimensionIds 661 662 (by decide)
    (by decide) (by decide) (by decide) (degreeValues N)
    (by simp [degreeValues_eq,initialDimensions]) input tape s0 b0 z0
  rw [degreeValues_eq,ite_eq_left rfl] at b1
  change NatAssign.Bank dimensionIds (scannedValues N) s1.val at b1
  obtain ⟨c2,t,e2,h2,b2,z2,f2⟩ := RationalDataflow.fixedBankStage_executes dimensionIds dimensionIds_ge
    gridSetup gridSetup_valid (by simp [gridSetup]) (scannedValues N) (degreeWidth W)
    (scannedValues_width N W hN hW) (gridSetup_literalWidth W hW) input tape s1 b1 z1
  change NatAssign.Bank dimensionIds (finalDimensions N) t.val at b2
  refine ⟨c0+(c1+c2),t,e0.seq (e1.seq e2),?_,b2,z2,f0.trans ((f1.mono ?_).trans f2),?_,?_,?_,?_⟩
  · have hd := degreeValues_width N W hN hW 661 (by decide)
    have hscan : 48*((degreeValues N 661).bits.length+1)^2+1≤2^26*(W+2)^2 := by
      have hbase : (degreeValues N 661).bits.length+1≤2^10*(W+2) := by unfold degreeWidth at hd;omega
      have hsquare := Nat.pow_le_pow_left hbase 2
      have hone : 1≤(W+2)^2 := one_le_pow₀ (by omega)
      nlinarith only [hsquare,hone]
    have hlast : RationalDataflow.stageCost (degreeWidth W)≤2^116*(W+2)^2 := by
      have hb : degreeWidth W+2≤2^10*(W+2) := by unfold degreeWidth;omega
      unfold RationalDataflow.stageCost
      calc
        _≤2^96*(2^10*(W+2))^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hb 2)
        _=2^116*(W+2)^2 := by ring
    have hfirst : c0≤2^96*(W+2)^2 := h0
    have hmiddle := h1.trans hscan
    have hfinish := h2.trans hlast
    nlinarith only [hfirst,hmiddle,hfinish,Nat.zero_le ((W+2)^2)]
  · decide
  · simpa [finalDimensions_eq,scannedValues,degreeValues_eq,initialDimensions] using b2 660 (by decide)
  · simpa [finalDimensions_eq,scannedValues,degreeValues_eq] using b2 661 (by decide)
  · simpa only [finalDimensions_work] using b2 663 (by decide)
  · simpa only [finalDimensions_grid] using b2 664 (by decide)

#print axioms dimensions_executes
#print axioms finalDimensions_width
end Maxwell.Continuum.Profile.Runtime
