import Maxwell.Continuum.CutoffScalePreparationMachine

/-! Raw bit-cost and table preservation for the executed scale initializer. -/
namespace Maxwell.Continuum.Calibration.RawCutoff
open RationalDataflow RationalDataflow.PartArray Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 3000000
set_option maxRecDepth 32768

theorem scalePreparationCost_polynomial (n W len oldlen : ℕ) (hlen : len≤W) (hold : oldlen≤W) :
    scalePreparationCost n W len oldlen≤2^128*(n+W+4)^3 := by
  let Z := n+W+4
  have hZ : 1≤Z := by dsimp [Z];omega
  have hn : n≤Z := by dsimp [Z];omega
  have hZ2 : 1≤Z^2 := one_le_pow₀ hZ
  have hZ23 : Z^2≤Z^3 := Nat.pow_le_pow_right hZ (by decide)
  have hiw : 128*(W+4)+3≤131*Z := by dsimp [Z];omega
  have hip := Nat.pow_le_pow_left hiw 2
  have hi : operationCost (128*(W+4))≤2^115*Z^2 := by
    unfold operationCost
    nlinarith only [hip,Nat.zero_le (Z^2)]
  have hliw : 64*(n+1)+3≤67*Z := by dsimp [Z];omega
  have hlip := Nat.pow_le_pow_left hliw 2
  have hli : operationCost (64*(n+1))≤2^113*Z^2 := by
    unfold operationCost
    nlinarith only [hlip,Nat.zero_le (Z^2)]
  have hloop : (n-1)*(2*operationCost (64*(n+1))+1)≤2^115*Z^3 := by
    have hp : 2*operationCost (64*(n+1))+1≤2^115*Z^2 := by nlinarith only [hli,hZ2]
    have hm := Nat.mul_le_mul (show n-1≤Z by omega) hp
    nlinarith only [hm]
  have hsw : 8*(n+1)+2≤10*Z := by dsimp [Z];omega
  have hsp := Nat.pow_le_pow_left hsw 2
  have hs : stageCost (8*(n+1))≤2^103*Z^2 := by
    unfold stageCost
    nlinarith only [hsp,Nat.zero_le (Z^2)]
  have hcounter : (6*oldlen+15*len+21)+(29*len+32)+n*(13*len+15)+(21*len+21)≤256*Z^2 := by
    dsimp [Z]
    nlinarith
  have hinit : 7*operationCost (128*(W+4))+1≤2^118*Z^2 := by nlinarith only [hi,hZ2]
  unfold scalePreparationCost
  change _≤2^128*Z^3
  nlinarith only [hinit,hloop,hs,hcounter,hZ23]

theorem scalePreparation_keeps {input : List Bool} {tape : ℕ→Bool} {cost : ℕ} {s t : Store}
    (ex : Executes input tape scalePreparationCode cost s t) (i : ℕ)
    (hi : i∈([5,6,7,8,9,37,200,202,203,204,205,210,212,213,214,215,216,220,221,222,223]:List ℕ)) :
    t.val.tapes i=s.val.tapes i :=
  ex.protectsTape i (List.all_eq_true.mp scalePreparation_protects_tables i hi)

theorem scalePreparation_table_frame {n : ℕ} {a : Table n} {input : List Bool} {tape : ℕ→Bool}
    {cost : ℕ} {s t : Store} (ha : a.Ready s)
    (ex : Executes input tape scalePreparationCode cost s t) (hz : NatAssign.Scratch t.val) : a.Ready t := by
  have hm := ex.protectsMemory scalePreparation_protects_memory
  refine ⟨⟨hz 0 (by decide),hz 1 (by decide),hz 2 (by decide),hz 3 (by decide),?_,?_,?_,?_⟩,
    ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact RationalAccumulator.blank_of_eq (scalePreparation_keeps ex 5 (by simp)) ha.scratch.2.2.2.2.1
  · exact RationalAccumulator.blank_of_eq (scalePreparation_keeps ex 6 (by simp)) ha.scratch.2.2.2.2.2.1
  · exact RationalAccumulator.blank_of_eq (scalePreparation_keeps ex 8 (by simp)) ha.scratch.2.2.2.2.2.2.1
  · exact RationalAccumulator.blank_of_eq (scalePreparation_keeps ex 9 (by simp)) ha.scratch.2.2.2.2.2.2.2
  · exact RationalAccumulator.blank_of_eq (scalePreparation_keeps ex 7 (by simp)) ha.seven
  · exact BankArray.word_of_eq (scalePreparation_keeps ex 200 (by simp)) ha.width
  · exact BankArray.word_of_eq (scalePreparation_keeps ex 202 (by simp)) ha.basePositive
  · exact BankArray.word_of_eq (scalePreparation_keeps ex 203 (by simp)) ha.baseNegative
  · exact BankArray.word_of_eq (scalePreparation_keeps ex 204 (by simp)) ha.baseDenominator
  · exact BankArray.word_of_eq (scalePreparation_keeps ex 205 (by simp)) ha.clock
  · simpa only [hm] using ha.positive
  · simpa only [hm] using ha.negative
  · simpa only [hm] using ha.denominator

theorem scalePreparation_output_frame {n : ℕ} {a : Table n} {input : List Bool} {tape : ℕ→Bool}
    {cost : ℕ} {s t : Store} (ha : a.OutputReady s)
    (ex : Executes input tape scalePreparationCode cost s t)
    (hz : BankArray.Scratch t.val) (h7 : RationalAccumulator.Blank t.val 7) : a.OutputReady t := by
  apply ha.transfer (ex.protectsMemory scalePreparation_protects_memory) _ hz h7
  intro i hi
  apply scalePreparation_keeps ex i
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
  tauto

#print axioms scalePreparationCost_polynomial
#print axioms scalePreparation_table_frame
end Maxwell.Continuum.Calibration.RawCutoff
