import Maxwell.Continuum.FourierTensorCacheAllocationData

/-! Fixed-code calculation of the cache allocation and traversal sizes. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime.TensorSetup
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow PartArray
set_option maxHeartbeats 4500000
set_option maxRecDepth 16384

def setupChanges : Finset ℕ := dimensionWorkspace∪{725,726,727,728,1100,1110}
def setupWidth (W : ℕ) : ℕ := 2^54*(W+2)

theorem setup_executes (Q N R width bp bn bd W : ℕ) (hW : 6≤W)
    (hw : ∀i∈ids,(initial Q N R width bp bn bd i).bits.length≤W)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hb : NatAssign.Bank ids (initial Q N R width bp bn bd) s.val) (hz : NatAssign.Scratch s.val) :
    ∃cost t,Executes input tape setupCode cost s t ∧ cost≤2^156*(W+2)^2 ∧
      NatAssign.Bank ids (values Q N R width bp bn bd) t.val ∧
      (∀i∈ids,(values Q N R width bp bn bd i).bits.length≤setupWidth W) ∧
      NatAssign.Scratch t.val ∧ BinaryPrecision.Frame setupChanges s.val t.val := by
  have hQ : Q.bits.length≤W := by simpa [initial,initialDimensions] using hw 710 (by simp [ids,dimensionIds])
  have hN : N.bits.length≤W := by simpa [initial,initialDimensions] using hw 711 (by simp [ids,dimensionIds])
  have hd : NatAssign.Bank dimensionIds (initialDimensions Q N) s.val := by
    intro i hi
    simpa only [initial_dimensions Q N R width bp bn bd i hi] using hb i (Finset.mem_union_left _ hi)
  obtain ⟨c0,u,e0,hc0,b0,z0,f0,_,_,_,_,_,_⟩ := dimensions_executes Q N W hQ hN hW input tape s hd hz
  have bank : NatAssign.Bank ids (afterDimensions Q N R width bp bn bd) u.val := by
    intro i hi
    by_cases hid : i∈dimensionIds
    · simpa only [afterDimensions,ite_eq_left hid] using b0 i hid
    · rw [afterDimensions,ite_eq_right hid]
      apply RationalAccumulator.word_of_eq (f0.tapes i _) (hb i hi)
      intro him
      rcases Finset.mem_union.mp him with low|high
      · have hilow := ids_ge i hi
        simp only [Finset.mem_insert,Finset.mem_singleton] at low
        omega
      · exact hid high
  have width0 : ∀i∈ids,(afterDimensions Q N R width bp bn bd i).bits.length≤dimensionWidth W := by
    intro i hi
    by_cases hid : i∈dimensionIds
    · simpa only [afterDimensions,ite_eq_left hid] using finalDimensions_width Q N W hQ hN hW i hid
    · simpa only [afterDimensions,ite_eq_right hid] using (hw i hi).trans
        (show W≤dimensionWidth W by unfold dimensionWidth;omega)
  have literalWidth : ∀a∈plan,a.literalWidth≤dimensionWidth W := by
    simp [plan,NatAssign.Instruction.literalWidth,show (2:ℕ).bits.length=2 by decide,
      show (5:ℕ).bits.length=3 by decide,
      show (7:ℕ).bits.length=3 by decide]
    unfold dimensionWidth
    omega
  obtain ⟨c1,t,e1,hc1,b1,z1,f1⟩ := NatAssign.executes ids ids_ge plan plan_valid
    (afterDimensions Q N R width bp bn bd) input tape u bank z0
  have price := hc1.trans (NatAssign.price_bound ids plan plan_valid _ (dimensionWidth W) width0 literalWidth)
  have widths := NatAssign.values_width_bound ids plan plan_valid _ (dimensionWidth W) width0 literalWidth
  refine ⟨c0+c1,t,e0.seq e1,?_,b1,?_,z1,
    (f0.mono Finset.subset_union_left).trans (f1.mono (by decide))⟩
  · have hp : c1≤3000*8^23*(dimensionWidth W+2)^2 := by
      simpa only [plan,List.length_cons,List.length_nil] using price
    have hs : (dimensionWidth W+2)^2≤(2^29)^2*(W+2)^2 := by
      have bound : dimensionWidth W+2≤2^29*(W+2) := by unfold dimensionWidth;omega
      simpa only [mul_pow] using Nat.pow_le_pow_left bound 2
    nlinarith only [hp,hs,hc0,Nat.zero_le ((W+2)^2)]
  · intro i hi
    have h := widths i hi
    change (values Q N R width bp bn bd i).bits.length+1≤2^23*(dimensionWidth W+1) at h
    unfold setupWidth
    unfold dimensionWidth at h
    omega

#print axioms setup_executes
end Maxwell.Continuum.Profile.WaveMachine.Runtime.TensorSetup
