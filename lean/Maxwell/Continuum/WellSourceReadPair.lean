import Maxwell.Continuum.WellSourceReadOne

/-! The original-well pass obtains both of its source fields by executing
the fixed array readers. The input channels retain their explicit natural
number invariant; no decoded diagonal or degree is supplied by an oracle. -/
namespace Maxwell.Continuum.RationalDataflow.WellSourceRead
open Maxwell.Cost Maxwell.Cost.Structured
open RationalAccumulator (Word Blank)
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

def pairCode : Code := .seq (readCode true) (readCode false)

def pairValues (v : ℕ→Parts) (diagonal degree : ℕ) : ℕ→Parts :=
  NaturalArrayRead.values (NaturalArrayRead.values v 8 diagonal) 9 degree

theorem pairValues_diagonal (v : ℕ→Parts) (diagonal degree : ℕ)
    (hn : (v 8).negative=0) (hd : (v 8).denominator=1) :
    (pairValues v diagonal degree 8).value=(diagonal:ℚ) := by
  simp [pairValues,NaturalArrayRead.values,NaturalChannel.replace,Parts.value,hn,hd]

theorem pairValues_degree (v : ℕ→Parts) (diagonal degree : ℕ)
    (hn : (v 9).negative=0) (hd : (v 9).denominator=1) :
    (pairValues v diagonal degree 9).value=(degree:ℚ) := by
  simp [pairValues,NaturalArrayRead.values,NaturalChannel.replace,Parts.value,hn,hd]

theorem pairValues_preserves (v : ℕ→Parts) (diagonal degree k : ℕ)
    (h8 : k ≠ 8) (h9 : k ≠ 9) : pairValues v diagonal degree k=v k := by
  simp only [pairValues,NaturalArrayRead.values,Function.update_of_ne h8,
    Function.update_of_ne h9]

theorem pair_executes {n : ℕ} (diagonals degrees : Vector (List Bool) n)
    (diagonalBase degreeBase B : ℕ) (hB : 4 ≤ B)
    (hdB : diagonalBase.bits.length ≤ B) (hgB : degreeBase.bits.length ≤ B)
    (index : List Bool) (hlen : index.length ≤ B) (i : Fin n) (hi : addressValue index=i.val)
    (v : ℕ→Parts) (hv : WidthBank WellStrength.bank B v) (hg : Good WellStrength.bank v)
    (m : ℕ→ℕ) (hm : ∀j∈metaIds,(m j).bits.length ≤ B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hr : Ready WellStrength.bank v s) (hs : BankArray.Scratch s.val) (h7 : Blank s.val 7)
    (hmeta : NatAssign.Bank metaIds m s.val)
    (hdiagonal : Word s.val 993 diagonalBase) (hdegree : Word s.val 994 degreeBase)
    (hindex : BankArray.Word s.val 998 index)
    (ha : BitArray.Represents s.val.memory diagonalBase 4 diagonals)
    (hb : BitArray.Represents s.val.memory degreeBase 2 degrees) :
    ∃cost t,Executes input tape pairCode cost s t ∧ cost ≤ 2^22*(B+3)^2 ∧
      Ready WellStrength.bank
        (pairValues v (addressValue (diagonals.get i)) (addressValue (degrees.get i))) t ∧
      Good WellStrength.bank
        (pairValues v (addressValue (diagonals.get i)) (addressValue (degrees.get i))) ∧
      WidthBank WellStrength.bank B
        (pairValues v (addressValue (diagonals.get i)) (addressValue (degrees.get i))) ∧
      BankArray.Scratch t.val ∧ Blank t.val 7 ∧
      NatAssign.Bank metaIds (prepared 2 2 (prepared 4 8 m)) t.val ∧ Frame s.val t.val := by
  obtain ⟨c0,u,e0,hc0,r0,g0,w0,z0,z7,b0,f0⟩ := read_executes true diagonals diagonalBase B hB
    hdB index hlen i hi v hv hg m hm input tape s hr hs h7 hmeta hdiagonal hindex ha
  have hwidth0 : ∀j∈metaIds,(prepared 4 8 m j).bits.length ≤ B := by
    intro j hj
    simp only [metaIds,Finset.mem_insert,Finset.mem_singleton] at hj
    rcases hj with rfl|rfl
    · rw [prepared_width]
      change 3 ≤ B
      omega
    · rw [prepared_clock]
      change 4 ≤ B
      exact hB
  have hdegree0 : Word u.val 994 degreeBase := RationalAccumulator.word_of_eq
    (f0.tapes 994 (by decide) (by decide) (by decide) (by decide)) hdegree
  have hindex0 : BankArray.Word u.val 998 index := BankArray.word_of_eq
    (f0.tapes 998 (by decide) (by decide) (by decide) (by decide)) hindex
  obtain ⟨c1,t,e1,hc1,r1,g1,w1,z1,z17,b1,f1⟩ := read_executes false degrees degreeBase B hB
    hgB index hlen i hi _ w0 g0 (prepared 4 8 m) hwidth0 input tape u r0 z0 z7 b0 hdegree0
    hindex0 (by simpa [wordWidth,f0.memory] using hb)
  exact ⟨c0+c1,t,e0.seq e1,by omega,r1,g1,w1,z1,z17,b1,f0.trans f1⟩

#print axioms pair_executes
end Maxwell.Continuum.RationalDataflow.WellSourceRead
