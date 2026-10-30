import Maxwell.Continuum.CalibrationRootGridIndex

/-! Charged quotient/remainder and dot-product execution for the literal
three-coordinate root quadrature index. -/
namespace Maxwell.Continuum.RationalDataflow.RootGrid
open Maxwell.Cost Maxwell.Cost.Structured
open Calibration.ArrayDecodeMachine (divModValues divModValues_width)
set_option maxHeartbeats 3500000
set_option maxRecDepth 8192

theorem divide_executes (source targetQ targetR : ℕ)
    (hsource : source∈Finset.Icc 330 341) (hq : targetQ∈Finset.Icc 330 341)
    (hr : targetR∈Finset.Icc 330 341) (hqr : targetQ≠targetR)
    (v : ℕ→ℕ) (B : ℕ) (hzero : ∀i∈NaturalQuotient.workPorts,v i=0) (hpos : 0<v 331)
    (hw : ∀i∈ids,(v i).bits.length≤B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : NatAssign.Bank ids v s.val)
    (hz : ∀i,i<5 → RationalAccumulator.Blank s.val i) :
    ∃ cost t,Executes input tape (NaturalDivMod.code source 331 targetQ targetR) cost s t ∧
      cost≤2^100*(B+2)^2 ∧ NatAssign.Bank ids (divModValues v source 331 targetQ targetR) t.val ∧
      (∀i,i<5 → RationalAccumulator.Blank t.val i) ∧
      BinaryPrecision.Frame ({0,1,2,3,4}∪ids) s.val t.val := by
  have hout (i : ℕ) (hi : i∈Finset.Icc 330 341) : i∉NaturalQuotient.workPorts := by
    simp only [Finset.mem_Icc] at hi
    simp only [NaturalQuotient.workPorts,Finset.mem_insert,Finset.mem_singleton]
    omega
  exact NaturalDivMod.executes ids ids_ge Finset.subset_union_left source 331 targetQ targetR
    (Finset.mem_union_right _ hsource) (by decide) (Finset.mem_union_right _ hq)
    (Finset.mem_union_right _ hr) (hout _ hsource) (by decide) (hout _ hq) (hout _ hr)
    hqr v hzero hpos B hw input tape s hs hz

theorem executes (v : ℕ→ℕ) (B : ℕ) (hzero : ∀i∈NaturalQuotient.workPorts,v i=0)
    (hpos : 0<v 331) (hw : ∀i∈ids,(v i).bits.length≤B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : NatAssign.Bank ids v s.val)
    (hz : ∀i,i<5 → RationalAccumulator.Blank s.val i) :
    ∃ cost t,Executes input tape code cost s t ∧ cost≤2^120*(B+2)^2 ∧
      NatAssign.Bank ids (values v) t.val ∧
      (∀i,i<5 → RationalAccumulator.Blank t.val i) ∧
      BinaryPrecision.Frame ({0,1,2,3,4}∪ids) s.val t.val := by
  obtain ⟨c0,s0,e0,h0,b0,z0,f0⟩ := divide_executes 330 332 333 (by decide) (by decide)
    (by decide) (by decide) v B hzero hpos hw input tape s hs hz
  have keep0 (i : ℕ) (hi : i∈NaturalQuotient.workPorts ∨ i=331) : first v i=v i := by
    simp only [NaturalQuotient.workPorts,Finset.mem_insert,Finset.mem_singleton] at hi
    simp (disch := omega) [first,divModValues]
  have w0 := divModValues_width v ids 330 331 332 333 B (by decide) hw
  obtain ⟨c1,s1,e1,h1,b1,z1,f1⟩ := divide_executes 332 332 334 (by decide) (by decide)
    (by decide) (by decide) (first v) B (fun i hi => (keep0 i (Or.inl hi)).trans (hzero i hi))
    (by simpa only [keep0 331 (Or.inr rfl)] using hpos) w0 input tape s0 b0 z0
  have keep1 (i : ℕ) (hi : i∈NaturalQuotient.workPorts ∨ i=331) : second v i=v i := by
    have hi' := hi
    simp only [NaturalQuotient.workPorts,Finset.mem_insert,Finset.mem_singleton] at hi'
    simp only [second,divModValues,Function.update_of_ne (by omega : i≠334),
      Function.update_of_ne (by omega : i≠332),keep0 i hi]
  have w1 := divModValues_width (first v) ids 332 331 332 334 B (by decide) w0
  obtain ⟨c2,s2,e2,h2,b2,z2,f2⟩ := divide_executes 332 340 335 (by decide) (by decide)
    (by decide) (by decide) (second v) B (fun i hi => (keep1 i (Or.inl hi)).trans (hzero i hi))
    (by simpa only [keep1 331 (Or.inr rfl)] using hpos) w1 input tape s1 b1 z1
  obtain ⟨c3,s3,e3,h3,b3,z3,f3⟩ := fixedBankStage_executes ids (fun i hi => by have := ids_ge i hi;omega)
    dot dot_valid (by decide) (third v) B (thirds_width v B hw)
    (by simp [dot,NatAssign.Instruction.literalWidth]) input tape s2 b2 (fun i hi => z2 i (by omega))
  have z3' (i : ℕ) (hi : i<5) : RationalAccumulator.Blank s3.val i := by
    by_cases hh : i<4
    · exact z3 i hh
    have he : i=4 := by omega
    subst i
    exact RationalAccumulator.blank_of_eq (f3.tapes 4 (by decide)) (z2 4 (by decide))
  obtain ⟨c4,t,e4,h4,b4,z4,f4⟩ := divide_executes 339 340 341 (by decide) (by decide)
    (by decide) (by decide) (dotted v) (2^8*(B+1))
    (fun i hi => (dotted_keep v i (Or.inl hi)).trans (hzero i hi))
    (by simpa only [dotted_keep v 331 (Or.inr rfl)] using hpos)
    (dotted_width v B hw) input tape s3 b3 z3'
  refine ⟨c0+(c1+(c2+(c3+c4))),t,e0.seq (e1.seq (e2.seq (e3.seq e4))),?_,b4,z4,
    f0.trans (f1.trans (f2.trans ((f3.mono ?_).trans f4)))⟩
  · have hsqr : (2^8*(B+1)+2)^2≤(2^8*(B+2))^2 := Nat.pow_le_pow_left (by omega) 2
    have h4' : c4≤2^116*(B+2)^2 := by
      apply h4.trans
      calc
        _≤2^100*(2^8*(B+2))^2 := Nat.mul_le_mul_left _ hsqr
        _=_ := by ring
    unfold stageCost at h3
    nlinarith only [h0,h1,h2,h3,h4',Nat.zero_le ((B+2)^2)]
  · intro i hi
    rcases Finset.mem_union.mp hi with hi|hi
    · exact Finset.mem_union_left _ ((show ({0,1,2,3}:Finset ℕ)⊆{0,1,2,3,4} by decide) hi)
    · exact Finset.mem_union_right _ hi

#print axioms executes
end Maxwell.Continuum.RationalDataflow.RootGrid
