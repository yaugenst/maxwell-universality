import Maxwell.Continuum.CalibrationRootFrequencyCoordinates

/-! Actual fixed program producing all three modular negative frequencies.
The head is separate so its parity word can be saved before the tail. -/
namespace Maxwell.Continuum.RationalDataflow.RootFrequency
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 3500000
set_option maxRecDepth 8192

def tailCode : Code := .seq coordinateCode
  (.seq (negativeCode 333 336) (.seq (negativeCode 334 337) (negativeCode 335 338)))

theorem negative_zero (coordinate target : ℕ) (ht : target∈({336,337,338}:Finset ℕ))
    (n : ℕ→ℕ) (hz : ∀i∈NaturalQuotient.workPorts,n i=0) :
    ∀i∈NaturalQuotient.workPorts,negative coordinate target n i=0 := by
  intro i hi
  have hh := hi
  simp only [NaturalQuotient.workPorts,Finset.mem_insert,Finset.mem_singleton] at hh
  simp only [Finset.mem_insert,Finset.mem_singleton] at ht
  rw [negative_keep coordinate target n i (by omega) (by omega) (by omega),hz i hi]

theorem tail_width (n : ℕ→ℕ) (B : ℕ) (hn : ∀i∈ids,(pair n i).bits.length≤B) :
    ∀i∈ids,(values n i).bits.length≤4096*(B+1) := by
  have w0 := coordinate_width n B hn
  have w1 := negative_width 333 336 (by decide) (factored n) (4*(B+1)) w0
  have w2 := negative_width 334 337 (by decide) (negative 333 336 (factored n))
    (8*(4*(B+1)+1)) w1
  have w3 := negative_width 335 338 (by decide) (negative 334 337 (negative 333 336 (factored n)))
    (8*(8*(4*(B+1)+1)+1)) w2
  intro i hi
  exact (w3 i hi).trans (by omega)

theorem tail_executes (n : ℕ→ℕ) (B : ℕ)
    (hn : ∀i∈ids,(pair n i).bits.length≤B)
    (hz : ∀i∈NaturalQuotient.workPorts,n i=0) (hp : 0 < n 331)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hb : NatAssign.Bank ids (pair n) s.val) (hblank : ∀i,i<5 → RationalAccumulator.Blank s.val i) :
    ∃cost t,Executes input tape tailCode cost s t ∧ cost≤2^130*(B+2)^2 ∧
      NatAssign.Bank ids (values n) t.val ∧
      (∀i,i<5 → RationalAccumulator.Blank t.val i) ∧ BinaryPrecision.Frame changed s.val t.val := by
  have zeroPair (i : ℕ) (hi : i∈NaturalQuotient.workPorts) : pair n i=0 := by
    have hh := hi
    simp only [NaturalQuotient.workPorts,Finset.mem_insert,Finset.mem_singleton] at hh
    simp only [pair,Calibration.ArrayDecodeMachine.divModValues,
      Function.update_of_ne (by omega : i≠341),Function.update_of_ne (by omega : i≠330),
      prepared_keep n i ⟨by omega,by omega⟩,hz i hi]
  obtain ⟨c0,s0,e0,h0,b0,z0,f0⟩ := coordinate_executes n B hn zeroPair hp input tape s hb hblank
  have w0 := coordinate_width n B hn
  have zero0 (i : ℕ) (hi : i∈NaturalQuotient.workPorts) : factored n i=0 := by
    rw [factored_keep n i (Or.inl hi),hz i hi]
  have p0 : 0 < factored n 331 := by rw [factored_keep n 331 (Or.inr rfl)];exact hp
  obtain ⟨c1,s1,e1,h1,b1,z1,f1⟩ := negative_executes 333 336 (by decide) (by decide)
    (factored n) (4*(B+1)) w0 zero0 p0 input tape s0 b0 z0
  have w1 := negative_width 333 336 (by decide) (factored n) (4*(B+1)) w0
  have zero1 := negative_zero 333 336 (by decide) (factored n) zero0
  have p1 : 0 < negative 333 336 (factored n) 331 := by
    rw [negative_keep _ _ _ 331 (by decide) (by decide) (by decide)];exact p0
  obtain ⟨c2,s2,e2,h2,b2,z2,f2⟩ := negative_executes 334 337 (by decide) (by decide)
    (negative 333 336 (factored n)) (8*(4*(B+1)+1)) w1 zero1 p1 input tape s1 b1 z1
  have w2 := negative_width 334 337 (by decide) (negative 333 336 (factored n))
    (8*(4*(B+1)+1)) w1
  have zero2 := negative_zero 334 337 (by decide) (negative 333 336 (factored n)) zero1
  have p2 : 0 < negative 334 337 (negative 333 336 (factored n)) 331 := by
    rw [negative_keep _ _ _ 331 (by decide) (by decide) (by decide)];exact p1
  obtain ⟨c3,t,e3,h3,b3,z3,f3⟩ := negative_executes 335 338 (by decide) (by decide)
    (negative 334 337 (negative 333 336 (factored n))) (8*(8*(4*(B+1)+1)+1))
    w2 zero2 p2 input tape s2 b2 z2
  refine ⟨c0+(c1+(c2+c3)),t,e0.seq (e1.seq (e2.seq e3)),?_,b3,z3,
    f0.trans (f1.trans (f2.trans f3))⟩
  have sq0 : (4*(B+1)+2)^2≤512^2*(B+2)^2 := by
    calc
      _ ≤ (512*(B+2))^2 := Nat.pow_le_pow_left (by omega) _
      _ = _ := by ring
  have sq1 : (8*(4*(B+1)+1)+2)^2≤512^2*(B+2)^2 := by
    calc
      _ ≤ (512*(B+2))^2 := Nat.pow_le_pow_left (by omega) _
      _ = _ := by ring
  have sq2 : (8*(8*(4*(B+1)+1)+1)+2)^2≤512^2*(B+2)^2 := by
    calc
      _ ≤ (512*(B+2))^2 := Nat.pow_le_pow_left (by omega) _
      _ = _ := by ring
  have h1' := h1.trans (Nat.mul_le_mul_left (2^109) sq0)
  have h2' := h2.trans (Nat.mul_le_mul_left (2^109) sq1)
  have h3' := h3.trans (Nat.mul_le_mul_left (2^109) sq2)
  omega

#print axioms tail_executes
end Maxwell.Continuum.RationalDataflow.RootFrequency
