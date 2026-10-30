import Maxwell.Continuum.MachinStages

/-! A composed, charged Boolean program for the literal Machin pi center. -/

namespace Maxwell.Continuum.Machin
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalTaylor
set_option maxHeartbeats 1500000

def stageCost (N : ℕ) : ℕ := 2^80*(RationalArctan.width (N+6) 8+2)^2
def costBound (N : ℕ) : ℕ := 3*stageCost N+2*RationalArctan.costBound (N+6) 8

def program (N : ℕ) : Code :=
  .seq (NatAssign.code prologue)
    (.seq (RationalArctan.program negativeSigns (N+6))
      (.seq (NatAssign.code saveFirst)
        (.seq (RationalArctan.program negativeSigns (N+6)) (NatAssign.code combine))))

theorem stage_executes (N : ℕ) (ins : List NatAssign.Instruction)
    (hv : ∀ a∈ins, a.Valid allIds) (hl : ins.length≤21)
    (hc : ∀ a∈ins, a.literalWidth≤8) (hf : NatAssign.changes ins⊆allWorkspace)
    (v : ℕ→ℕ) (hw : ∀ i∈allIds, (v i).bits.length≤RationalArctan.width (N+6) 8)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : NatAssign.Bank allIds v s.val) (hsc : NatAssign.Scratch s.val) :
    ∃ cost t, Executes input tape (NatAssign.code ins) cost s t ∧
      cost≤stageCost N ∧ NatAssign.Bank allIds (NatAssign.values ins v) t.val ∧
      NatAssign.Scratch t.val ∧ BinaryPrecision.Frame allWorkspace s.val t.val := by
  obtain ⟨cost,t,he,hcost,hb,hsc',hframe⟩ := NatAssign.executes allIds allIds_ge ins hv v input tape s hs hsc
  have hp := NatAssign.price_bound allIds ins hv v (RationalArctan.width (N+6) 8) hw
    (fun a ha => (hc a ha).trans (prefix_width_ge_eight N))
  have hcoef : 3000*8^ins.length≤(2:ℕ)^80 := by
    calc
      _ ≤ 3000*8^21 := Nat.mul_le_mul_left 3000 (Nat.pow_le_pow_right (by decide) hl)
      _ ≤ _ := by norm_num
  exact ⟨cost,t,he,hcost.trans (hp.trans (Nat.mul_le_mul_right _ hcoef)),hb,hsc',hframe.mono hf⟩

theorem costBound_polynomial (N : ℕ) : costBound N≤2^112*(N+1)^5 := by
  have hw := wordWidth_bound N
  have hwidth : RationalArctan.width (N+6) 8+2≤2^12*(N+1)^2 := by
    unfold wordWidth at hw
    omega
  have hs := Nat.pow_le_pow_left hwidth 2
  have ha := RationalArctan.costBound_polynomial (N+6) 8
  have hn : N+6+2≤8*(N+1) := by omega
  have har := ha.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hn 5)))
  have h4 : (N+1)^4≤(N+1)^5 := Nat.pow_le_pow_right (by omega) (by decide)
  have hstage : stageCost N≤2^104*(N+1)^5 := by
    calc
      _ ≤ 2^80*(2^12*(N+1)^2)^2 := Nat.mul_le_mul_left _ hs
      _ = 2^104*(N+1)^4 := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ h4
  unfold costBound
  nlinarith only [hstage,har]

/-- Starting with the finite work bank blank, the program produces the
literal Machin center as a signed numerator pair and positive denominator.
All arithmetic is performed by the preceding stored-word subprograms. -/
theorem executes (N : ℕ) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : NatAssign.Bank allIds (fun _ => 0) s.val) (hsc : NatAssign.Scratch s.val) :
    ∃ cost t, Executes input tape (program N) cost s t ∧ cost≤costBound N ∧
      Word t.val 623 (numeratorPositive N) ∧ Word t.val 624 (numeratorNegative N) ∧
      Word t.val 625 (commonDenominator N) ∧ NatAssign.Scratch t.val ∧
      BinaryPrecision.Frame allWorkspace s.val t.val := by
  obtain ⟨c0,s0,e0,h0,b0,z0,f0⟩ := stage_executes N prologue stages_valid.1 (by decide)
    (by simp [prologue,NatAssign.Instruction.literalWidth]; decide) (by decide) (fun _ => 0)
    (by intro i _; simp) input tape s hs hsc
  have b0' : NatAssign.Bank allIds (initialValues 5) s0.val := by
    intro i hi
    simpa only [prologue_values _ i hi] using b0 i hi
  obtain ⟨c1,s1,e1,h1,b1,z1,f1⟩ := RationalArctan.program_extended allIds ids_subset outside_workspace
    (initialValues 5) negativeSigns (N+6) 8 (by decide)
    (fun i _ => initial_width 5 (by decide) i) input tape s0 b0' z0
  change NatAssign.Bank allIds (firstValues N) s1.val at b1
  obtain ⟨c2,s2,e2,h2,b2,z2,f2⟩ := stage_executes N saveFirst stages_valid.2.1 (by decide)
    (by simp [saveFirst,NatAssign.Instruction.literalWidth]; decide) (by decide) (firstValues N)
    (first_width N) input tape s1 b1 z1
  have b2' : NatAssign.Bank allIds (preparedValues N) s2.val := by
    intro i hi
    simpa only [saveFirst_values N i hi] using b2 i hi
  obtain ⟨c3,s3,e3,h3,b3,z3,f3⟩ := RationalArctan.program_extended allIds ids_subset outside_workspace
    (preparedValues N) negativeSigns (N+6) 8 (by decide) (prepared_input_width N)
    input tape s2 b2' z2
  change NatAssign.Bank allIds (secondValues N) s3.val at b3
  obtain ⟨c4,t,e4,h4,bt,zt,ft⟩ := stage_executes N combine stages_valid.2.2 (by decide)
    (by simp [combine,NatAssign.Instruction.literalWidth]; decide) (by decide) (secondValues N)
    (fun i _ => second_width N i) input tape s3 b3 z3
  have hsub : RationalArctan.workspace⊆allWorkspace := by decide
  refine ⟨c0+(c1+(c2+(c3+c4))),t,e0.seq (e1.seq (e2.seq (e3.seq e4))),?_,?_,?_,?_,zt,
    f0.trans ((f1.mono hsub).trans (f2.trans ((f3.mono hsub).trans ft)))⟩
  · unfold costBound
    omega
  · simpa only [(combine_values N).1] using bt 623 (by decide)
  · simpa only [(combine_values N).2.1] using bt 624 (by decide)
  · simpa only [(combine_values N).2.2] using bt 625 (by decide)

theorem compiled_computes (N : ℕ) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : NatAssign.Bank allIds (fun _ => 0) s.val) (hsc : NatAssign.Scratch s.val) :
    ∃ (cost : ℕ) (t : Store),
      (runPriced ((program N).compile.next input tape) (2^112*(N+1)^5+1) s.val).finished=
        some (t.place (program N).size) ∧
      (runPriced ((program N).compile.next input tape) (2^112*(N+1)^5+1) s.val).instructions=cost ∧
      cost≤2^112*(N+1)^5 ∧
      Word t.val 623 (numeratorPositive N) ∧ Word t.val 624 (numeratorNegative N) ∧
      Word t.val 625 (commonDenominator N) ∧
      (Maxwell.Certificate.Elementary.piApprox N).center=
        ((numeratorPositive N:ℚ)-numeratorNegative N)/commonDenominator N := by
  obtain ⟨cost,t,he,hc,hp,hn,hd,_,_⟩ := executes N input tape s hs hsc
  have hpCost := hc.trans (costBound_polynomial N)
  obtain ⟨hrun,hcost⟩ := he.compiled_run (2^112*(N+1)^5+1) (by omega)
  exact ⟨cost,t,hrun,hcost,hpCost,hp,hn,hd,piApprox_center N⟩

#print axioms executes
#print axioms compiled_computes

end Maxwell.Continuum.Machin
