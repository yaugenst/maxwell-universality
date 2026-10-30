import Maxwell.Continuum.MachinProgram
import Maxwell.Continuum.NatAssignOutputWidth

/-! Full work-bank postcondition for the literal Machin program, so
callers can charge cleanup and safely compose repeated evaluations. -/
namespace Maxwell.Continuum.Machin
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalTaylor
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

def finalValues (N : ℕ) : ℕ→ℕ := NatAssign.values combine (secondValues N)

def finalWidth (N : ℕ) : ℕ := 2^21*(RationalArctan.width (N+6) 8+1)

theorem finalValues_width (N i : ℕ) (hi : i∈allIds) :
    (finalValues N i).bits.length≤finalWidth N := by
  have h := NatAssign.values_width_bound allIds combine stages_valid.2.2 (secondValues N)
    (RationalArctan.width (N+6) 8) (fun j _ => second_width N j)
    (fun a ha => by
      have hc : a.literalWidth≤8 := by
        simp only [combine,List.mem_cons,List.not_mem_nil,or_false] at ha
        rcases ha with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;>
          subst a <;> simp [NatAssign.Instruction.literalWidth] <;> decide
      exact hc.trans (prefix_width_ge_eight N)) i hi
  have hl : combine.length=21 := rfl
  rw [hl] at h
  exact (Nat.le_add_right _ 1).trans h

theorem executes_bank (N : ℕ) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : NatAssign.Bank allIds (fun _ => 0) s.val) (hsc : NatAssign.Scratch s.val) :
    ∃ cost t,Executes input tape (program N) cost s t ∧ cost≤costBound N ∧
      NatAssign.Bank allIds (finalValues N) t.val ∧ NatAssign.Scratch t.val ∧
      BinaryPrecision.Frame allWorkspace s.val t.val := by
  obtain ⟨c0,s0,e0,h0,b0,z0,f0⟩ := stage_executes N prologue stages_valid.1 (by decide)
    (by simp [prologue,NatAssign.Instruction.literalWidth];decide) (by decide) (fun _ => 0)
    (by intro i _;simp) input tape s hs hsc
  have b0' : NatAssign.Bank allIds (initialValues 5) s0.val := by
    intro i hi
    simpa only [prologue_values _ i hi] using b0 i hi
  obtain ⟨c1,s1,e1,h1,b1,z1,f1⟩ := RationalArctan.program_extended allIds ids_subset outside_workspace
    (initialValues 5) negativeSigns (N+6) 8 (by decide)
    (fun i _ => initial_width 5 (by decide) i) input tape s0 b0' z0
  change NatAssign.Bank allIds (firstValues N) s1.val at b1
  obtain ⟨c2,s2,e2,h2,b2,z2,f2⟩ := stage_executes N saveFirst stages_valid.2.1 (by decide)
    (by simp [saveFirst,NatAssign.Instruction.literalWidth];decide) (by decide) (firstValues N)
    (first_width N) input tape s1 b1 z1
  have b2' : NatAssign.Bank allIds (preparedValues N) s2.val := by
    intro i hi
    simpa only [saveFirst_values N i hi] using b2 i hi
  obtain ⟨c3,s3,e3,h3,b3,z3,f3⟩ := RationalArctan.program_extended allIds ids_subset outside_workspace
    (preparedValues N) negativeSigns (N+6) 8 (by decide) (prepared_input_width N)
    input tape s2 b2' z2
  change NatAssign.Bank allIds (secondValues N) s3.val at b3
  obtain ⟨c4,t,e4,h4,bt,zt,ft⟩ := stage_executes N combine stages_valid.2.2 (by decide)
    (by simp [combine,NatAssign.Instruction.literalWidth];decide) (by decide) (secondValues N)
    (fun i _ => second_width N i) input tape s3 b3 z3
  have hsub : RationalArctan.workspace⊆allWorkspace := by decide
  refine ⟨c0+(c1+(c2+(c3+c4))),t,e0.seq (e1.seq (e2.seq (e3.seq e4))),?_,bt,zt,
    f0.trans ((f1.mono hsub).trans (f2.trans ((f3.mono hsub).trans ft)))⟩
  unfold costBound
  omega

#print axioms finalValues_width
#print axioms executes_bank
end Maxwell.Continuum.Machin
