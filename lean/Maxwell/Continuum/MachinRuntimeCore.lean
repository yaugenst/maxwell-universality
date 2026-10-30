import Maxwell.Continuum.MachinRuntimeCall

/-! A single fixed Boolean program computes the Machin rational center from
the stored term count. Neither arctangent is expanded in generated code. -/
namespace Maxwell.Continuum.Machin.Runtime
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalTaylor
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

def core : Code := .seq (NatAssign.code prologue)
  (.seq arctanCall (.seq (NatAssign.code saveFirst) (.seq arctanCall (NatAssign.code combine))))
def coreCost (N : ℕ) : ℕ := 3*stageCost N+2*callCost N

theorem core_executes (N : ℕ) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : NatAssign.Bank allIds (fun _ => 0) s.val) (hz : NatAssign.Scratch s.val)
    (ha : AuxReady N s.val) :
    ∃cost t,Executes input tape core cost s t ∧ cost≤coreCost N ∧
      NatAssign.Bank allIds (finalValues N) t.val ∧ NatAssign.Scratch t.val ∧
      AuxReady N t.val ∧ BinaryPrecision.Frame workspace s.val t.val := by
  obtain ⟨c0,s0,e0,h0,b0,z0,f0⟩ := stage_executes N prologue stages_valid.1 (by decide)
    (by simp [prologue,NatAssign.Instruction.literalWidth];decide) (by decide) (fun _ => 0)
    (by intro i _;simp) input tape s hs hz
  have b0' : NatAssign.Bank allIds (initialValues 5) s0.val := by
    intro i hi
    simpa only [prologue_values _ i hi] using b0 i hi
  obtain ⟨c1,s1,e1,h1,b1,z1,a1,f1⟩ := arctan_call N (initialValues 5)
    (fun i _ => initial_width 5 (by decide) i) input tape s0 b0' z0 (ha.frame f0)
  change NatAssign.Bank allIds (firstValues N) s1.val at b1
  obtain ⟨c2,s2,e2,h2,b2,z2,f2⟩ := stage_executes N saveFirst stages_valid.2.1 (by decide)
    (by simp [saveFirst,NatAssign.Instruction.literalWidth];decide) (by decide) (firstValues N)
    (first_width N) input tape s1 b1 z1
  have b2' : NatAssign.Bank allIds (preparedValues N) s2.val := by
    intro i hi
    simpa only [saveFirst_values N i hi] using b2 i hi
  obtain ⟨c3,s3,e3,h3,b3,z3,a3,f3⟩ := arctan_call N (preparedValues N)
    (prepared_input_width N) input tape s2 b2' z2 (a1.frame f2)
  change NatAssign.Bank allIds (secondValues N) s3.val at b3
  obtain ⟨c4,t,e4,h4,bt,zt,ft⟩ := stage_executes N combine stages_valid.2.2 (by decide)
    (by simp [combine,NatAssign.Instruction.literalWidth];decide) (by decide) (secondValues N)
    (fun i _ => second_width N i) input tape s3 b3 z3
  have hsub : allWorkspace⊆workspace := Finset.subset_union_left
  refine ⟨c0+(c1+(c2+(c3+c4))),t,e0.seq (e1.seq (e2.seq (e3.seq e4))),?_,bt,zt,a3.frame ft,
    (f0.mono hsub).trans (f1.trans ((f2.mono hsub).trans (f3.trans (ft.mono hsub))))⟩
  unfold coreCost
  omega

#print axioms core_executes
end Maxwell.Continuum.Machin.Runtime
