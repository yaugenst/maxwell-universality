import Maxwell.Continuum.CalibrationRootFrequency

/-! Fixed arithmetic stages for the literal centered-frequency decoder. -/
namespace Maxwell.Continuum.RationalDataflow.RootFrequency
open Maxwell.Cost Maxwell.Cost.Structured
open Calibration.ArrayDecodeMachine (divModValues divModValues_width nat_values_width)
set_option maxHeartbeats 3500000
set_option maxRecDepth 8192

def changed : Finset ℕ := {0,1,2,3,4}∪ids
def headCode : Code := .seq (NatAssign.code prepare) (NaturalDivMod.code 330 343 330 341)
def negativeCode (coordinate target : ℕ) : Code :=
  .seq (NatAssign.code (negativePrepare coordinate)) (NaturalDivMod.code 341 331 332 target)

theorem ids_ge (i : ℕ) (hi : i∈ids) : 10 ≤ i := by
  simp only [ids,Finset.mem_union,Finset.mem_Icc,NaturalQuotient.workPorts,
    Finset.mem_insert,Finset.mem_singleton] at hi
  omega

theorem range_outside_work (i : ℕ) (hi : i∈Finset.Icc 330 344) :
    i∉NaturalQuotient.workPorts := by
  simp only [Finset.mem_Icc] at hi
  simp only [NaturalQuotient.workPorts,Finset.mem_insert,Finset.mem_singleton]
  omega

theorem divide_executes (source divisor q r : ℕ)
    (hs : source∈Finset.Icc 330 344) (hd : divisor∈Finset.Icc 330 344)
    (hq : q∈Finset.Icc 330 344) (hr : r∈Finset.Icc 330 344) (hqr : q≠r)
    (n : ℕ→ℕ) (B : ℕ) (hn : ∀i∈ids,(n i).bits.length≤B)
    (hz : ∀i∈NaturalQuotient.workPorts,n i=0) (hpos : 0 < n divisor)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hb : NatAssign.Bank ids n s.val) (hblank : ∀i,i<5 → RationalAccumulator.Blank s.val i) :
    ∃cost t,Executes input tape (NaturalDivMod.code source divisor q r) cost s t ∧
      cost≤2^100*(B+2)^2 ∧ NatAssign.Bank ids (divModValues n source divisor q r) t.val ∧
      (∀i,i<5 → RationalAccumulator.Blank t.val i) ∧ BinaryPrecision.Frame changed s.val t.val :=
  NaturalDivMod.executes ids ids_ge Finset.subset_union_left source divisor q r
    (Finset.mem_union_right _ hs) (Finset.mem_union_right _ hd)
    (Finset.mem_union_right _ hq) (Finset.mem_union_right _ hr)
    (range_outside_work _ hs) (range_outside_work _ hd)
    (range_outside_work _ hq) (range_outside_work _ hr) hqr n hz hpos B hn input tape s hb hblank

theorem stage_executes (plan : List NatAssign.Instruction)
    (hv : ∀a∈plan,a.Valid ids) (hlen : plan.length≤16)
    (n : ℕ→ℕ) (B : ℕ) (hn : ∀i∈ids,(n i).bits.length≤B)
    (hl : ∀a∈plan,a.literalWidth≤B) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hb : NatAssign.Bank ids n s.val) (hz : ∀i,i<5 → RationalAccumulator.Blank s.val i) :
    ∃cost t,Executes input tape (NatAssign.code plan) cost s t ∧ cost≤stageCost B ∧
      NatAssign.Bank ids (NatAssign.values plan n) t.val ∧
      (∀i,i<5 → RationalAccumulator.Blank t.val i) ∧ BinaryPrecision.Frame changed s.val t.val := by
  obtain ⟨c,t,e,hc,bt,zt,f⟩ := fixedBankStage_executes ids (fun i hi => by have := ids_ge i hi;omega)
    plan hv (by omega) n B hn hl input tape s hb (fun i hi => hz i (by omega))
  refine ⟨c,t,e,hc,bt,?_,f.mono ?_⟩
  · intro i hi
    by_cases h4 : i<4
    · exact zt i h4
    have he : i=4 := by omega
    subst i
    exact RationalAccumulator.blank_of_eq (f.tapes 4 (by decide)) (hz 4 (by decide))
  · intro i hi
    rcases Finset.mem_union.mp hi with hi|hi
    · exact Finset.mem_union_left _ ((show ({0,1,2,3}:Finset ℕ)⊆{0,1,2,3,4} by decide) hi)
    · exact Finset.mem_union_right _ hi

theorem prepare_valid : ∀a∈prepare,a.Valid ids := by
  simp [prepare,NatAssign.Instruction.Valid,ids]

theorem prepared_keep (n : ℕ→ℕ) (i : ℕ) (hi : i≠343 ∧ i≠344) : prepared n i=n i := by
  simp [prepared,prepare,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.target,hi.1,hi.2]

theorem head_executes (n : ℕ→ℕ) (B : ℕ) (hB : 2≤B)
    (hn : ∀i∈ids,(n i).bits.length≤B) (hz : ∀i∈NaturalQuotient.workPorts,n i=0)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hb : NatAssign.Bank ids n s.val) (hblank : ∀i,i<5 → RationalAccumulator.Blank s.val i) :
    ∃cost t,Executes input tape headCode cost s t ∧ cost≤2^107*(B+2)^2 ∧
      NatAssign.Bank ids (pair n) t.val ∧
      (∀i,i<5 → RationalAccumulator.Blank t.val i) ∧ BinaryPrecision.Frame changed s.val t.val := by
  have hl : ∀a∈prepare,a.literalWidth≤B := by
    simp [prepare,NatAssign.Instruction.literalWidth,show (2:ℕ).bits.length=2 by rfl]
    omega
  obtain ⟨c0,s0,e0,h0,b0,z0,f0⟩ := stage_executes prepare prepare_valid (by decide) n B hn hl input tape s hb hblank
  have w0 : ∀i∈ids,(prepared n i).bits.length≤4*(B+1) := by
    simpa only [prepared,show prepare.length=2 by rfl,show 2^2=4 by rfl] using
      nat_values_width ids prepare prepare_valid n B hn hl
  have zero0 (i : ℕ) (hi : i∈NaturalQuotient.workPorts) : prepared n i=0 := by
    have hh := hi
    simp only [NaturalQuotient.workPorts,Finset.mem_insert,Finset.mem_singleton] at hh
    rw [prepared_keep n i ⟨by omega,by omega⟩,hz i hi]
  have pos0 : 0 < prepared n 343 := by
    simp [prepared,prepare,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.value,
      NatAssign.Instruction.target]
  obtain ⟨c1,t,e1,h1,b1,z1,f1⟩ := divide_executes 330 343 330 341 (by decide) (by decide)
    (by decide) (by decide) (by decide) (prepared n) (4*(B+1)) w0 zero0 pos0 input tape s0 b0 z0
  refine ⟨c0+c1,t,e0.seq e1,?_,b1,z1,f0.trans f1⟩
  have hh : (4*(B+1)+2)^2≤16*(B+2)^2 := by
    calc
      _ ≤ (4*(B+2))^2 := Nat.pow_le_pow_left (by omega) _
      _ = _ := by ring
  unfold stageCost at h0
  nlinarith only [h0,h1,hh,Nat.zero_le ((B+2)^2)]

theorem negativePrepare_valid (coordinate : ℕ) (hc : coordinate∈({333,334,335}:Finset ℕ)) :
    ∀a∈negativePrepare coordinate,a.Valid ids := by
  simp only [Finset.mem_insert,Finset.mem_singleton] at hc
  rcases hc with rfl|rfl|rfl <;> simp [negativePrepare,NatAssign.Instruction.Valid,ids]

theorem negativePrepared_keep (coordinate : ℕ) (n : ℕ→ℕ) (i : ℕ) (hi : i≠341) :
    NatAssign.values (negativePrepare coordinate) n i=n i := by
  simp only [negativePrepare,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.target,Function.update_of_ne hi]

theorem negative_width (coordinate target : ℕ) (hc : coordinate∈({333,334,335}:Finset ℕ))
    (n : ℕ→ℕ) (B : ℕ) (hn : ∀i∈ids,(n i).bits.length≤B) :
    ∀i∈ids,(negative coordinate target n i).bits.length≤8*(B+1) := by
  have hw := nat_values_width ids (negativePrepare coordinate) (negativePrepare_valid coordinate hc)
    n B hn (by simp [negativePrepare,NatAssign.Instruction.literalWidth])
  have w0 : ∀i∈ids,(NatAssign.values (negativePrepare coordinate) n i).bits.length≤8*(B+1) := by
    simpa only [show (negativePrepare coordinate).length=3 by rfl,show 2^3=8 by rfl] using hw
  exact divModValues_width _ ids 341 331 332 target _ (by decide) w0

theorem negative_executes (coordinate target : ℕ)
    (hc : coordinate∈({333,334,335}:Finset ℕ)) (ht : target∈({336,337,338}:Finset ℕ))
    (n : ℕ→ℕ) (B : ℕ) (hn : ∀i∈ids,(n i).bits.length≤B)
    (hz : ∀i∈NaturalQuotient.workPorts,n i=0) (hp : 0 < n 331)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hb : NatAssign.Bank ids n s.val) (hblank : ∀i,i<5 → RationalAccumulator.Blank s.val i) :
    ∃cost t,Executes input tape (negativeCode coordinate target) cost s t ∧ cost≤2^109*(B+2)^2 ∧
      NatAssign.Bank ids (negative coordinate target n) t.val ∧
      (∀i,i<5 → RationalAccumulator.Blank t.val i) ∧ BinaryPrecision.Frame changed s.val t.val := by
  have hl : ∀a∈negativePrepare coordinate,a.literalWidth≤B := by
    simp [negativePrepare,NatAssign.Instruction.literalWidth]
  obtain ⟨c0,s0,e0,h0,b0,z0,f0⟩ := stage_executes (negativePrepare coordinate)
    (negativePrepare_valid coordinate hc) (by simp [negativePrepare]) n B hn hl input tape s hb hblank
  have w0 : ∀i∈ids,(NatAssign.values (negativePrepare coordinate) n i).bits.length≤8*(B+1) := by
    simpa only [show (negativePrepare coordinate).length=3 by rfl,show 2^3=8 by rfl] using
      nat_values_width ids (negativePrepare coordinate) (negativePrepare_valid coordinate hc) n B hn hl
  have zero0 (i : ℕ) (hi : i∈NaturalQuotient.workPorts) : NatAssign.values (negativePrepare coordinate) n i=0 := by
    rw [negativePrepared_keep coordinate n i (by
      simp only [NaturalQuotient.workPorts,Finset.mem_insert,Finset.mem_singleton] at hi;omega),hz i hi]
  have pos0 : 0 < NatAssign.values (negativePrepare coordinate) n 331 := by
    rw [negativePrepared_keep _ _ _ (by decide)];exact hp
  have htt : target∈Finset.Icc 330 344 ∧ 332≠target := by
    simp only [Finset.mem_insert,Finset.mem_singleton] at ht
    simp only [Finset.mem_Icc]
    omega
  obtain ⟨c1,t,e1,h1,b1,z1,f1⟩ := divide_executes 341 331 332 target (by decide) (by decide)
    (by decide) htt.1 htt.2 _ (8*(B+1)) w0 zero0 pos0 input tape s0 b0 z0
  refine ⟨c0+c1,t,e0.seq e1,?_,b1,z1,f0.trans f1⟩
  have hh : (8*(B+1)+2)^2≤64*(B+2)^2 := by
    calc
      _ ≤ (8*(B+2))^2 := Nat.pow_le_pow_left (by omega) _
      _ = _ := by ring
  unfold stageCost at h0
  nlinarith only [h0,h1,hh,Nat.zero_le ((B+2)^2)]

#print axioms head_executes
#print axioms negative_executes
end Maxwell.Continuum.RationalDataflow.RootFrequency
