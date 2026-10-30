import Maxwell.Continuum.PhaseMachineFinalData

/-! The same literal phase program with a complete work-bank
postcondition. No residual temporary word is hidden from later costs. -/
namespace Maxwell.Continuum.PhaseMachine
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalTaylor
set_option maxHeartbeats 3500000
set_option maxRecDepth 8192

def fullStageCost (Q N W : ℕ) : ℕ := 2^60*(fullWorkWidth Q N W+2)^2
def fullCost (Q N W : ℕ) : ℕ :=
  Machin.costBound (Calibration.phaseBits Q N)+2*fullStageCost Q N W+
    300*(2*fullWorkWidth Q N W+4)+RationalTaylor.costBound (order Q N) (fullWorkWidth Q N W)

private theorem full_changes (ins : List NatAssign.Instruction)
    (hv : ∀a∈ins,a.Valid allIds) : NatAssign.changes ins⊆allWorkspace := by
  intro i hi
  rcases Finset.mem_union.mp hi with hz|ht
  · exact Finset.mem_union_left _ hz
  · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ht)
    apply Finset.mem_union_right
    have h := hv a ha
    cases a <;> first | exact h | exact h.2.1

private theorem full_stage_executes (Q N W : ℕ) (ins : List NatAssign.Instruction)
    (hv : ∀a∈ins,a.Valid allIds) (hl : ins.length≤8)
    (hc : ∀a∈ins,a.literalWidth≤fullWorkWidth Q N W)
    (v : ℕ→ℕ) (hw : ∀i∈allIds,(v i).bits.length≤fullWorkWidth Q N W)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : NatAssign.Bank allIds v s.val) (hsc : NatAssign.Scratch s.val) :
    ∃ cost t,Executes input tape (NatAssign.code ins) cost s t ∧ cost≤fullStageCost Q N W ∧
      NatAssign.Bank allIds (NatAssign.values ins v) t.val ∧ NatAssign.Scratch t.val ∧
      BinaryPrecision.Frame allWorkspace s.val t.val := by
  obtain ⟨cost,t,he,hcost,hb,hsc',hf⟩ := NatAssign.executes allIds allIds_ge ins hv v input tape s hs hsc
  have hp := NatAssign.price_bound allIds ins hv v (fullWorkWidth Q N W) hw hc
  have hcoef : 3000*8^ins.length≤(2 : ℕ)^60 := by
    calc
      _ ≤ 3000*8^8 := Nat.mul_le_mul_left 3000 (Nat.pow_le_pow_right (by decide) hl)
      _ ≤ _ := by norm_num
  exact ⟨cost,t,he,hcost.trans (hp.trans (Nat.mul_le_mul_right _ hcoef)),hb,hsc',
    hf.mono (full_changes ins hv)⟩

theorem core_executes_bank (negative : Bool) (base : ℕ→Sign) (a b Q N W : ℕ)
    (ha : a.bits.length≤W) (hb : b.bits.length≤W)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : NatAssign.Bank allIds (initialValues a b) s.val) (hsc : NatAssign.Scratch s.val) :
    ∃ cost t,Executes input tape (core negative base Q N) cost s t ∧ cost≤fullCost Q N W ∧
      NatAssign.Bank allIds (fullFinal negative base a b Q N) t.val ∧ NatAssign.Scratch t.val ∧
      BinaryPrecision.Frame allWorkspace s.val t.val := by
  have hm : NatAssign.Bank Machin.allIds (fun _ => 0) s.val := by
    intro i hi
    have h := hs i (Finset.mem_union_right _ hi)
    have h630 : i≠630 := by
      simp only [Machin.allIds,RationalArctan.ids,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hi
      omega
    have h631 : i≠631 := by
      simp only [Machin.allIds,RationalArctan.ids,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hi
      omega
    simpa only [initialValues,ite_eq_right h630,ite_eq_right h631] using h
  obtain ⟨c0,s0,e0,h0,b0,z0,f0⟩ := Machin.executes_bank (Calibration.phaseBits Q N) input tape s hm hsc
  have seed : NatAssign.Bank allIds (fullSeed a b Q N) s0.val := by
    intro i hi
    by_cases hm : i∈Machin.allIds
    · simpa only [fullSeed,ite_eq_left hm] using b0 i hm
    · have hout : i∉Machin.allWorkspace := by
        have h4 := allIds_ge i hi
        simp only [Machin.allWorkspace,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
        exact not_or_intro (by omega) hm
      simpa only [fullSeed,ite_eq_right hm] using word_of_eq (f0.tapes i hout) (hs i hi)
  have hseed : fullSeedWidth Q N W≤fullWorkWidth Q N W := by unfold fullWorkWidth;omega
  obtain ⟨c1,s1,e1,h1,b1,z1,f1⟩ := full_stage_executes Q N W prepareMagnitude
    (fun x hx => instruction_valid_all (stages_valid.1 x hx)) (by decide)
    (by simp [prepareMagnitude,NatAssign.Instruction.literalWidth]) (fullSeed a b Q N)
    (fun i _ => (fullSeed_width a b Q N W ha hb i).trans hseed) input tape s0 seed z0
  change NatAssign.Bank allIds (fullBefore a b Q N) s1.val at b1
  obtain ⟨c2,s2,e2,h2,b2,z2,f2,_⟩ := RationalMagnitude.executes allIds (by decide) allIds_ge
    (fullBefore a b Q N) (fullBefore_inputs a b Q N).2.2 input tape s1 b1 z1
  have b2' : NatAssign.Bank allIds (fullAfter a b Q N) s2.val := by
    simpa only [(fullBefore_inputs a b Q N).1,(fullBefore_inputs a b Q N).2.1,fullAfter,piMagnitude] using b2
  have hc2 : c2≤300*(2*fullWorkWidth Q N W+4) := by
    have hp := fullBefore_width a b Q N W ha hb 30 (by decide)
    have hn := fullBefore_width a b Q N W ha hb 31 (by decide)
    apply h2.trans
    apply Nat.mul_le_mul_left
    unfold fullWorkWidth
    omega
  obtain ⟨c3,s3,e3,h3,b3,z3,f3⟩ := full_stage_executes Q N W prepareTaylor
    (fun x hx => instruction_valid_all (stages_valid.2 x hx)) (by decide)
    (by
      have ht : (2 : ℕ).bits.length=2 := by decide
      simp [prepareTaylor,NatAssign.Instruction.literalWidth,ht]
      unfold fullWorkWidth
      omega)
    (fullAfter a b Q N)
    (fun i hi => (fullAfter_width a b Q N W ha hb i hi).trans (by unfold fullWorkWidth;omega))
    input tape s2 b2' z2
  change NatAssign.Bank allIds (fullPrepared a b Q N) s3.val at b3
  obtain ⟨c4,t,e4,h4,bt,zt,ft⟩ := RationalTaylor.program_extended allIds (by decide)
    (by
      intro i hi hn
      have h4 := allIds_ge i hi
      simp only [RationalTaylor.workspace,RationalTaylor.ids,Finset.mem_insert,Finset.mem_singleton] at hn ⊢
      omega)
    (fullPrepared a b Q N) (fractionSigns negative base) (order Q N) (fullWorkWidth Q N W)
    (by unfold fullWorkWidth;omega)
    (fun i hi => fullPrepared_width a b Q N W ha hb i (Finset.mem_union_left _
      (Finset.mem_union_left _ (Finset.mem_union_left _ hi)))) input tape s3 b3 z3
  refine ⟨c0+(c1+(c2+(c3+c4))),t,e0.seq (e1.seq (e2.seq (e3.seq e4))),?_,bt,zt,
    (f0.mono (by decide)).trans (f1.trans ((f2.mono (by decide)).trans (f3.trans (ft.mono (by decide)))))⟩
  unfold fullCost
  omega

theorem executes_bank (negative : Bool) (base : ℕ→Sign) (a b Q N W : ℕ)
    (ha : a.bits.length≤W) (hb : b.bits.length≤W)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : NatAssign.Bank allIds (initialValues a b) s.val) (hsc : NatAssign.Scratch s.val)
    (hsg : s.val.registers 200=negative) :
    ∃ cost t,Executes input tape (program base Q N) cost s t ∧ cost≤fullCost Q N W+1 ∧
      NatAssign.Bank allIds (fullFinal negative base a b Q N) t.val ∧ NatAssign.Scratch t.val ∧
      BinaryPrecision.Frame allWorkspace s.val t.val := by
  obtain ⟨cost,t,he,hc,hb,hz,hf⟩ := core_executes_bank negative base a b Q N W ha hb input tape s hs hsc
  refine ⟨1+cost,t,?_,by omega,hb,hz,hf⟩
  cases negative with
  | false => exact Executes.no hsg he
  | true => exact Executes.yes hsg he

#print axioms core_executes_bank
#print axioms executes_bank
end Maxwell.Continuum.PhaseMachine
