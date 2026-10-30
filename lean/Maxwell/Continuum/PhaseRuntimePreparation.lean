import Maxwell.Continuum.PhaseMachineFinalBank

/-! Fixed stored-word preparation from the actual Machin result to the
Taylor numerator and denominator, retaining the complete phase bank. -/
namespace Maxwell.Continuum.PhaseMachine.Runtime
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalTaylor
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

def preparation : Code := .seq (NatAssign.code prepareMagnitude)
  (.seq RationalMagnitude.program (NatAssign.code prepareTaylor))
def preparationCost (Q N W : ℕ) : ℕ := 2*fullStageCost Q N W+300*(2*fullWorkWidth Q N W+4)

private theorem stage (Q N W : ℕ) (ins : List NatAssign.Instruction)
    (hv : ∀a∈ins,a.Valid allIds) (hl : ins.length≤8)
    (hc : ∀a∈ins,a.literalWidth≤fullWorkWidth Q N W)
    (v : ℕ→ℕ) (hw : ∀i∈allIds,(v i).bits.length≤fullWorkWidth Q N W)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : NatAssign.Bank allIds v s.val) (hz : NatAssign.Scratch s.val) :
    ∃cost t,Executes input tape (NatAssign.code ins) cost s t ∧ cost≤fullStageCost Q N W ∧
      NatAssign.Bank allIds (NatAssign.values ins v) t.val ∧ NatAssign.Scratch t.val ∧
      BinaryPrecision.Frame allWorkspace s.val t.val := by
  obtain ⟨c,t,e,hc0,bt,zt,ft⟩ := NatAssign.executes allIds allIds_ge ins hv v input tape s hs hz
  have hp := NatAssign.price_bound allIds ins hv v (fullWorkWidth Q N W) hw hc
  have hcoef : 3000*8^ins.length≤(2:ℕ)^60 := by
    calc
      _≤3000*8^8 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) hl)
      _≤_ := by norm_num
  have hsub : NatAssign.changes ins⊆allWorkspace := by
    intro i hi
    rcases Finset.mem_union.mp hi with hz|ht
    · exact Finset.mem_union_left _ hz
    · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ht)
      apply Finset.mem_union_right
      have h := hv a ha
      cases a <;> first | exact h | exact h.2.1
  exact ⟨c,t,e,hc0.trans (hp.trans (Nat.mul_le_mul_right _ hcoef)),bt,zt,ft.mono hsub⟩

theorem preparation_executes (a b Q N W : ℕ) (ha : a.bits.length≤W) (hb : b.bits.length≤W)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : NatAssign.Bank allIds (fullSeed a b Q N) s.val) (hz : NatAssign.Scratch s.val) :
    ∃cost t,Executes input tape preparation cost s t ∧ cost≤preparationCost Q N W ∧
      NatAssign.Bank allIds (fullPrepared a b Q N) t.val ∧ NatAssign.Scratch t.val ∧
      BinaryPrecision.Frame allWorkspace s.val t.val := by
  have hseed : fullSeedWidth Q N W≤fullWorkWidth Q N W := by unfold fullWorkWidth;omega
  obtain ⟨c1,s1,e1,h1,b1,z1,f1⟩ := stage Q N W prepareMagnitude
    (fun x hx => instruction_valid_all (stages_valid.1 x hx)) (by decide)
    (by simp [prepareMagnitude,NatAssign.Instruction.literalWidth]) (fullSeed a b Q N)
    (fun i _ => (fullSeed_width a b Q N W ha hb i).trans hseed) input tape s hs hz
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
  obtain ⟨c3,t,e3,h3,bt,zt,ft⟩ := stage Q N W prepareTaylor
    (fun x hx => instruction_valid_all (stages_valid.2 x hx)) (by decide)
    (by
      have ht : (2:ℕ).bits.length=2 := by decide
      simp [prepareTaylor,NatAssign.Instruction.literalWidth,ht]
      unfold fullWorkWidth
      omega)
    (fullAfter a b Q N)
    (fun i hi => (fullAfter_width a b Q N W ha hb i hi).trans (by unfold fullWorkWidth;omega))
    input tape s2 b2' z2
  exact ⟨c1+(c2+c3),t,e1.seq (e2.seq e3),by unfold preparationCost;omega,bt,zt,
    f1.trans ((f2.mono (by decide)).trans ft)⟩

#print axioms preparation_executes
end Maxwell.Continuum.PhaseMachine.Runtime
