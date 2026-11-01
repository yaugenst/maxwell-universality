import Maxwell.Continuum.ParameterOuterAdvance
import Maxwell.Cost.SelectedParameters.LeastLoopResult

/-! A fixed outer loop with executed inner searches and comparisons. The
uniform finite envelope is derived from the visited candidates; the machine
does not receive an iteration count or a successful-test oracle. -/
namespace Maxwell.Continuum.Parameters.OuterMachine
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.SelectedParameters
set_option maxRecDepth 8192
set_option maxHeartbeats 2500000

def loopCode : Code := LeastLoop.code 35 stageCode (NatAssign.code advance)
def loopWidth (D : Data) (hD : D.Positive) (e base ℓ B : ℕ) (hℓ : 0<ℓ) : ℕ :=
  B+∑n∈Finset.range (selectedOuterSteps (D.input hD) e base ℓ hℓ+1),
    stageWidth D hD e (initialExponent base ℓ+n)
def loopTestCost (D : Data) (hD : D.Positive) (e base ℓ W : ℕ) (hℓ : 0<ℓ) : ℕ :=
  ∑n∈Finset.range (selectedOuterSteps (D.input hD) e base ℓ hℓ+1),
    stageCost D hD e (initialExponent base ℓ+n) W
def loopCost (D : Data) (hD : D.Positive) (e base ℓ W : ℕ) (hℓ : 0<ℓ) : ℕ :=
  loopTestCost D hD e base ℓ W hℓ+1+selectedOuterSteps (D.input hD) e base ℓ hℓ*
    (advanceCost W+loopTestCost D hD e base ℓ W hℓ+1)

theorem loopWidth_stage (D : Data) (hD : D.Positive) (e base ℓ B : ℕ) (hℓ : 0<ℓ)
    (n : ℕ) (hn : n ≤ selectedOuterSteps (D.input hD) e base ℓ hℓ) :
    stageWidth D hD e (initialExponent base ℓ+n) ≤ loopWidth D hD e base ℓ B hℓ := by
  have hh := Finset.single_le_sum (fun i (_ : i∈Finset.range (selectedOuterSteps (D.input hD) e base ℓ hℓ+1))=>
    Nat.zero_le (stageWidth D hD e (initialExponent base ℓ+i)))
    (show n∈Finset.range (selectedOuterSteps (D.input hD) e base ℓ hℓ+1) by simp;omega)
  exact hh.trans (Nat.le_add_left _ _)

theorem loop_executes (D : Data) (hD : D.Positive) (e base ℓ B : ℕ) (hℓ : 0<ℓ)
    (hC : D.constant=2^e) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : Ready D (initialExponent base ℓ) B s) :
    let W := loopWidth D hD e base ℓ B hℓ
    let k := selectedOuterExponent (D.input hD) e base ℓ hℓ
    ∃cost t v,Executes input tape loopCode cost s t ∧ cost ≤ loopCost D hD e base ℓ W hℓ ∧
      NatAssign.Bank ids v t.val ∧ (∀i,i<5→RationalAccumulator.Blank t.val i) ∧
      (∀i∈ids,(v i).bits.length ≤ W) ∧ StageOutputs D hD e k v ∧
      BinaryPrecision.Frame workspace s.val t.val := by
  dsimp only
  let W := loopWidth D hD e base ℓ B hℓ
  let R : ℕ→Store→Prop := fun n t=>Ready D (initialExponent base ℓ+n) W t ∧
    BinaryPrecision.Frame workspace s.val t.val
  let Q : ℕ→Store→Prop := fun n t=>∃v,NatAssign.Bank ids v t.val ∧
    (∀i,i<5→RationalAccumulator.Blank t.val i) ∧ (∀i∈ids,(v i).bits.length ≤ W) ∧
    StageOutputs D hD e (initialExponent base ℓ+n) v
  have test : ∀n,n ≤ selectedOuterSteps (D.input hD) e base ℓ hℓ→∀a,R n a→∃cost t,
      Executes input tape stageCode cost a t ∧ cost ≤ loopTestCost D hD e base ℓ W hℓ ∧ R n t ∧ Q n t ∧
      t.val.registers 35=decide (¬OuterTest (D.input hD) e (initialExponent base ℓ+n)) := by
    intro n hn a ha
    obtain ⟨cost,t,v,he,hcost,hb,hsc,hw,ho,hf,frame⟩ := stage_executes D hD e (initialExponent base ℓ+n)
      W hC (loopWidth_stage D hD e base ℓ B hℓ n hn) input tape a ha.1
    have price : stageCost D hD e (initialExponent base ℓ+n) W ≤ loopTestCost D hD e base ℓ W hℓ :=
      Finset.single_le_sum (fun i (_ : i∈Finset.range (selectedOuterSteps (D.input hD) e base ℓ hℓ+1))=>
        Nat.zero_le (stageCost D hD e (initialExponent base ℓ+i) W))
        (show n∈Finset.range (selectedOuterSteps (D.input hD) e base ℓ hℓ+1) by simp;omega)
    exact ⟨cost,t,he,hcost.trans price,⟨⟨v,hb,hsc,hw,ho.core⟩,ha.2.trans frame⟩,⟨v,hb,hsc,hw,ho⟩,hf⟩
  have next : ∀n,n < selectedOuterSteps (D.input hD) e base ℓ hℓ→∀a,R n a→∃cost t,
      Executes input tape (NatAssign.code advance) cost a t ∧ cost ≤ advanceCost W ∧ R (n+1) t := by
    intro n hn a ha
    have hw := loopWidth_stage D hD e base ℓ B hℓ (n+1) (by omega)
    have hp := Nat.two_pow_pos (initialExponent base ℓ+(n+1))
    dsimp only [stageWidth] at hw
    obtain ⟨cost,t,he,hcost,ht,hf⟩ := advance_executes D (initialExponent base ℓ+n) W
      (by rw [Nat.add_assoc];omega) (by rw [Nat.add_assoc];omega) input tape a ha.1
    exact ⟨cost,t,he,hcost,by simpa only [Nat.add_assoc] using And.intro ht (ha.2.trans hf)⟩
  have start : R 0 s := by
    obtain ⟨v,hb,hsc,hw,hc⟩ := hs
    refine ⟨⟨v,hb,hsc,fun i hi=>(hw i hi).trans (Nat.le_add_right _ _),?_⟩,BinaryPrecision.Frame.refl _ _⟩
    simpa only [Nat.add_zero] using hc
  obtain ⟨cost,t,he,hcost,hr,hq⟩ := LeastLoop.executes_result
    (fun n=>OuterTest (D.input hD) e (initialExponent base ℓ+n)) (outerSearch_exists (D.input hD) e base ℓ hℓ)
    35 stageCode (NatAssign.code advance) (loopTestCost D hD e base ℓ W hℓ) (advanceCost W)
    input tape R Q test next s start
  obtain ⟨v,hb,hsc,hw,ho⟩ := hq
  exact ⟨cost,t,v,he,hcost,hb,hsc,hw,ho,hr.2⟩

#print axioms loop_executes
end Maxwell.Continuum.Parameters.OuterMachine
