import Maxwell.Continuum.ParameterOuterStageBounds

namespace Maxwell.Continuum.Parameters.OuterMachine
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.SelectedParameters
set_option maxRecDepth 8192
set_option maxHeartbeats 2500000

def stageCode : Code := .seq spacingCode (.seq tauStageCode (.seq bufferStageCode stoppingCode))
def stageCost (D : Data) (hD : D.Positive) (e k W : ℕ) : ℕ :=
  spacingCost D hD e k W (baseWidth D hD e k)+
    (tauStageCost D hD e k W (baseWidth D hD e k)+
      (bufferStageCost D hD e k W (bufferWidth D hD e k)+stoppingCost W))

theorem stage_executes (D : Data) (hD : D.Positive) (e k W : ℕ) (hC : D.constant=2^e)
    (hW : stageWidth D hD e k ≤ W) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : Ready D k W s) :
    ∃cost t v,Executes input tape stageCode cost s t ∧ cost ≤ stageCost D hD e k W ∧
      NatAssign.Bank ids v t.val ∧ (∀i,i<5→RationalAccumulator.Blank t.val i) ∧
      (∀i∈ids,(v i).bits.length ≤ W) ∧ StageOutputs D hD e k v ∧
      t.val.registers 35=decide (¬OuterTest (D.input hD) e k) ∧
      BinaryPrecision.Frame workspace s.val t.val := by
  have hp : 0<(2:ℕ)^k := Nat.two_pow_pos k
  have hb := baseWidth_spec D hD e k
  have hsW : SpacingMachine.width (spacingSteps D hD e k) (baseWidth D hD e k) ≤ W := by
    dsimp only [stageWidth] at hW;omega
  obtain ⟨c1,a,v1,e1,p1,b1,s1,w1,h1,o1,f1⟩ := spacingStage D hD e k W (baseWidth D hD e k)
    hC hb.spacing hsW input tape s hs
  obtain ⟨c2,b,v2,e2,p2,b2,s2,w2,h2,o2,t2,f2⟩ := tauStage D hD e k W (baseWidth D hD e k)
    hb.literal hb.spacing.length hb.zeta (by dsimp only [stageWidth] at hW;omega)
    (by dsimp only [stageWidth] at hW;omega) v1 h1 o1 w1 input tape a b1 s1
  obtain ⟨c3,c,v3,e3,p3,b3,s3,w3,h3,o3,t3,q3,f3⟩ := bufferStage D hD e k W (bufferWidth D hD e k)
    (baseWidth D hD e k) hC v2 h2 o2 t2 w2 (hb.spanSources v2 h2 o2)
    (by dsimp only [stageWidth] at hW;omega) (bufferWidth_spec D hD e k)
    (by dsimp only [stageWidth] at hW;omega) input tape b b2 s2
  obtain ⟨c4,t,v4,e4,p4,b4,s4,w4,h4,g4,f4⟩ := stoppingStage D hD e k W (baseWidth D hD e k)
    hC v3 ⟨h3,o3,t3,q3⟩ w3 (by dsimp only [stageWidth] at hW;omega) (by dsimp only [stageWidth] at hW;omega)
    (hb.tailSources v3 h3 o3) (by dsimp only [stageWidth] at hW;omega) input tape c b3 s3
  exact ⟨c1+(c2+(c3+c4)),t,v4,e1.seq (e2.seq (e3.seq e4)),
    Nat.add_le_add p1 (Nat.add_le_add p2 (Nat.add_le_add p3 p4)),b4,s4,w4,h4,g4,
    f1.trans (f2.trans (f3.trans f4))⟩

#print axioms stage_executes
end Maxwell.Continuum.Parameters.OuterMachine
