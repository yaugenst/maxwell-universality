import Maxwell.Continuum.ParameterOuterTestStage

/-! Canonical finite operand widths for one executed outer stage. These
are explicit arithmetic data; polynomial estimates can be proved separately. -/
namespace Maxwell.Continuum.Parameters.OuterMachine
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.SelectedParameters
set_option maxRecDepth 8192
set_option maxHeartbeats 2500000

def baseWidth (D : Data) (hD : D.Positive) (e k : ℕ) : ℕ :=
  25+D.constant.bits.length+D.sourceSize.bits.length+D.wells.bits.length+
    D.conditionNum.bits.length+D.conditionDen.bits.length+D.epsilonNum.bits.length+D.epsilonDen.bits.length+
    (D.span 0).bits.length+(D.span 1).bits.length+(D.span 2).bits.length+
    (stageLength k).bits.length+(stageSpacing (D.input hD) e k).bits.length+
    (3^(stageSpacing (D.input hD) e k)).bits.length

structure OperandBound (D : Data) (hD : D.Positive) (e k B : ℕ) : Prop where
  literal : 25 ≤ B
  spacing : (D.spacing k).Width B
  sourceSize : D.sourceSize.bits.length ≤ B
  wells : D.wells.bits.length ≤ B
  span : ∀j,(D.span j).bits.length ≤ B
  spacingValue : (stageSpacing (D.input hD) e k).bits.length ≤ B
  zeta : (3^(stageSpacing (D.input hD) e k)).bits.length ≤ B

theorem baseWidth_spec (D : Data) (hD : D.Positive) (e k : ℕ) :
    OperandBound D hD e k (baseWidth D hD e k) := by
  constructor
  · unfold baseWidth;omega
  · constructor <;> dsimp only [Data.spacing] <;> unfold baseWidth <;> omega
  · unfold baseWidth;omega
  · unfold baseWidth;omega
  · have h0 : (D.span 0).bits.length ≤ baseWidth D hD e k := by unfold baseWidth;omega
    have h1 : (D.span 1).bits.length ≤ baseWidth D hD e k := by unfold baseWidth;omega
    have h2 : (D.span 2).bits.length ≤ baseWidth D hD e k := by unfold baseWidth;omega
    intro j;fin_cases j
    · exact h0
    · exact h1
    · exact h2
  · unfold baseWidth;omega
  · unfold baseWidth;omega

def bufferWidth (D : Data) (hD : D.Positive) (e k : ℕ) : ℕ :=
  baseWidth D hD e k+((stageLength k)^2).bits.length+
    (2^1026*8^(stageSpacing (D.input hD) e k)).bits.length+(D.detuningDen hD e k).bits.length+
    (stageSpan (D.input hD) e k 0).bits.length+(stageSpan (D.input hD) e k 1).bits.length+
    (stageSpan (D.input hD) e k 2).bits.length

theorem bufferWidth_spec (D : Data) (hD : D.Positive) (e k : ℕ) :
    (D.buffer hD e k).Width (bufferWidth D hD e k) := by
  have hb := baseWidth_spec D hD e k
  have le : baseWidth D hD e k ≤ bufferWidth D hD e k := by unfold bufferWidth;omega
  constructor
  · exact hb.spacing.constant.trans le
  · exact hb.spacing.length.trans le
  · exact hb.wells.trans le
  · exact hb.sourceSize.trans le
  · exact hb.spacing.conditionNum.trans le
  · exact hb.spacing.conditionDen.trans le
  · exact hb.spacing.epsilonNum.trans le
  · exact hb.spacing.epsilonDen.trans le
  · dsimp only [Data.buffer];unfold bufferWidth;omega
  · dsimp only [Data.buffer];unfold bufferWidth;omega
  · dsimp only [Data.buffer]
    have hone : (1:ℕ).bits.length=1 := rfl
    rw [hone]
    have := hb.literal;omega
  · dsimp only [Data.buffer];unfold bufferWidth;omega
  · have h0 : (stageSpan (D.input hD) e k 0).bits.length ≤ bufferWidth D hD e k := by unfold bufferWidth;omega
    have h1 : (stageSpan (D.input hD) e k 1).bits.length ≤ bufferWidth D hD e k := by unfold bufferWidth;omega
    have h2 : (stageSpan (D.input hD) e k 2).bits.length ≤ bufferWidth D hD e k := by unfold bufferWidth;omega
    intro j;fin_cases j
    · exact h0
    · exact h1
    · exact h2

theorem OperandBound.spanSources {D : Data} {hD : D.Positive} {e k B : ℕ}
    (h : OperandBound D hD e k B) (v : ℕ→ℕ) (hc : Core D k v) (ho : SpacingOutputs D hD e k v) :
    ∀i∈spanSources,(v i).bits.length ≤ B := by
  have hs (j : Fin 3) : v (2217+j.val)=D.span j := congrArg (fun A:Data=>A.span j) hc.data
  intro i hi
  simp only [OuterMachine.spanSources,Finset.mem_insert,Finset.mem_singleton] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · simpa only [show v 2217=D.span 0 from hs 0] using h.span 0
  · simpa only [show v 2218=D.span 1 from hs 1] using h.span 1
  · simpa only [show v 2219=D.span 2 from hs 2] using h.span 2
  · simpa only [hc.length,Data.spacing] using h.spacing.length
  · simpa only [ho.spacing] using h.spacingValue
  · rw [hc.two];change 2 ≤ B;have := h.literal;omega
  · rw [hc.four];change 3 ≤ B;have := h.literal;omega

theorem OperandBound.tailSources {D : Data} {hD : D.Positive} {e k B : ℕ}
    (h : OperandBound D hD e k B) (v : ℕ→ℕ) (hc : Core D k v) (ho : SpacingOutputs D hD e k v) :
    ∀i∈tailSources,(v i).bits.length ≤ B := by
  have hC : v 2210=D.constant := congrArg Data.constant hc.data
  have hJ : v 2212=D.wells := congrArg Data.wells hc.data
  intro i hi
  simp only [OuterMachine.tailSources,Finset.mem_insert,Finset.mem_singleton] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl
  · simpa only [hC,Data.spacing] using h.spacing.constant
  · simpa only [hJ] using h.wells
  · simpa only [hc.length,Data.spacing] using h.spacing.length
  · rw [hc.four];change 3 ≤ B;have := h.literal;omega
  · simpa only [ho.zetaDen] using h.zeta

def stageWidth (D : Data) (hD : D.Positive) (e k : ℕ) : ℕ :=
  let B := baseWidth D hD e k
  SpacingMachine.width (spacingSteps D hD e k) B+tauInputWidth B+
    OuterTau.width (tauSteps D hD e k) (tauInputWidth B)+spanInputWidth B+
    BufferMachine.width (bufferSteps D hD e k) (bufferWidth D hD e k)+tailInputWidth B+
    2^k+stageLength k+2

#print axioms bufferWidth_spec
end Maxwell.Continuum.Parameters.OuterMachine
