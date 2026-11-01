import Maxwell.Continuum.ParameterOuterSpacingStage
import Maxwell.Cost.Structured.NatAssign.Dependencies

/-! The executed detuning computation resets only its local arithmetic bank.
Its uniform width depends on the current length and spacing, not stale words
left by earlier outer candidates. -/
namespace Maxwell.Continuum.Parameters.OuterMachine
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.SelectedParameters
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

def tauSources : Finset ℕ := {2221,2228}
def tauInputWidth (B : ℕ) : ℕ := 2^prepareTau.length*(B+1)
def tauSteps (D : Data) (hD : D.Positive) (e k : ℕ) : ℕ :=
  Nat.clog 2 (OuterTau.budgetDen (stageLength k) (stageSpacing (D.input hD) e k))
def tauStageCode : Code := .seq (NatAssign.code prepareTau) OuterTau.code
def tauStageCost (D : Data) (hD : D.Positive) (e k W B : ℕ) : ℕ :=
  3000*8^prepareTau.length*(W+2)^2+OuterTau.costBound (tauSteps D hD e k) (tauInputWidth B)

structure TauOutputs (D : Data) (hD : D.Positive) (e k : ℕ) (v : ℕ→ℕ) : Prop where
  numerator : v 2234=1
  denominator : v 2237=D.detuningDen hD e k

theorem prepareTau_dependencies : ∀a∈prepareTau,NatAssign.dependencies prepareTau a.target⊆tauSources := by
  decide +kernel

theorem tau_inputs_dependencies : ∀i∈OuterTau.ids,NatAssign.dependencies prepareTau i⊆tauSources := by
  decide +kernel

theorem tauStage (D : Data) (hD : D.Positive) (e k W B : ℕ)
    (h25 : 25 ≤ B) (hlw : (stageLength k).bits.length ≤ B)
    (hzw : (3^(stageSpacing (D.input hD) e k)).bits.length ≤ B)
    (hprep : tauInputWidth B ≤ W) (htw : OuterTau.width (tauSteps D hD e k) (tauInputWidth B) ≤ W)
    (v : ℕ→ℕ) (hc : Core D k v) (ho : SpacingOutputs D hD e k v)
    (hw : ∀i∈ids,(v i).bits.length ≤ W)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hb : NatAssign.Bank ids v s.val) (hs : ∀i,i<5→RationalAccumulator.Blank s.val i) :
    ∃cost t w,Executes input tape tauStageCode cost s t ∧
      cost ≤ tauStageCost D hD e k W B ∧ NatAssign.Bank ids w t.val ∧
      (∀i,i<5→RationalAccumulator.Blank t.val i) ∧ (∀i∈ids,(w i).bits.length ≤ W) ∧
      Core D k w ∧ SpacingOutputs D hD e k w ∧ TauOutputs D hD e k w ∧
      BinaryPrecision.Frame workspace s.val t.val := by
  have hsrc : ∀i∈tauSources,(v i).bits.length ≤ B := by
    intro i hi
    simp only [tauSources,Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl|rfl
    · simpa only [hc.length] using hlw
    · simpa only [ho.zetaDen] using hzw
  have hlit : ∀a∈prepareTau,a.literalWidth ≤ B := by
    have hn : (16777216:ℕ).bits.length=25 := by decide
    simp [prepareTau,NatAssign.Instruction.literalWidth,GeometricAdapter.clearGeo,Rational.clear,hn]
    omega
  obtain ⟨cp,p,ep,pp,bp,sp,fp⟩ := NatAssign.executes_scratch 5 (by decide) ids
    (fun i hi=>by have := ids_ge i hi;omega) prepareTau prepareTau_valid v input tape s hb hs
  let vp := NatAssign.values prepareTau v
  have wp : ∀i∈ids,(vp i).bits.length ≤ W := NatAssign.values_local_width ids tauSources prepareTau
    prepareTau_valid v W B hw hsrc hlit prepareTau_dependencies hprep
  have wpt : ∀i∈OuterTau.ids,(vp i).bits.length ≤ tauInputWidth B := by
    intro i hi
    exact NatAssign.values_dependencies_width ids tauSources prepareTau prepareTau_valid v B hsrc hlit i
      ((show OuterTau.ids⊆ids by decide +kernel) hi) (tau_inputs_dependencies i hi)
  obtain ⟨pden,pone,pzero,pcounter,pgeo⟩ := prepareTau_fields v
  have pden' : vp 2233=OuterTau.budgetDen (stageLength k) (stageSpacing (D.input hD) e k) := by
    simpa only [hc.length,ho.zetaDen,OuterTau.budgetDen,pow_mul] using pden
  obtain ⟨ct,t,et,pt,bt,st,wt,_,_,ft⟩ := tau vp (stageLength k) (stageSpacing (D.input hD) e k)
    W (tauInputWidth B) (stageLength_pos k) pden' pone pcounter pzero pgeo wp wpt input tape p bp sp
  let w := NatAssign.overlay OuterTau.ids (OuterTau.result vp (tauSteps D hD e k)) vp
  have outside : ∀i∈retained∪{2227,2228,2229,2243},w i=v i := by
    intro i hi
    have hnot : i∉OuterTau.ids := by
      have dis : Disjoint (retained∪{2227,2228,2229,2243}) OuterTau.ids := by decide +kernel
      exact Finset.disjoint_left.mp dis hi
    rw [show w i=vp i from NatAssign.overlay_outside _ _ _ hnot]
    apply NatAssign.values_preserves
    simp only [retained,Finset.mem_union,Finset.mem_Icc,Finset.mem_insert,Finset.mem_singleton] at hi
    simp [prepareTau,NatAssign.Instruction.target,GeometricAdapter.clearGeo,Rational.clear]
    omega
  have wc : Core D k w := hc.congr (fun i hi=>outside i (Finset.mem_union_left _ hi))
  have wo : SpacingOutputs D hD e k w := ⟨
    (outside 2227 (by decide +kernel)).trans ho.spacing,
    (outside 2228 (by decide +kernel)).trans ho.zetaDen,
    (outside 2229 (by decide +kernel)).trans ho.alphaNum,
    (outside 2243 (by decide +kernel)).trans ho.alphaDen⟩
  have dto : TauOutputs D hD e k w := by
    constructor
    · change NatAssign.overlay OuterTau.ids (OuterTau.result vp _) vp 2234=1
      simpa [NatAssign.overlay,OuterTau.result,OuterTau.searched,Rational.after,Rational.common,
        show 2234∈OuterTau.ids by decide +kernel] using pone
    · simp [w,NatAssign.overlay,OuterTau.result,Data.detuningDen,tauSteps,
        show 2237∈OuterTau.ids by decide +kernel]
  have ppb := NatAssign.price_bound ids prepareTau prepareTau_valid v W hw
    (fun a ha=>(hlit a ha).trans (by
      have : B+1 ≤ tauInputWidth B := by unfold tauInputWidth;exact Nat.le_mul_of_pos_left _ (by positivity)
      omega))
  exact ⟨cp+ct,t,w,ep.seq et,Nat.add_le_add (pp.trans ppb) pt,bt,st,
    by change ∀i∈ids,(w i).bits.length ≤ max W (OuterTau.width (tauSteps D hD e k) (tauInputWidth B)) at wt
       simpa only [max_eq_left htw] using wt,wc,wo,dto,(fp.mono (by decide +kernel)).trans ft⟩

#print axioms tauStage
end Maxwell.Continuum.Parameters.OuterMachine
