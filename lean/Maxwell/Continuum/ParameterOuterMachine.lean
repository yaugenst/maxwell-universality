import Maxwell.Continuum.ParameterOuterInitialize

/-! Source operands to the actual first-success outer parameters. The code
is fixed: stored input words control all searches and iteration counts. -/
namespace Maxwell.Continuum.Parameters.OuterMachine
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.SelectedParameters
set_option maxRecDepth 8192
set_option maxHeartbeats 2500000

def code : Code := .seq initializeCode loopCode

def resultWidth (v : ℕ→ℕ) (hD : (dataOf v).Positive) (e B : ℕ) (hℓ : 0<v 2200) : ℕ :=
  loopWidth (dataOf v) hD e (v 2201) (v 2200) (initialWidth v B) hℓ

def costBound (v : ℕ→ℕ) (hD : (dataOf v).Positive) (e B : ℕ) (hℓ : 0<v 2200) : ℕ :=
  initializeCost v B+loopCost (dataOf v) hD e (v 2201) (v 2200) (resultWidth v hD e B hℓ) hℓ

theorem executes (v : ℕ→ℕ) (hD : (dataOf v).Positive) (e B : ℕ) (hℓ : 0<v 2200)
    (hC : v 2210=2^e) (hw : ∀i∈ids,(v i).bits.length ≤ B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hb : NatAssign.Bank ids v s.val) (hs : ∀i,i<5→RationalAccumulator.Blank s.val i) :
    let k := selectedOuterExponent ((dataOf v).input hD) e (v 2201) (v 2200) hℓ
    ∃cost t w,Executes input tape code cost s t ∧ cost ≤ costBound v hD e B hℓ ∧
      NatAssign.Bank ids w t.val ∧ (∀i,i<5→RationalAccumulator.Blank t.val i) ∧
      (∀i∈ids,(w i).bits.length ≤ resultWidth v hD e B hℓ) ∧
      StageOutputs (dataOf v) hD e k w ∧ BinaryPrecision.Frame workspace s.val t.val ∧
      RationalAccumulator.Word t.val 2200 (v 2200) := by
  dsimp only
  obtain ⟨ci,a,ei,pi,ha,fi,log⟩ := initialize_executes v B hℓ hw input tape s hb hs
  obtain ⟨cl,t,w,el,pl,bt,st,wt,ht,ft⟩ := loop_executes (dataOf v) hD e (v 2201) (v 2200)
    (initialWidth v B) hℓ hC input tape a ha
  exact ⟨ci+cl,t,w,ei.seq el,Nat.add_le_add pi pl,bt,st,wt,ht,fi.trans ft,
    RationalAccumulator.word_of_eq (el.protectsTape 2200 loop_protects_log) log⟩

#print axioms executes
end Maxwell.Continuum.Parameters.OuterMachine
