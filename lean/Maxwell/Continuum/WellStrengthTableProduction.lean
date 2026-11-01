import Maxwell.Continuum.WellOriginalGeometryBridge
import Maxwell.Continuum.WellInternalPass
import Maxwell.Continuum.WellMediatorPass
import Maxwell.Cost.Structured.OutputFootprint

/-! The complete strength producer runs originals, internal vertices, and
mediators in exactly the packed geometry order. Its public execution proof
uses concrete subprograms throughout, with one shared width invariant. -/
namespace Maxwell.Continuum.RationalDataflow.WellStrengthPass
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
open Maxwell.Composition Maxwell.Composition.SourceDecorationEnumeration Maxwell.Logical.Routing
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384

def code : Code := .seq WellOriginalPass.fullCode (.seq WellInternalGeometry.runCode WellMediatorGeometry.runCode)

theorem code_protectsOutput : code.protectsOutput=true := by decide +kernel

def costBound {V J : ℕ} (p : WellOriginalPass.Plan V J) (initialIndex oldLength edges bound : ℕ) : ℕ :=
  12*initialIndex.bits.length+6*oldLength+21*V.bits.length+47+
    (V+1)*(13*V.bits.length+15)+V*WellOriginalPass.stepCost p+
      WellInternalGeometry.runCost p.precision p.budget p.metadataBudget edges bound+
      WellMediatorGeometry.runCost p.precision p.budget p.metadataBudget edges bound

theorem executes {V E J base width initialIndex : ℕ} (saved : SourceEmission.Geometry V E)
    (p : WellOriginalPass.Plan V J) {clock : List Bool} {constants gv : ℕ→ℕ} {s : Store}
    (g : GeometryOutput.Context (packedVector saved) base width p.budget clock constants gv s)
    (hw : 0<width) (hB : width ≤ p.budget) (hlen : clock.length=width)
    (hn : (packedLength saved).bits.length ≤ p.budget)
    (hfit : ∀i,((packedVector saved).get i).bits.length ≤ width)
    (hb : constants 960=base) (hv : constants 961=width) (ho : constants 970=1)
    (hV : constants 963=V) (hE : constants 964=E) (hthree : constants 969=3)
    (bound : ℕ) (htwo : ∀i:Fin E,2 ≤ (saved.paths.get i).length)
    (hbound : ∀i:Fin E,(saved.paths.get i).length ≤ bound)
    (harray : base+packedLength saved*width ≤ p.prefixLimit)
    (hcount : V+pathPrefix saved 2 E+pathPrefix saved 1 E=J) (hJ : J.bits.length ≤ p.metadataBudget)
    (internalNonzero : (p.values 1).value+WellTarget.target .internal p.values ≠ 0)
    (mediatorNonzero : ∀i:Fin E,∀j<(saved.paths.get i).length-1,
      (p.values 1).value+WellMediatorGeometry.target (packedVector saved) (pathOffset saved i.val+1+3*j) p.values ≠ 0)
    (values : ℕ→Parts)
    (originalValues : ∀j,∀hj:j<V,p.part ⟨j,hj⟩=values j)
    (internalValues : ∀i:Fin E,∀j<(saved.paths.get i).length-2,
      values (V+pathPrefix saved 2 i.val+j)=WellInternalEntry.part p.precision p.values)
    (mediatorValues : ∀i:Fin E,∀j<(saved.paths.get i).length-1,
      values (V+pathPrefix saved 2 E+pathPrefix saved 1 i.val+j)=
        WellMediatorGeometry.part p.precision (packedVector saved) (pathOffset saved i.val+1+3*j) p.values)
    (a : PartArray.Table J) (state : WellOriginalPass.State p a initialIndex s.val.memory s)
    (outer inner : List Bool) (hout : BankArray.Word s.val 972 outer) (hin : BankArray.Word s.val 973 inner)
    (hinner : inner.length ≤ p.budget) (input : List Bool) (tape : ℕ→Bool) :
    ∃cost t,∃a':PartArray.Table J,∃gv',Executes input tape code cost s t ∧
      cost ≤ costBound p initialIndex outer.length E bound ∧
      GeometryOutput.Context (packedVector saved) base width p.budget clock constants gv' t ∧
      gv' 971=packedLength saved ∧ State a' p.precision p.values J t ∧
      Configuration a' p.precision p.budget p.metadataBudget p.prefixLimit ∧
      (∀i:Fin J,a'.get i=values i.val) ∧ (∀k,k<p.prefixLimit→t.val.memory k=s.val.memory k) ∧
      Blank t.val 972 ∧ Blank t.val 973 ∧ Word t.val 988 J := by
  obtain ⟨c0,u,a0,e0,hc0,state0,completed0,blank0,keep0⟩ :=
    WellOriginalPass.full_executes p a s.val.memory input tape s state outer hout
  have g0 := state0.geometry g harray keep0
  have done0 : a0.CorrectPrefix values V := completed0.congr (by
    intro k hk
    rw [p.parts_eq k hk]
    exact originalValues k hk)
  have inner0 : BankArray.Word u.val 973 inner := BankArray.word_of_eq
    (keep0 973 (by unfold WellOriginalPass.preserved;omega)) hin
  obtain ⟨c1,z,a1,w1,e1,hc1,g1,_,state1,config1,done1,memory1,inner1,outer1,total1⟩ :=
    WellInternalGeometry.run_executes saved g0 hw hB hlen hn hfit hb hv ho hV hE hthree V bound htwo hbound
      p.values p.canonical p.budget_ge p.power_width p.width p.good p.scale_nonzero internalNonzero a0
      state0.configuration harray (by omega) hJ values done0 internalValues s.val.memory state0.savedPrefix
      state0.strengthState [] inner ((zero_word_iff_blank u.val 972).mpr blank0) inner0 (by simp) hinner input tape
  obtain ⟨c2,t,a2,w2,e2,hc2,g2,ix2,state2,config2,done2,memory2,inner2,outer2,total2⟩ :=
    WellMediatorGeometry.run_executes saved g1 hw hB hlen hn hfit hb hv ho hV hE hthree
      (V+pathPrefix saved 2 E) bound htwo hbound p.values p.canonical p.budget_ge p.power_width p.width p.good
      p.scale_nonzero mediatorNonzero a1 config1 harray (by omega) hJ values done1 mediatorValues s.val.memory memory1
      state1 [] [] ((zero_word_iff_blank z.val 972).mpr outer1) ((zero_word_iff_blank z.val 973).mpr inner1)
      (by simp) (by simp) input tape
  rw [hcount] at state2 done2
  refine ⟨c0+(c1+c2),t,a2,w2,e0.seq (e1.seq e2),by unfold costBound;omega,g2,ix2,state2,config2,
    fun i=>done2 i i.isLt,memory2,outer2,inner2,?_⟩
  exact word_of_eq (total2.trans (total1.trans
    (keep0 988 (by unfold WellOriginalPass.preserved;omega)))) state.totalCount

#print axioms executes
end Maxwell.Continuum.RationalDataflow.WellStrengthPass
