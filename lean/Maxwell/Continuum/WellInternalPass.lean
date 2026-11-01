import Maxwell.Continuum.WellInternalPaths
import Maxwell.Continuum.WellStrengthPathPrepare

/-! This complete path pass obtains its cursor and counter from the
runtime metadata, executes every path, and clears the outer counter. -/
namespace Maxwell.Continuum.RationalDataflow.WellInternalGeometry
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
open Maxwell.Composition Maxwell.Composition.SourceDecorationEnumeration Maxwell.Logical.Routing
open WellStrengthPass
set_option maxHeartbeats 7000000
set_option maxRecDepth 16384

def runCode : Code := .seq prepareCode (.seq pathsCode (.call (TapeOps.clear 972)))

def runCost (P B M edges bound : ℕ) : ℕ :=
  2^23*(B+3)^2+27*B+32+(edges+1)*(13*B+15)+edges*pathCost P B M bound+6*B+4

theorem run_executes {V E base width B P M J boundary : ℕ} (saved : SourceEmission.Geometry V E)
    {clock : List Bool} {constants gv : ℕ→ℕ} {s : Store}
    (g : GeometryOutput.Context (packedVector saved) base width B clock constants gv s)
    (hw : 0<width) (hB : width ≤ B) (hlen : clock.length=width) (hn : (packedLength saved).bits.length ≤ B)
    (hfit : ∀i,((packedVector saved).get i).bits.length ≤ width)
    (hb : constants 960=base) (hv : constants 961=width) (ho : constants 970=1)
    (hV : constants 963=V) (hE : constants 964=E) (hthree : constants 969=3)
    (first bound : ℕ)
    (htwo : ∀i:Fin E,2 ≤ (saved.paths.get i).length) (hbound : ∀i:Fin E,(saved.paths.get i).length ≤ bound)
    (v : ℕ→Parts) (canonical : WellStrengthReset.canonical v=v)
    (hW : 4 ≤ B) (hP : (2^P).bits.length ≤ B) (rvwidth : WidthBank WellStrength.bank B v)
    (good : Good WellStrength.bank v) (scale : (v 4).value ≠ 0)
    (denominator : (v 1).value+WellTarget.target .internal v ≠ 0)
    (a : PartArray.Table J) (config : Configuration a P B M boundary)
    (harray : base+packedLength saved*width ≤ boundary)
    (hcapacity : first+pathPrefix saved 2 E ≤ J) (hJ : J.bits.length ≤ M)
    (values : ℕ→Parts) (completed : a.CorrectPrefix values first)
    (agrees : ∀i:Fin E,∀j<(saved.paths.get i).length-2,
      values (first+pathPrefix saved 2 i.val+j)=WellInternalEntry.part P v)
    (memory : ℕ→Bool) (preserved : ∀k,k<boundary→s.val.memory k=memory k)
    (state : State a P v first s)
    (outer inner : List Bool) (hout : BankArray.Word s.val 972 outer) (hin : BankArray.Word s.val 973 inner)
    (houter : outer.length ≤ B) (hinner : inner.length ≤ B) (input : List Bool) (tape : ℕ→Bool) :
    ∃cost t,∃a':PartArray.Table J,∃gv',Executes input tape runCode cost s t ∧
      cost ≤ runCost P B M E bound ∧
      GeometryOutput.Context (packedVector saved) base width B clock constants gv' t ∧ gv' 971=packedLength saved ∧
      State a' P v (first+pathPrefix saved 2 E) t ∧ Configuration a' P B M boundary ∧
      a'.CorrectPrefix values (first+pathPrefix saved 2 E) ∧
      (∀k,k<boundary→t.val.memory k=memory k) ∧ Blank t.val 973 ∧
      Blank t.val 972 ∧
      t.val.tapes 988=s.val.tapes 988 := by
  obtain ⟨c0,u,e0,hc0,g0,state0,counter0,inner0,memory0,keep0⟩ :=
    prepare_executes g V E hV hE hthree (originals_span saved) hn state outer inner hout hin houter hinner input tape
  obtain ⟨origin,word0⟩ := counter0
  obtain ⟨c1,z,b,w,lastWord,e1,hc1,g1,ix1,state1,cf1,done1,mem1,blank1,word1,len1,keep1⟩ :=
    paths_executes saved g0 hw hB hlen hn hfit hb hv ho first bound (by simp) htwo hbound
      v canonical hW hP rvwidth good scale denominator a config harray hcapacity hJ values completed agrees
      memory (by intro k hk;rw [memory0];exact preserved k hk) state0 inner0 input tape E.bits origin
      (addressValue_bits E) word0
  obtain ⟨t,e2,g2,state2,blank2,f2⟩ := clearOuter_executes g1 state1 lastWord origin word1 input tape
  have eWidth : E.bits.length ≤ B := by
    have hh := g.wordWidth 964 (by decide)
    rwa [g.fixed 964 (by decide),hE] at hh
  refine ⟨c0+(c1+(6*lastWord.length+4)),t,b,w,e0.seq (e1.seq e2),?_,g2,ix1,state2,cf1,done1,?_,
    blank_of_eq (f2.tapes 973 (by decide)) blank1,blank2,(f2.tapes 988 (by decide)).trans (keep1.trans keep0)⟩
  · rw [len1]
    have cap := hc1.trans (Nat.add_le_add_right
      (Nat.mul_le_mul_left (E+1) (show 13*E.bits.length+15 ≤ 13*B+15 by omega)) _)
    unfold runCost
    omega
  · intro k hk;rw [f2.memory];exact mem1 k hk

#print axioms run_executes
end Maxwell.Continuum.RationalDataflow.WellInternalGeometry
