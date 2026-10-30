import Maxwell.Continuum.RationalArctanRuntimeStep

/-! The alternating arctangent sign is a runtime Boolean state. -/
namespace Maxwell.Continuum.RationalArctan.Runtime
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalTaylor
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

def cycleSign (n : ℕ) : Bool := decide (n%2=0)
def cycleSelect : Code := .branch 240 (NatAssign.code (step .plus)) (NatAssign.code (step .minus))
def cycleStep : Code := .seq cycleSelect (Code.atom (.bitNot 240 240))

theorem cycleSign_succ (n : ℕ) : cycleSign (n+1)= !cycleSign n := by
  have h : n%2<2 := Nat.mod_lt _ (by decide)
  have he : (n+1)%2=(n%2+1)%2 := by omega
  interval_cases hm : n%2 <;> simp [cycleSign,he,hm]

structure CycleReady (a b n : ℕ) (s : Store) : Prop where
  data : Ready a b n s
  sign : s.val.registers 240=cycleSign n

theorem cycleStep_executes (a b n N W : ℕ) (hn : n<N) (ha : a.bits.length≤W) (hb : b.bits.length≤W)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : CycleReady a b n s) :
    ∃cost t,Executes input tape cycleStep cost s t ∧
      cost≤2^64*(RationalArctan.width N W+2)^2+3 ∧ CycleReady a b (n+1) t ∧
      BinaryPrecision.Frame workspace s.val t.val := by
  obtain ⟨cost,u,he,hc,hu,hf⟩ := step_executes a b n N W hn ha hb input tape s hs.data
  have hp := he.protectsRegister 240 (by cases negativeSigns n <;> rfl)
  have select : Executes input tape cycleSelect (1+cost) s u := by
    by_cases hn0 : n%2=0
    · have hsg : s.val.registers 240=true := by simpa [cycleSign,hn0] using hs.sign
      simpa only [cycleSelect,negativeSigns,ite_eq_left hn0] using Executes.yes (no:=NatAssign.code (step .minus)) hsg he
    · have hsg : s.val.registers 240=false := by simpa [cycleSign,hn0] using hs.sign
      simpa only [cycleSelect,negativeSigns,ite_eq_right hn0] using Executes.no (yes:=NatAssign.code (step .plus)) hsg he
  let t := Store.ofState (u.val.setRegister 240 (!u.val.registers 240))
  have advance : Executes input tape (Code.atom (.bitNot 240 240)) 2 u t := Executes.bitNot input tape u 240 240
  refine ⟨(1+cost)+2,t,select.seq advance,by omega,⟨⟨hu.bank,hu.scratch⟩,?_⟩,?_⟩
  · simp only [t,Store.ofState,BitRAMState.setRegister,Function.update_self]
    rw [hp,hs.sign,cycleSign_succ]
  · exact hf.trans ⟨rfl,rfl,rfl,rfl,rfl,fun _ _ => rfl⟩

theorem CycleReady.count_frame (a b n countTape : ℕ) (hc : countTape∉ids) (hc4 : 4≤countTape)
    {s t : Store} (hs : CycleReady a b n s) (hf : CountedShifted.Frame countTape s t) :
    CycleReady a b n t := by
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro i hi
    exact word_of_eq (hf.2.2.2.2.2.1 i (by intro he;subst i;exact hc hi)) (hs.data.bank i hi)
  · intro i hi
    exact blank_of_eq (hf.2.2.2.2.2.1 i (by omega)) (hs.data.scratch i hi)
  · exact (hf.2.2.2.2.2.2 240 (by decide) (by decide) (by decide) (by decide)).trans hs.sign

#print axioms cycleStep_executes
end Maxwell.Continuum.RationalArctan.Runtime
