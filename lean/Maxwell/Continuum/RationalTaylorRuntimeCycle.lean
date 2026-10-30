import Maxwell.Continuum.RationalTaylorRuntimeStep

/-! Four fixed branches implement the sign cycles of exponential,
alternating exponential, sine, and cosine. The cycle position lives in two
Boolean registers; the term count and factorial index remain runtime words. -/
namespace Maxwell.Continuum.RationalTaylor.Runtime
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

abbrev Cycle := Fin 4→Sign
abbrev cycleSigns (cycle : Cycle) (n : ℕ) : Sign := cycle ⟨n%4,Nat.mod_lt _ (by decide)⟩
def cycleLow (n : ℕ) : Bool := decide (n%4=1 ∨ n%4=3)
def cycleHigh (n : ℕ) : Bool := decide (2≤n%4)
def cycleSelect (cycle : Cycle) : Code :=
  .branch 241
    (.branch 240 (NatAssign.code (step (cycle 3))) (NatAssign.code (step (cycle 2))))
    (.branch 240 (NatAssign.code (step (cycle 1))) (NatAssign.code (step (cycle 0))))
def cycleAdvance : Code :=
  .seq (Code.atom (.bitXor 241 241 240)) (Code.atom (.bitNot 240 240))
def cycleStep (cycle : Cycle) : Code := .seq (cycleSelect cycle) cycleAdvance

theorem cycleLow_succ (n : ℕ) : cycleLow (n+1)= !cycleLow n := by
  have h : n%4<4 := Nat.mod_lt _ (by decide)
  have he : (n+1)%4=(n%4+1)%4 := by omega
  interval_cases hm : n%4 <;> simp [cycleLow,he,hm]
theorem cycleHigh_succ (n : ℕ) : cycleHigh (n+1)=xor (cycleHigh n) (cycleLow n) := by
  have h : n%4<4 := Nat.mod_lt _ (by decide)
  have he : (n+1)%4=(n%4+1)%4 := by omega
  interval_cases hm : n%4 <;> simp [cycleLow,cycleHigh,he,hm]

structure CycleReady (a b : ℕ) (cycle : Cycle) (n : ℕ) (s : Store) : Prop where
  data : Ready a b (cycleSigns cycle) n s
  low : s.val.registers 240=cycleLow (n+1)
  high : s.val.registers 241=cycleHigh (n+1)

theorem cycleSelect_executes (a b : ℕ) (cycle : Cycle) (n N W : ℕ) (hn : n<N)
    (ha : a.bits.length≤W) (hb : b.bits.length≤W)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : CycleReady a b cycle n s) :
    ∃cost t,Executes input tape (cycleSelect cycle) cost s t ∧
      cost≤2^44*(width N W+2)^2+2 ∧ Ready a b (cycleSigns cycle) (n+1) t ∧
      t.val.registers 240=cycleLow (n+1) ∧ t.val.registers 241=cycleHigh (n+1) ∧
      BinaryPrecision.Frame workspace s.val t.val := by
  obtain ⟨cost,t,he,hc,ht,hf⟩ := step_executes a b (cycleSigns cycle) n N W hn ha hb input tape s hs.data
  have hp0 := he.protectsRegister 240 (by cases cycleSigns cycle (n+1) <;> rfl)
  have hp1 := he.protectsRegister 241 (by cases cycleSigns cycle (n+1) <;> rfl)
  refine ⟨1+(1+cost),t,?_,by omega,ht,hp0.trans hs.low,hp1.trans hs.high,hf⟩
  have h : (n+1)%4<4 := Nat.mod_lt _ (by decide)
  have hlo := hs.low
  have hhi := hs.high
  interval_cases hm : (n+1)%4
  all_goals simp only [cycleSigns,hm] at he
  all_goals simp only [cycleLow,cycleHigh,hm] at hlo hhi
  · exact Executes.no hhi (Executes.no hlo he)
  · exact Executes.no hhi (Executes.yes hlo he)
  · exact Executes.yes hhi (Executes.no hlo he)
  · exact Executes.yes hhi (Executes.yes hlo he)

theorem cycleStep_executes (a b : ℕ) (cycle : Cycle) (n N W : ℕ) (hn : n<N)
    (ha : a.bits.length≤W) (hb : b.bits.length≤W)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : CycleReady a b cycle n s) :
    ∃cost t,Executes input tape (cycleStep cycle) cost s t ∧
      cost≤2^44*(width N W+2)^2+6 ∧ CycleReady a b cycle (n+1) t ∧
      BinaryPrecision.Frame workspace s.val t.val := by
  obtain ⟨cost,u,he,hc,hu,hlo,hhi,hf⟩ := cycleSelect_executes a b cycle n N W hn ha hb input tape s hs
  let v := Store.ofState (u.val.setRegister 241 (xor (u.val.registers 241) (u.val.registers 240)))
  let t := Store.ofState (v.val.setRegister 240 (!v.val.registers 240))
  have e1 : Executes input tape (Code.atom (.bitXor 241 241 240)) 2 u v :=
    Executes.bitXor input tape u 241 241 240
  have e2 : Executes input tape (Code.atom (.bitNot 240 240)) 2 v t :=
    Executes.bitNot input tape v 240 240
  have htdata : Ready a b (cycleSigns cycle) (n+1) t := ⟨hu.bank,hu.scratch⟩
  have htl : t.val.registers 240=cycleLow ((n+1)+1) := by
    simp only [t,v,Store.ofState,BitRAMState.setRegister,Function.update_self,
      Function.update_of_ne (by decide : (240:ℕ)≠241)]
    rw [hlo,cycleLow_succ (n+1)]
  have hth : t.val.registers 241=cycleHigh ((n+1)+1) := by
    simp only [t,v,Store.ofState,BitRAMState.setRegister,
      Function.update_of_ne (by decide : (241:ℕ)≠240),Function.update_self]
    rw [hhi,hlo,cycleHigh_succ (n+1)]
  refine ⟨cost+(2+2),t,he.seq (e1.seq e2),by omega,⟨htdata,htl,hth⟩,?_⟩
  exact hf.trans ⟨rfl,rfl,rfl,rfl,rfl,fun _ _ => rfl⟩

theorem CycleReady.count_frame (a b : ℕ) (cycle : Cycle) (n : ℕ) {s t : Store}
    (hs : CycleReady a b cycle n s) (hf : CountedShifted.Frame 609 s t) : CycleReady a b cycle n t := by
  refine ⟨hs.data.count_frame a b (cycleSigns cycle) n hf,?_,?_⟩
  · exact (hf.2.2.2.2.2.2 240 (by decide) (by decide) (by decide) (by decide)).trans hs.low
  · exact (hf.2.2.2.2.2.2 241 (by decide) (by decide) (by decide) (by decide)).trans hs.high

#print axioms cycleStep_executes
end Maxwell.Continuum.RationalTaylor.Runtime
