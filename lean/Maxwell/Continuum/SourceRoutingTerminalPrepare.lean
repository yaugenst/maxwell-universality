import Maxwell.Continuum.SourceRoutingTerminalShapes
import Maxwell.Continuum.SourceRoutingPathRestore

/-! Recover terminal origins and bottom-arm selectors from the current port.
The program uses the same stored grid width and fixed scratch bank as slabs. -/
namespace Maxwell.Cost.RoutingPorts.Complete.GeometryPath
open Structured GeometryArithmetic Maxwell.Logical.Routing
open RationalAccumulator (Word Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 2800000

def terminalProgram (bottom : Bool) : Control :=
  .divide 1201 1200 1203 1204 (if bottom then
    .divide 1203 1220 1226 1209 (.divide 1204 1220 1227 1210
      (Control.prepend [.literal 1229 32,.multiply 1229 1226,.multiply 1229 1227,.literal 1228 0] .done))
  else Control.prepend [.literal 1229 16,.copy 1203 1226,.copy 1204 1227,
    .multiply 1229 1226,.multiply 1229 1227,.literal 1229 96,.copy 1200 1228,
    .multiply 1229 1228] .done)

def terminalValues {q : ℕ} (p : GeometrySort.Plan q) (round : ℕ) (port : Port q)
    (cursor : ℕ) (bottom : Bool) : ℕ→ℕ :=
  (terminalProgram bottom).evaluate (cursorValues (GeometrySort.seed p round (finProdFinEquiv port).val) cursor)

theorem terminalProgram_valid (bottom : Bool) : (terminalProgram bottom).Valid := by
  cases bottom <;> simp [terminalProgram,Control.Valid,Control.prepend,NatAssign.Instruction.Valid,controls]

theorem terminalProgram_steps (bottom : Bool) : (terminalProgram bottom).steps ≤ 9 := by
  cases bottom <;> decide

theorem terminalProgram_literals (bottom : Bool) (B : ℕ) (large : 7 ≤ B) :
    (terminalProgram bottom).Literals B := by
  have h16 : (16 : ℕ).bits.length=5 := by decide
  have h32 : (32 : ℕ).bits.length=6 := by decide
  have h96 : (96 : ℕ).bits.length=7 := by decide
  cases bottom <;> simp [terminalProgram,Control.Literals,Control.prepend,NatAssign.Instruction.literalWidth]
  all_goals omega

theorem terminal_other {q : ℕ} (p : GeometrySort.Plan q) (round : ℕ) (port : Port q)
    (cursor : ℕ) (bottom : Bool) (j : ℕ)
    (outside : j∉({1203,1204,1209,1210,1226,1227,1228,1229} : Finset ℕ)) :
    terminalValues p round port cursor bottom j=cursorValues (GeometrySort.seed p round (finProdFinEquiv port).val) cursor j := by
  apply Control.evaluate_other
  intro h
  exact outside ((show (terminalProgram bottom).writes⊆{1203,1204,1209,1210,1226,1227,1228,1229}
    by cases bottom <;> decide) h)

theorem terminal_values {q : ℕ} (p : GeometrySort.Plan q) (round : ℕ) (port : Port q) (cursor : ℕ) (bottom : Bool) :
    let v := terminalValues p round port cursor bottom
    v (axisBank 0)=(if bottom then 32*(port.1.val/2) else 16*port.1.val) ∧
    v (axisBank 1)=(if bottom then 32*(port.2.val/2) else 16*port.2.val) ∧
    v (axisBank 2)=(if bottom then 0 else 96*q) := by
  have quotient : (port.2.val+q*port.1.val)/q=port.1.val :=
    congrArg (fun a : Port q => a.1.val) (finProdFinEquiv.symm_apply_apply port)
  cases bottom <;> simp [terminalValues,terminalProgram,Control.evaluate,Control.prepend,divided,
    NatAssign.Instruction.update,NatAssign.Instruction.target,NatAssign.Instruction.value,
    cursorValues,GeometrySort.seed,axisBank,finProdFinEquiv,quotient,Nat.mod_eq_of_lt port.2.isLt]

theorem terminal_selectors {q : ℕ} (p : GeometrySort.Plan q) (round : ℕ) (port : Port q) (cursor : ℕ) :
    terminalValues p round port cursor true 1209=port.1.val%2 ∧
    terminalValues p round port cursor true 1210=port.2.val%2 := by
  have quotient : (port.2.val+q*port.1.val)/q=port.1.val :=
    congrArg (fun a : Port q => a.1.val) (finProdFinEquiv.symm_apply_apply port)
  simp [terminalValues,terminalProgram,Control.evaluate,Control.prepend,divided,
    NatAssign.Instruction.update,NatAssign.Instruction.target,NatAssign.Instruction.value,
    cursorValues,GeometrySort.seed,finProdFinEquiv,quotient,Nat.mod_eq_of_lt port.2.isLt]

theorem terminal_fields {q : ℕ} (p : GeometrySort.Plan q) (round : ℕ) (port : Port q)
    (cursor : ℕ) (bottom : Bool) :
    ∀j∈seedFields,terminalValues p round port cursor bottom j=GeometrySort.seed p round (finProdFinEquiv port).val j := by
  intro j hj
  have outside : j∉({1203,1204,1209,1210,1226,1227,1228,1229} : Finset ℕ) ∧ j≠1234 := by
    simp only [seedFields,Finset.mem_insert,Finset.mem_singleton] at hj
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or]
    omega
  rw [terminal_other p round port cursor bottom j outside.1,cursorValues_other _ _ _ outside.2]

theorem terminal_zero {q : ℕ} (p : GeometrySort.Plan q) (round : ℕ) (port : Port q)
    (cursor : ℕ) (bottom : Bool) :
    ∀j∈Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,terminalValues p round port cursor bottom j=0 := by
  apply (terminalProgram bottom).evaluate_zero (terminalProgram_valid bottom)
  intro j hj
  have small : j<1200 := by
    simp only [Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,Finset.mem_insert,Finset.mem_singleton] at hj
    omega
  rw [cursorValues_other _ _ j (by omega),GeometrySort.seed_zero p round _ j hj]

theorem terminal_width {q : ℕ} (p : GeometrySort.Plan q) (round : ℕ) (port : Port q)
    (cursor B : ℕ) (bottom : Bool) (large : 7 ≤ B) (planBound : p.bound round ≤ B) (cursorBound : cursor.bits.length ≤ B) :
    ∀j∈ids,(terminalValues p round port cursor bottom j).bits.length ≤ 2^9*(B+1) := by
  have initial : ∀j∈ids,(cursorValues (GeometrySort.seed p round (finProdFinEquiv port).val) cursor j).bits.length ≤ B :=
    cursorValues_width _ _ _ (fun j hj => (GeometrySort.seed_width p round _ (finProdFinEquiv port).isLt.le j hj).trans planBound) cursorBound
  have h := (terminalProgram bottom).evaluate_width (terminalProgram_valid bottom) _ B initial (terminalProgram_literals bottom B large)
  intro j hj
  exact (Nat.le_add_right _ _).trans ((h j hj).trans (Nat.mul_le_mul_right _
    (Nat.pow_le_pow_right (by decide) (terminalProgram_steps bottom))))

def terminalPrepare (bottom : Bool) : Code := .seq (loadCode 1253 1234) (terminalProgram bottom).code

theorem terminalPrepare_executes {q : ℕ} (p : GeometrySort.Plan q) (round : ℕ) (port : Port q)
    (cursor B : ℕ) (bottom : Bool) (large : 7 ≤ B) (planBound : p.bound round ≤ B) (cursorBound : cursor.bits.length ≤ B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank ids (GeometrySort.seed p round (finProdFinEquiv port).val) s.val)
    (ready : GeometryArray.Ready s.val) (privateBlank : Blank s.val 1249) (cursorWord : Word s.val 1253 cursor) :
    ∃steps t,Executes input tape (terminalPrepare bottom) steps s t ∧
      steps ≤ 2^139*(B+2)^2 ∧ NatAssign.Bank ids (terminalValues p round port cursor bottom) t.val ∧
      GeometryArray.Ready t.val ∧ Blank t.val 1249 ∧ BinaryPrecision.Frame work s.val t.val := by
  obtain ⟨c₀,a,e₀,h₀,ba,za,pa,f₀⟩ := load_executes 1253 1234 (by decide) (by decide)
    (GeometrySort.seed p round (finProdFinEquiv port).val) cursor input tape s bank ready privateBlank cursorWord
  have initial : ∀j∈ids,(cursorValues (GeometrySort.seed p round (finProdFinEquiv port).val) cursor j).bits.length ≤ B :=
    cursorValues_width _ _ _ (fun j hj => (GeometrySort.seed_width p round _ (finProdFinEquiv port).isLt.le j hj).trans planBound) cursorBound
  have zero : ∀j∈Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,
      cursorValues (GeometrySort.seed p round (finProdFinEquiv port).val) cursor j=0 := by
    intro j hj
    have small : j<1200 := by
      simp only [Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,Finset.mem_insert,Finset.mem_singleton] at hj
      omega
    rw [cursorValues_other _ _ j (by omega),GeometrySort.seed_zero p round _ j hj]
  have admissible : (terminalProgram bottom).Admissible
      (cursorValues (GeometrySort.seed p round (finProdFinEquiv port).val) cursor) := by
    cases bottom <;> simp [terminalProgram,Control.Admissible,Control.prepend,divided,
      cursorValues,GeometrySort.seed,p.positive]
  obtain ⟨c₁,t,e₁,h₁,bt,zt,pt,f₁⟩ := (terminalProgram bottom).executes (terminalProgram_valid bottom) _ zero
    admissible B initial (terminalProgram_literals bottom B large) input tape a ba za pa
  refine ⟨c₀+c₁,t,e₀.seq e₁,?_,bt,zt,pt,(f₀.mono (by decide)).trans f₁⟩
  have bounded := h₁.trans (controlCost_steps _ _ _ (terminalProgram_steps bottom))
  change c₁ ≤ 2^137*(B+2)^2 at bounded
  change c₀ ≤ 6*0+15*cursor.bits.length+21 at h₀
  nlinarith only [h₀,bounded,cursorBound]

#print axioms terminal_values
#print axioms terminalPrepare_executes
end Maxwell.Cost.RoutingPorts.Complete.GeometryPath
