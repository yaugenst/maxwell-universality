import Maxwell.Continuum.ParameterSourceLog
import Maxwell.Continuum.ParameterSourceBudgetMachine

/-! Load the retained source counts and the computed geometry count into
the parameter bank. All other high control words start from fresh tapes. -/
namespace Maxwell.Continuum.Parameters.SourceInitialize
open Maxwell.Cost Maxwell.Cost.Structured
open RationalAccumulator (Word Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 1800000

def sourcePorts : Finset ℕ := {500,501,503,1200,1209}
def ids : Finset ℕ := SourceLogMachine.ids∪sourcePorts
def instructions : List NatAssign.Instruction :=
  [.copy 500 2300,.copy 501 2301,.copy 503 2302,.copy 1200 2303,.copy 1209 2304]
def code : Code := NatAssign.code instructions
def work : Finset ℕ := {0,1,2,3,2300,2301,2302,2303,2304}
def initial (n m circuit side sites i : ℕ) : ℕ :=
  if i=500 then n else if i=501 then m else if i=503 then circuit
  else if i=1200 then side else if i=1209 then sites else 0
def values (n m circuit side sites : ℕ) : ℕ→ℕ :=
  NatAssign.values instructions (initial n m circuit side sites)
def inputWidth (n m circuit side sites : ℕ) : ℕ :=
  n.bits.length+m.bits.length+circuit.bits.length+side.bits.length+sites.bits.length

theorem valid : ∀a∈instructions,a.Valid ids := by
  simp [instructions,NatAssign.Instruction.Valid,ids,SourceLogMachine.ids,SourceBudgetMachine.ids,
    SourceBudgetMachine.extra,SourceBudgetMachine.outputs,sourcePorts]

theorem fields (n m circuit side sites : ℕ) :
    values n m circuit side sites 2300=n ∧ values n m circuit side sites 2301=m ∧
    values n m circuit side sites 2302=circuit ∧ values n m circuit side sites 2303=side ∧
    values n m circuit side sites 2304=sites := by
  simp [values,instructions,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.value,
    NatAssign.Instruction.target,initial]

theorem initial_bank (n m circuit side sites : ℕ) (s : BitRAMState)
    (wn : Word s 500 n) (wm : Word s 501 m) (wc : Word s 503 circuit)
    (wq : Word s 1200 side) (wj : Word s 1209 sites)
    (fresh : ∀i∈SourceLogMachine.ids,Blank s i) :
    NatAssign.Bank ids (initial n m circuit side sites) s := by
  intro i hi
  by_cases h500 : i=500
  · subst i;simpa [initial] using wn
  by_cases h501 : i=501
  · subst i;simpa [initial] using wm
  by_cases h503 : i=503
  · subst i;simpa [initial] using wc
  by_cases h1200 : i=1200
  · subst i;simpa [initial] using wq
  by_cases h1209 : i=1209
  · subst i;simpa [initial] using wj
  have hi' : i∈SourceLogMachine.ids := by
    rcases Finset.mem_union.mp hi with hi|hi
    · exact hi
    · simp only [sourcePorts,Finset.mem_insert,Finset.mem_singleton] at hi
      omega
  simpa only [initial,ite_eq_right h500,ite_eq_right h501,ite_eq_right h503,ite_eq_right h1200,ite_eq_right h1209]
    using (RationalAccumulator.zero_word_iff_blank s i).mpr (fresh i hi')

theorem executes (n m circuit side sites : ℕ) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (wn : Word s.val 500 n) (wm : Word s.val 501 m) (wc : Word s.val 503 circuit)
    (wq : Word s.val 1200 side) (wj : Word s.val 1209 sites)
    (fresh : ∀i∈SourceLogMachine.ids,Blank s.val i) (scratch : NatAssign.Scratch s.val) :
    ∃steps t,Executes input tape code steps s t ∧
      steps≤3000*8^5*(inputWidth n m circuit side sites+2)^2 ∧
      NatAssign.Bank SourceLogMachine.ids (values n m circuit side sites) t.val ∧
      (∀i∈SourceLogMachine.ids,(values n m circuit side sites i).bits.length≤
        32*(inputWidth n m circuit side sites+1)) ∧ NatAssign.Scratch t.val ∧
      BinaryPrecision.Frame work s.val t.val := by
  have lower : ∀i∈ids,4≤ i := by
    intro i hi
    rcases Finset.mem_union.mp hi with hi|hi
    · exact SourceLogMachine.ids_lower i hi
    · simp only [sourcePorts,Finset.mem_insert,Finset.mem_singleton] at hi;omega
  have width : ∀i∈ids,(initial n m circuit side sites i).bits.length ≤ inputWidth n m circuit side sites := by
    intro i _
    simp only [initial]
    split_ifs <;> simp only [inputWidth,show (0:ℕ).bits.length=0 by decide] <;> omega
  have literals : ∀a∈instructions,a.literalWidth ≤ inputWidth n m circuit side sites := by
    simp [instructions,NatAssign.Instruction.literalWidth]
  obtain ⟨steps,t,he,hc,bt,st,ft⟩:=NatAssign.executes ids lower instructions valid
    (initial n m circuit side sites) input tape s (initial_bank n m circuit side sites s.val wn wm wc wq wj fresh) scratch
  refine ⟨steps,t,he,hc.trans (NatAssign.price_bound ids instructions valid _ _ width literals),
    fun i hi=>bt i (Finset.mem_union_left _ hi),?_,st,ft.mono (by decide +kernel)⟩
  intro i hi
  have h:=NatAssign.values_width ids instructions valid _ _ width literals i (Finset.mem_union_left _ hi)
  exact (Nat.le_add_right _ 1).trans h

#print axioms executes
end Maxwell.Continuum.Parameters.SourceInitialize
