import Maxwell.Cost.Structured.TapeInterval

/-! A structural upper bound on all tape identifiers mentioned by a program.
Keeping this expression symbolic avoids expanding large generated circuits. -/
namespace Maxwell.Cost

def BitRAMInstruction.tapeBound : BitRAMInstruction→ℕ
  | .readTape tape _ _ | .writeTape tape _ | .eraseTape tape
  | .tapeLeft tape | .tapeRight tape => tape+1
  | _ => 0

def BitRAM.tapeBound (body : BitRAM) : ℕ :=
  body.code.foldr (fun instruction bound => max instruction.tapeBound bound) 0

@[simp] theorem BitRAMInstruction.tapeBound_relocate (instruction : BitRAMInstruction) (base exitPC : ℕ) :
    (instruction.relocate base exitPC).tapeBound=instruction.tapeBound := by
  cases instruction <;> rfl

theorem BitRAM.tapeBound_append (first second : List BitRAMInstruction) :
    (BitRAM.mk (first++second)).tapeBound=
      max (BitRAM.mk first).tapeBound (BitRAM.mk second).tapeBound := by
  induction first with
  | nil => simp [tapeBound]
  | cons instruction rest ih =>
    simpa only [tapeBound,List.cons_append,List.foldr_cons,max_assoc] using
      congrArg (max instruction.tapeBound) ih

theorem BitRAM.tapeBound_relocate (body : BitRAM) (base exitPC : ℕ) :
    (BitRAM.mk (body.code.map (BitRAMInstruction.relocate base exitPC))).tapeBound=body.tapeBound := by
  rcases body with ⟨instructions⟩
  induction instructions with
  | nil => rfl
  | cons instruction rest ih =>
    simpa only [tapeBound,List.map_cons,List.foldr_cons,BitRAMInstruction.tapeBound_relocate] using
      congrArg (max instruction.tapeBound) ih

theorem BitRAMInstruction.protectsTape_of_bound (instruction : BitRAMInstruction) (i : ℕ)
    (h : instruction.tapeBound≤ i) : instruction.protectsTape i=true := by
  cases instruction <;> simp_all [tapeBound,protectsTape]
  all_goals omega

theorem BitRAM.tapeBound_le (body : BitRAM) (bound : ℕ) :
    body.tapeBound≤ bound ↔ ∀instruction∈body.code,instruction.tapeBound≤ bound := by
  rcases body with ⟨instructions⟩
  induction instructions with
  | nil => simp [tapeBound]
  | cons instruction rest ih =>
    simpa only [tapeBound,List.foldr_cons,max_le_iff,List.mem_cons,forall_eq_or_imp] using
      and_congr Iff.rfl ih

theorem BitRAM.protectsTape_of_bound (body : BitRAM) (i : ℕ) (h : body.tapeBound≤ i) :
    body.protectsTape i=true := by
  apply List.all_eq_true.mpr
  intro instruction member
  exact instruction.protectsTape_of_bound i ((body.tapeBound_le i).mp h instruction member)

namespace Structured

def Code.tapeBound : Code→ℕ
  | .skip => 0
  | .call body => body.tapeBound
  | .seq first second | .branch _ first second => max first.tapeBound second.tapeBound
  | .loop _ body => body.tapeBound

theorem Code.compileAt_tapeBound (code : Code) (base exitPC : ℕ) :
    (BitRAM.mk (code.compileAt base exitPC)).tapeBound=code.tapeBound := by
  induction code generalizing base exitPC with
  | skip => rfl
  | call body => exact body.tapeBound_relocate base exitPC
  | seq first second ih₁ ih₂ =>
    simp only [compileAt,BitRAM.tapeBound_append,ih₁,ih₂,tapeBound]
  | branch register yes no ih₁ ih₂ =>
    simp only [compileAt,BitRAM.tapeBound_append,ih₁,ih₂,tapeBound]
    change max (max 0 yes.tapeBound) no.tapeBound=max yes.tapeBound no.tapeBound
    rw [Nat.zero_max]
  | loop register body ih =>
    simp only [compileAt,BitRAM.tapeBound_append,ih,tapeBound]
    exact Nat.zero_max _

theorem Code.compile_tapeBound (code : Code) : code.compile.tapeBound=code.tapeBound := by
  simp only [compile,BitRAM.tapeBound_append,compileAt_tapeBound]
  exact Nat.max_zero _

theorem Code.protectsTape_of_bound (code : Code) (i : ℕ) (h : code.tapeBound≤ i) :
    code.protectsTape i=true := by
  induction code with
  | skip => rfl
  | call body => exact body.protectsTape_of_bound i h
  | seq first second ih₁ ih₂ =>
    simp only [tapeBound,max_le_iff] at h
    simp only [protectsTape,ih₁ h.1,ih₂ h.2,Bool.and_self]
  | branch register yes no ih₁ ih₂ =>
    simp only [tapeBound,max_le_iff] at h
    simp only [protectsTape,ih₁ h.1,ih₂ h.2,Bool.and_self]
  | loop register body ih => exact ih h

theorem Executes.tapeBound {input : List Bool} {tape : ℕ→Bool} {code : Code}
    {cost : ℕ} {s t : Store} (execution : Executes input tape code cost s t)
    (i : ℕ) (h : code.tapeBound≤ i) : t.val.tapes i=s.val.tapes i :=
  execution.protectsTape i (code.protectsTape_of_bound i h)

#print axioms Executes.tapeBound
end Structured
end Maxwell.Cost
