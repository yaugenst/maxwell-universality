import Maxwell.Cost.RealSimulation.InstructionSimulation

namespace Maxwell.Cost.RealSimulation
open Control

/-- These are precisely the finite scalar cells changed by the interpreter.
All other changed cells receive a Boolean or tape symbol. -/
def ScalarCell (L : Layout) (j : ℕ) : Prop :=
  j < 16 ∨ j = virtualPC ∨ j = addressLength ∨ j = inputHead ∨ j = outputLength ∨
    (256 ≤ j ∧ j < L.frameEnd)

def WriteFrame (L : Layout) (s t : RAMState) : Prop :=
  ∀ j, ¬ ScalarCell L j → t.indices j = s.indices j ∨ t.indices j ≤ 2

theorem WriteFrame.refl (L : Layout) (s : RAMState) : WriteFrame L s s :=
  fun _ _ => Or.inl rfl

theorem WriteFrame.trans {L : Layout} {s t u : RAMState}
    (h : WriteFrame L s t) (k : WriteFrame L t u) : WriteFrame L s u := by
  intro j hj
  rcases k j hj with he | hb
  · rw [he]; exact h j hj
  · exact Or.inr hb

theorem WriteFrame.put_scalar {L : Layout} {s t : Store} (h : WriteFrame L s.val t.val)
    (j v : ℕ) (hj : ScalarCell L j) : WriteFrame L s.val (t.put j v).val := by
  intro i hi
  have hn : i ≠ j := by rintro rfl; exact hi hj
  simpa only [Store.put_indices, ite_eq_right hn] using h i hi

theorem WriteFrame.put_small {L : Layout} {s t : Store} (h : WriteFrame L s.val t.val)
    (j v : ℕ) (hv : v ≤ 2) : WriteFrame L s.val (t.put j v).val := by
  intro i hi
  by_cases he : i = j
  · right; simpa only [Store.put_indices, he, ite_true] using hv
  · simpa only [Store.put_indices, ite_eq_right he] using h i hi

def LocalInstruction (P : ℕ → Prop) : RAMInstruction → Prop
  | .indexLiteral dst _ | .indexCopy dst _ | .indexAdd dst _ _ |
      .indexSubtract dst _ _ | .inputIndex dst _ | .loadIndex dst _ => P dst
  | .storeIndex _ _ => False
  | _ => True

def LocalCode (P : ℕ → Prop) : Code → Prop
  | .skip => True
  | .call body => ∀ op ∈ body.code, LocalInstruction P op
  | .seq a b | .branch _ _ a b => LocalCode P a ∧ LocalCode P b
  | .loop _ _ body => LocalCode P body

theorem local_next {P : ℕ → Prop} {M : Machine} {input : RAMInput} {tape : ℕ → Bool}
    (hloc : ∀ op ∈ M.code, LocalInstruction P op) {s t : RAMState}
    (step : M.next input tape s = some t) (j : ℕ) (hj : ¬ P j) :
    t.indices j = s.indices j := by
  cases hc : M.code[s.pc]? with
  | none => simp [Machine.next, hc] at step
  | some op =>
    have hl := hloc op (List.mem_of_getElem? hc)
    cases op <;> simp only [LocalInstruction] at hl
    all_goals simp only [Machine.next, hc, Option.some.injEq, reduceCtorEq] at step
    all_goals subst t
    all_goals try rfl
    all_goals simp only [RAMState.setIndex, Function.update_apply]
    all_goals split_ifs with he
    all_goals try rfl
    all_goals exact False.elim (hj (he ▸ hl))

theorem local_steps {P : ℕ → Prop} {M : Machine} {input : RAMInput} {tape : ℕ → Bool}
    (hloc : ∀ op ∈ M.code, LocalInstruction P op) {s t : RAMState} {n : ℕ}
    (steps : Steps (M.next input tape) n s t) (j : ℕ) (hj : ¬ P j) :
    t.indices j = s.indices j := by
  induction steps with
  | refl => rfl
  | step h _ ih => exact ih.trans (local_next hloc h j hj)

theorem LocalCode.preserves {P : ℕ → Prop} {code : Code} (hloc : LocalCode P code)
    {input : RAMInput} {tape : ℕ → Bool} {s t : Store} {n : ℕ}
    (execution : Executes input tape code n s t) (j : ℕ) (hj : ¬ P j) :
    t.val.indices j = s.val.indices j := by
  induction execution with
  | skip => rfl
  | call body s t cost steps halt => exact local_steps hloc steps j hj
  | seq _ _ ih1 ih2 => exact (ih2 hloc.2).trans (ih1 hloc.1)
  | yes _ _ ih => exact ih hloc.1
  | no _ _ ih => exact ih hloc.2
  | done => rfl
  | more _ _ _ ih1 ih2 => exact (ih2 hloc).trans (ih1 hloc)

theorem LocalCode.frame {L : Layout} {code : Code} (hloc : LocalCode (ScalarCell L) code)
    {input : RAMInput} {tape : ℕ → Bool} {s t : Store} {n : ℕ}
    (execution : Executes input tape code n s t) : WriteFrame L s.val t.val :=
  fun j hj => Or.inl (hloc.preserves execution j hj)

@[simp] theorem scalar_small (L : Layout) (j : ℕ) (h : j < 16) : ScalarCell L j := Or.inl h
@[simp] theorem scalar_pc (L : Layout) : ScalarCell L virtualPC := by simp [ScalarCell]
@[simp] theorem scalar_length (L : Layout) : ScalarCell L addressLength := by simp [ScalarCell]
@[simp] theorem scalar_inputHead (L : Layout) : ScalarCell L inputHead := by simp [ScalarCell]
@[simp] theorem scalar_outputLength (L : Layout) : ScalarCell L outputLength := by simp [ScalarCell]
theorem scalar_bit (L : Layout) (r : ℕ) (h : r < L.registerCount) :
    ScalarCell L (L.bitRegister r) := by
  simp only [ScalarCell, Layout.bitRegister, Layout.frameEnd]
  omega
theorem scalar_tape (L : Layout) (t : ℕ) (h : t < L.tapeCount) :
    ScalarCell L (L.tapeHead t) := by
  simp only [ScalarCell, Layout.tapeHead, Layout.frameEnd]
  omega

theorem local_repeatAdd {P : ℕ → Prop} (dst src n : ℕ) (h : P dst) :
    LocalCode P (repeatAdd dst src n) := by
  induction n with
  | zero => trivial
  | succ n ih => simpa [repeatAdd, LocalCode, add, LocalInstruction] using And.intro h ih

theorem local_bankPointer (L : Layout) (bank coordinate : ℕ) :
    LocalCode (ScalarCell L) (bankPointer L bank coordinate) := by
  simp only [bankPointer, sequence, LocalCode, literal, add, List.mem_cons, List.not_mem_nil,
    or_false, forall_eq_or_imp, forall_eq, LocalInstruction, and_true]
  exact ⟨scalar_small L _ (by decide), scalar_small L _ (by decide),
    local_repeatAdd _ _ _ (scalar_small L _ (by decide))⟩

theorem local_decodeStack (L : Layout) :
    LocalCode (ScalarCell L) (decodeStack Address.code) := by
  simp [decodeStack, sequence, LocalCode, copy, add, LocalInstruction,
    Address.code, Address.initProgram, Address.body, ScalarCell]

theorem Control.Executes.same_store {input : RAMInput} {tape : ℕ → Bool}
    {code : Code} {n m : ℕ} {s t u : Store}
    (ht : Executes input tape code n s t) (hu : Executes input tape code m s u) : t = u := by
  have h1 := (ht.compiled_run (n + m + 1) (by omega)).1
  have h2 := (hu.compiled_run (n + m + 1) (by omega)).1
  have he : t.place code.size = u.place code.size := Option.some.inj (h1.symm.trans h2)
  have hh := congrArg Store.ofState he
  have normalize (v : Store) : Store.ofState (v.place code.size) = v := by
    apply Subtype.ext
    simp [Store.ofState, Store.place, ← v.property]
  simpa only [normalize] using hh

def HasBankStore : BitRAMInstruction → Prop
  | .writeTape _ _ | .eraseTape _ | .addressPush _ | .writeMemory _ | .output _ => True
  | _ => False

theorem instruction_local (L : Layout) (op : BitRAMInstruction)
    (fit : Fits L op) (nostore : ¬ HasBankStore op) :
    LocalCode (ScalarCell L) (instruction L Address.code op) := by
  cases op <;> simp only [HasBankStore, not_true_eq_false] at nostore
  all_goals simp only [Fits, registerCap, tapeCap, Nat.max_le] at fit
  all_goals simp only [instruction, sequence, LocalCode, boundedInput, incrementPC,
    local_bankPointer, local_decodeStack]
  all_goals simp only [literal, copy, add, subtract, load, drawBit, LocalCode,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    LocalInstruction, and_true, true_and]
  all_goals simp only [ScalarCell, Layout.bitRegister, Layout.tapeHead, Layout.frameEnd,
    virtualPC, addressLength, inputHead, outputLength,
    activeRegister, coordinateRegister, valueRegister]
  all_goals try simp only [true_or, or_true, and_true]
  all_goals omega

end Maxwell.Cost.RealSimulation
