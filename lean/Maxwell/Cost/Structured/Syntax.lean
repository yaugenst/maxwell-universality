import Maxwell.Cost.Blocks

namespace Maxwell.Cost.Structured

/-- Finite structured control flow. Calls contain actual finite Boolean
programs; no constructor accepts a host-language state continuation. -/
inductive Code where
  | skip
  | call (body : BitRAM)
  | seq (first second : Code)
  | branch (register : ℕ) (yes no : Code)
  | loop (register : ℕ) (body : Code)

def Code.size : Code → ℕ
  | .skip => 1
  | .call body => body.code.length
  | .seq first second => first.size + second.size
  | .branch _ yes no => 1 + yes.size + no.size
  | .loop _ body => 1 + body.size

/-- Every return and loop backedge is an ordinary finite jump. The compiler
resolves only static code positions; it does not inspect input data. -/
def Code.compileAt : Code → ℕ → ℕ → List BitRAMInstruction
  | .skip, _, exitPC => [.jump exitPC]
  | .call body, base, exitPC => body.code.map (BitRAMInstruction.relocate base exitPC)
  | .seq first second, base, exitPC =>
      first.compileAt base (base + first.size) ++ second.compileAt (base + first.size) exitPC
  | .branch register yes no, base, exitPC =>
      [.branch register (base + 1) (base + 1 + yes.size)] ++
      yes.compileAt (base + 1) exitPC ++ no.compileAt (base + 1 + yes.size) exitPC
  | .loop register body, base, exitPC =>
      [.branch register (base + 1) exitPC] ++ body.compileAt (base + 1) base

@[simp] theorem Code.compileAt_length (code : Code) (base exitPC : ℕ) :
    (code.compileAt base exitPC).length = code.size := by
  induction code generalizing base exitPC with
  | skip => rfl
  | call body => simp [compileAt, size]
  | seq first second ih1 ih2 => simp [compileAt, size, ih1, ih2]
  | branch register yes no ih1 ih2 => simp [compileAt, size, ih1, ih2, Nat.add_comm, Nat.add_assoc]
  | loop register body ih => simp [compileAt, size, ih, Nat.add_comm]

def Code.compile (code : Code) : BitRAM := ⟨code.compileAt 0 code.size ++ [.halt]⟩

/-- A semantic state has no control-flow address. Its underlying machine
state is normalized to zero and the compiler supplies each actual PC. -/
abbrev Store := {s : BitRAMState // s.pc = 0}

def Store.ofState (s : BitRAMState) : Store := ⟨{s with pc := 0}, rfl⟩

def Store.place (s : Store) (pc : ℕ) : BitRAMState := {s.val with pc := pc}

@[simp] theorem Store.place_zero (s : Store) : s.place 0 = s.val := by
  simp [place, ← s.property]

@[simp] theorem Store.ofState_at (s : BitRAMState) (pc : ℕ) :
    (Store.ofState s).place pc = {s with pc := pc} := rfl

/-- Exact charged semantics. A call is justified by actual machine
transitions, then pays its return jump. Every tested loop/branch pays one
operation, including the final false loop test. -/
inductive Executes (input : List Bool) (randomTape : ℕ → Bool) :
    Code → ℕ → Store → Store → Prop where
  | skip (s : Store) : Executes input randomTape .skip 1 s s
  | call (body : BitRAM) (s : Store) (t : BitRAMState) (cost : ℕ)
      (steps : PricedSteps (body.next input randomTape) cost s.val t)
      (halt : body.code[t.pc]? = some .halt) :
      Executes input randomTape (.call body) (cost + 1) s (Store.ofState t)
  | seq {first second : Code} {a b : ℕ} {s t u : Store}
      (firstRun : Executes input randomTape first a s t)
      (secondRun : Executes input randomTape second b t u) :
      Executes input randomTape (.seq first second) (a + b) s u
  | yes {register : ℕ} {yes no : Code} {cost : ℕ} {s t : Store}
      (test : s.val.registers register = true)
      (body : Executes input randomTape yes cost s t) :
      Executes input randomTape (.branch register yes no) (1 + cost) s t
  | no {register : ℕ} {yes no : Code} {cost : ℕ} {s t : Store}
      (test : s.val.registers register = false)
      (body : Executes input randomTape no cost s t) :
      Executes input randomTape (.branch register yes no) (1 + cost) s t
  | done {register : ℕ} {body : Code} {s : Store}
      (test : s.val.registers register = false) :
      Executes input randomTape (.loop register body) 1 s s
  | more {register : ℕ} {body : Code} {a b : ℕ} {s t u : Store}
      (test : s.val.registers register = true)
      (bodyRun : Executes input randomTape body a s t)
      (rest : Executes input randomTape (.loop register body) b t u) :
      Executes input randomTape (.loop register body) (1 + a + b) s u

/-- A compiled fragment is present at these literal program positions. -/
def Placed (machine : BitRAM) (code : Code) (base exitPC : ℕ) : Prop :=
  ∀ i : Fin code.size, machine.code[base + i.val]? = (code.compileAt base exitPC)[i.val]?

end Maxwell.Cost.Structured
