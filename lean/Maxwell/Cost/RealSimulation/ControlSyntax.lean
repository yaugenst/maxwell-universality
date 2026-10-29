import Maxwell.Cost.RealLink

namespace Maxwell.Cost.RealSimulation.Control

/-- Finite structured control flow. Calls contain actual finite Real-RAM
programs; no constructor accepts a host-language state continuation. -/
inductive Code where
  | skip
  | call (body : Machine)
  | seq (first second : Code)
  | branch (left right : ℕ) (yes no : Code)
  | loop (left right : ℕ) (body : Code)

def Code.size : Code → ℕ
  | .skip => 1
  | .call body => body.code.length
  | .seq first second => first.size + second.size
  | .branch _ _ yes no => 1 + yes.size + no.size
  | .loop _ _ body => 1 + body.size

/-- Every return and loop backedge is an ordinary finite jump. The compiler
resolves only static code positions; it does not inspect input data. -/
def Code.compileAt : Code → ℕ → ℕ → List RAMInstruction
  | .skip, _, exitPC => [.jump exitPC]
  | .call body, base, exitPC => body.code.map (RAMInstruction.relocate base exitPC)
  | .seq first second, base, exitPC =>
      first.compileAt base (base + first.size) ++ second.compileAt (base + first.size) exitPC
  | .branch left right yes no, base, exitPC =>
      [.branchIndexLE left right (base + 1) (base + 1 + yes.size)] ++
      yes.compileAt (base + 1) exitPC ++ no.compileAt (base + 1 + yes.size) exitPC
  | .loop left right body, base, exitPC =>
      [.branchIndexLE left right (base + 1) exitPC] ++ body.compileAt (base + 1) base

@[simp] theorem Code.compileAt_length (code : Code) (base exitPC : ℕ) :
    (code.compileAt base exitPC).length = code.size := by
  induction code generalizing base exitPC with
  | skip => rfl
  | call body => simp [compileAt, size]
  | seq first second ih1 ih2 => simp [compileAt, size, ih1, ih2]
  | branch left right yes no ih1 ih2 => simp [compileAt, size, ih1, ih2, Nat.add_comm, Nat.add_assoc]
  | loop left right body ih => simp [compileAt, size, ih, Nat.add_comm]

def Code.compile (code : Code) : Machine := ⟨code.compileAt 0 code.size ++ [.halt]⟩

/-- A semantic state has no control-flow address. Its underlying machine
state is normalized to zero and the compiler supplies each actual PC. -/
abbrev Store := {s : RAMState // s.pc = 0}

def Store.ofState (s : RAMState) : Store := ⟨{s with pc := 0}, rfl⟩

def Store.place (s : Store) (pc : ℕ) : RAMState := {s.val with pc := pc}

@[simp] theorem Store.place_zero (s : Store) : s.place 0 = s.val := by
  simp [place, ← s.property]

@[simp] theorem Store.ofState_at (s : RAMState) (pc : ℕ) :
    (Store.ofState s).place pc = {s with pc := pc} := rfl

/-- Exact charged semantics. A call is justified by actual machine
transitions, then pays its return jump. Every tested loop/branch pays one
operation, including the final false loop test. -/
inductive Executes (input : RAMInput) (randomTape : ℕ → Bool) :
    Code → ℕ → Store → Store → Prop where
  | skip (s : Store) : Executes input randomTape .skip 1 s s
  | call (body : Machine) (s : Store) (t : RAMState) (cost : ℕ)
      (steps : Steps (body.next input randomTape) cost s.val t)
      (halt : body.code[t.pc]? = some .halt) :
      Executes input randomTape (.call body) (cost + 1) s (Store.ofState t)
  | seq {first second : Code} {a b : ℕ} {s t u : Store}
      (firstRun : Executes input randomTape first a s t)
      (secondRun : Executes input randomTape second b t u) :
      Executes input randomTape (.seq first second) (a + b) s u
  | yes {left right : ℕ} {yes no : Code} {cost : ℕ} {s t : Store}
      (test : s.val.indices left ≤ s.val.indices right)
      (body : Executes input randomTape yes cost s t) :
      Executes input randomTape (.branch left right yes no) (1 + cost) s t
  | no {left right : ℕ} {yes no : Code} {cost : ℕ} {s t : Store}
      (test : ¬ s.val.indices left ≤ s.val.indices right)
      (body : Executes input randomTape no cost s t) :
      Executes input randomTape (.branch left right yes no) (1 + cost) s t
  | done {left right : ℕ} {body : Code} {s : Store}
      (test : ¬ s.val.indices left ≤ s.val.indices right) :
      Executes input randomTape (.loop left right body) 1 s s
  | more {left right : ℕ} {body : Code} {a b : ℕ} {s t u : Store}
      (test : s.val.indices left ≤ s.val.indices right)
      (bodyRun : Executes input randomTape body a s t)
      (rest : Executes input randomTape (.loop left right body) b t u) :
      Executes input randomTape (.loop left right body) (1 + a + b) s u

/-- A compiled fragment is present at these literal program positions. -/
def Placed (machine : Machine) (code : Code) (base exitPC : ℕ) : Prop :=
  ∀ i : Fin code.size, machine.code[base + i.val]? = (code.compileAt base exitPC)[i.val]?

end Maxwell.Cost.RealSimulation.Control
