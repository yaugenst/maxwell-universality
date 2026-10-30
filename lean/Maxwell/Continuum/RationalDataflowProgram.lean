import Maxwell.Continuum.RationalDataflowInverse

/-! A finite shared-register rational program, compiled to the actual Boolean machine. -/

namespace Maxwell.Continuum.RationalDataflow
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

inductive Instruction where
  | literal (target : ℕ) (value : ℚ)
  | binary (op : BinaryOp) (target left right : ℕ)
  | inverse (target source : ℕ)
  deriving DecidableEq, Repr

def Instruction.update : Instruction → (ℕ→Parts) → (ℕ→Parts)
  | .literal target q,v => Function.update v target (Parts.literal q)
  | .binary op target left right,v => Function.update v target (op.eval (v left) (v right))
  | .inverse target source,v => Function.update v target (v source).inverse

def Instruction.Valid (S : Finset ℕ) : Instruction → Prop
  | .literal target _ => target∈S
  | .binary _ target left right => target∈S ∧ left∈S ∧ right∈S
  | .inverse target source => target∈S ∧ source∈S

def Instruction.LiteralFits (B : ℕ) : Instruction → Prop
  | .literal _ q => (Parts.literal q).Width B
  | _ => True

def Instruction.Admissible : Instruction → (ℕ→Parts) → Prop
  | .inverse _ source,v => (v source).value≠0
  | _,_ => True

def Instruction.code : Instruction → Code
  | .literal target q => NatAssign.code (literalStage target (Parts.literal q))
  | .binary op target left right => NatAssign.code (binaryStage op target left right)
  | .inverse target source => inverseCode target source

def evaluate : List Instruction → (ℕ→Parts) → (ℕ→Parts)
  | [],v => v
  | a::rest,v => evaluate rest (a.update v)

def program : List Instruction → Code
  | [] => .skip
  | a::rest => .seq a.code (program rest)

def Good (S : Finset ℕ) (v : ℕ→Parts) : Prop := ∀ i∈S, (v i).Valid
def WidthBank (S : Finset ℕ) (B : ℕ) (v : ℕ→Parts) : Prop := ∀ i∈S, (v i).Width B

def WidthTrace (S : Finset ℕ) (B : ℕ) : List Instruction → (ℕ→Parts) → Prop
  | [],v => WidthBank S B v
  | a::rest,v => WidthBank S B v ∧ a.LiteralFits B ∧ WidthTrace S B rest (a.update v)

def AdmissibleTrace : List Instruction → (ℕ→Parts) → Prop
  | [],_ => True
  | a::rest,v => a.Admissible v ∧ AdmissibleTrace rest (a.update v)

theorem Instruction.update_good (S : Finset ℕ) (a : Instruction) (ha : a.Valid S)
    (v : ℕ→Parts) (hv : Good S v) (had : a.Admissible v) : Good S (a.update v) := by
  intro i hi
  cases a with
  | literal target q =>
    by_cases he : i=target
    · subst i; simpa only [Instruction.update,Function.update_self] using Parts.literal_valid q
    · simpa only [Instruction.update,Function.update_of_ne he] using hv i hi
  | binary op target left right =>
    by_cases he : i=target
    · subst i
      simpa only [Instruction.update,Function.update_self] using
        BinaryOp.eval_valid op (hv left ha.2.1) (hv right ha.2.2)
    · simpa only [Instruction.update,Function.update_of_ne he] using hv i hi
  | inverse target source =>
    by_cases he : i=target
    · subst i; simpa only [Instruction.update,Function.update_self] using Parts.inverse_valid had
    · simpa only [Instruction.update,Function.update_of_ne he] using hv i hi

theorem evaluate_good (S : Finset ℕ) (ins : List Instruction) (hv : ∀ a∈ins, a.Valid S)
    (v : ℕ→Parts) (hg : Good S v) (had : AdmissibleTrace ins v) : Good S (evaluate ins v) := by
  induction ins generalizing v with
  | nil => exact hg
  | cons a rest ih =>
    exact ih (fun b hb => hv b (by simp [hb])) (a.update v)
      (a.update_good S (hv a (by simp)) v hg had.1) had.2

theorem Instruction.executes (S : Finset ℕ) (a : Instruction) (ha : a.Valid S)
    (v : ℕ→Parts) (B : ℕ) (hw : WidthBank S B v) (hl : a.LiteralFits B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : Ready S v s) :
    ∃ cost t, Executes input tape a.code cost s t ∧ cost≤operationCost B ∧
      Ready S (a.update v) t ∧ BinaryPrecision.Frame (workspace S) s.val t.val := by
  cases a with
  | literal target q =>
    obtain ⟨cost,t,he,hc,hb,hf⟩ := literal_executes S target ha (Parts.literal q) v B hl hw input tape s hs
    exact ⟨cost,t,he,hc.trans (stageCost_le_operationCost B),hb,hf⟩
  | binary op target left right =>
    obtain ⟨cost,t,he,hc,hb,hf⟩ := binary_executes S op target left right ha.1 ha.2.1 ha.2.2
      v B hw input tape s hs
    exact ⟨cost,t,he,hc.trans (stageCost_le_operationCost B),hb,hf⟩
  | inverse target source => exact inverse_executes S target source ha.1 ha.2 v B hw input tape s hs

theorem program_executes (S : Finset ℕ) (ins : List Instruction) (hv : ∀ a∈ins, a.Valid S)
    (v : ℕ→Parts) (B : ℕ) (hw : WidthTrace S B ins v)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : Ready S v s) :
    ∃ cost t, Executes input tape (program ins) cost s t ∧ cost ≤ ins.length*operationCost B+1 ∧
      Ready S (evaluate ins v) t ∧ BinaryPrecision.Frame (workspace S) s.val t.val := by
  induction ins generalizing v s with
  | nil => exact ⟨1,s,.skip s,by simp,hs,BinaryPrecision.Frame.refl _ _⟩
  | cons a rest ih =>
    obtain ⟨c0,s0,e0,h0,b0,f0⟩ := a.executes S (hv a (by simp)) v B hw.1 hw.2.1 input tape s hs
    obtain ⟨c1,t,e1,h1,b1,f1⟩ := ih (fun b hb => hv b (by simp [hb])) (a.update v) hw.2.2 s0 b0
    refine ⟨c0+c1,t,e0.seq e1,?_,b1,f0.trans f1⟩
    simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

theorem program_computes (S : Finset ℕ) (ins : List Instruction) (hv : ∀ a∈ins, a.Valid S)
    (v : ℕ→Parts) (B : ℕ) (hw : WidthTrace S B ins v)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : Ready S v s) :
    ∃ cost t,
      (runPriced ((program ins).compile.next input tape) (ins.length*operationCost B+2) s.val).finished=
        some (t.place (program ins).size) ∧
      (runPriced ((program ins).compile.next input tape) (ins.length*operationCost B+2) s.val).instructions=cost ∧
      cost ≤ ins.length*operationCost B+1 ∧ Ready S (evaluate ins v) t := by
  obtain ⟨cost,t,he,hc,hb,_⟩ := program_executes S ins hv v B hw input tape s hs
  obtain ⟨hrun,hcost⟩ := he.compiled_run (ins.length*operationCost B+2) (by omega)
  exact ⟨cost,t,hrun,hcost,hc,hb⟩

#print axioms evaluate_good
#print axioms program_computes

end Maxwell.Continuum.RationalDataflow
