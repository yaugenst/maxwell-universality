import Maxwell.Cost.SourceCircuit.Common

/-! A finite scan invokes one fixed body on each true bit. The semantic
invariant describes stored data only; the control flow is compiled Code. -/

namespace Maxwell.Cost.SourceCircuit.ScanBits
open Structured

def readCode (source : ℕ) : Code := .atom (.readTape source 30 31)

def checked (source : ℕ) (s : Store) : Store :=
  Store.ofState {s.val with
    registers := Function.update
      (Function.update s.val.registers 30 ((s.val.tapes source).read.getD false))
      31 ((s.val.tapes source).read.isSome)}

theorem read_executes (source : ℕ) (input : List Bool) (tape : ℕ → Bool) (s : Store) :
    Executes input tape (readCode source) 3 s (checked source s) := by
  apply Executes.atom (extra := 1) (t := {s.val.setRegister 30 ((s.val.tapes source).read.getD false) with
    registers := Function.update (Function.update s.val.registers 30
      ((s.val.tapes source).read.getD false)) 31 ((s.val.tapes source).read.isSome)})
  · simp [BitRAM.next,s.property]
  · simp [BitRAMState.setRegister,s.property]

def code (source : ℕ) (body : Code) : Code :=
  .seq (readCode source)
    (.loop 31 (.seq (.branch 30 body .skip)
      (.seq (.atom (.tapeRight source)) (readCode source))))

structure Passive (source : ℕ) (s t : Store) : Prop where
  address : t.val.address = s.val.address
  memory : t.val.memory = s.val.memory
  inputHead : t.val.inputHead = s.val.inputHead
  randomCursor : t.val.randomCursor = s.val.randomCursor
  output : t.val.output = s.val.output
  tapes : ∀ j, j ≠ source → t.val.tapes j = s.val.tapes j
  registers : ∀ j, j ≠ 30 → j ≠ 31 → t.val.registers j = s.val.registers j

theorem checked_passive (source : ℕ) (s : Store) : Passive source s (checked source s) := by
  refine ⟨rfl,rfl,rfl,rfl,rfl,fun _ _ => rfl,?_⟩
  intro j hj hk
  simp [checked,Store.ofState,hj,hk]

def advanced (source : ℕ) (s : Store) : Store := Store.ofState
  (s.val.setTape source {s.val.tapes source with head := (s.val.tapes source).head+1})

theorem advanced_passive (source : ℕ) (s : Store) : Passive source s (advanced source s) := by
  refine ⟨rfl,rfl,rfl,rfl,rfl,?_,fun _ _ _ => rfl⟩
  intro j hj
  simp [advanced,Store.ofState,BitRAMState.setTape,hj]

def fold {α : Type*} (step : α → α) : List Bool → α → α
  | [], data => data
  | b :: bits, data => fold step bits (if b then step data else data)

set_option maxRecDepth 8192 in
theorem executes {α : Type*} (source : ℕ) (body : Code) (step : α → α)
    (input : List Bool) (tape : ℕ → Bool) (invariant : List Bool → α → Store → Prop)
    (bound : ℕ)
    (stable : ∀ bits data s t, Passive source s t → invariant bits data s → invariant bits data t)
    (falseCorrect : ∀ bits data s, invariant (false::bits) data s → invariant bits data s)
    (bodyCorrect : ∀ bits data s, invariant (true::bits) data s →
      ∃ cost t, cost ≤ bound ∧ Executes input tape body cost s t ∧
        invariant bits (step data) t ∧ t.val.tapes source = s.val.tapes source)
    (bits preceding : List Bool) (origin : ℤ) (data : α) (s : Store)
    (hs : s.val.tapes source = Increment.cursor preceding bits origin)
    (hinv : invariant bits data s) :
    ∃ cost, ∃ t : Store, cost ≤ bits.length*(bound+8)+4 ∧
      Executes input tape (code source body) cost s t ∧
      invariant [] (fold step bits data) t ∧
      t.val.tapes source = BitTape.shiftedEnd (preceding ++ bits) origin := by
  induction bits generalizing preceding data s with
  | nil =>
    let c := checked source s
    have hread : (s.val.tapes source).read = none := by rw [hs,Increment.cursor_read]; rfl
    have hc : c.val.registers 31 = false := by simp [c,checked,Store.ofState,hread]
    refine ⟨4,c,by simp,(read_executes source input tape s).seq (.done hc),
      stable [] data s c (checked_passive source s) hinv,?_⟩
    simpa [c,checked,Store.ofState,Increment.cursor,BitTape.shiftedEnd] using hs
  | cons bit bits ih =>
    let c := checked source s
    have hread : (s.val.tapes source).read = some bit := by rw [hs,Increment.cursor_read]; rfl
    have present : c.val.registers 31 = true := by simp [c,checked,Store.ofState,hread]
    have symbol : c.val.registers 30 = bit := by simp [c,checked,Store.ofState,hread]
    have cinv := stable (bit::bits) data s c (checked_passive source s) hinv
    have bodyRun : ∃ cost u, cost ≤ bound+2 ∧
        Executes input tape (.branch 30 body .skip) cost c u ∧
        invariant bits (if bit then step data else data) u ∧
        u.val.tapes source = c.val.tapes source := by
      cases bit with
      | false => exact ⟨2,c,by omega,.no symbol (.skip c),falseCorrect bits data c cinv,rfl⟩
      | true =>
        obtain ⟨cost,u,hcost,he,hi,ht⟩ := bodyCorrect bits data c cinv
        exact ⟨1+cost,u,by omega,.yes symbol he,hi,ht⟩
    obtain ⟨bc,u,hbc,eb,uinv,us⟩ := bodyRun
    let v := advanced source u
    have ev := Executes.tapeRight input tape u source
    have vinv := stable bits _ u v (advanced_passive source u) uinv
    have vs : v.val.tapes source = Increment.cursor (preceding ++ [bit]) bits origin := by
      simp [v,advanced,Store.ofState,BitRAMState.setTape,us,c,checked,hs,
        Increment.cursor,List.append_assoc,Nat.cast_add,add_assoc]
    obtain ⟨rc,t,hrc,er,ti,ts⟩ := ih (preceding ++ [bit])
      (if bit then step data else data) v vs vinv
    change Executes input tape (.seq (readCode source) _) rc v t at er
    cases er with
    | seq test rest =>
      refine ⟨_,t,?_,(read_executes source input tape s).seq
        (.more present (eb.seq (ev.seq test)) rest),ti,?_⟩
      · simp only [List.length_cons]
        nlinarith
      · simpa [List.append_assoc] using ts

end Maxwell.Cost.SourceCircuit.ScanBits
