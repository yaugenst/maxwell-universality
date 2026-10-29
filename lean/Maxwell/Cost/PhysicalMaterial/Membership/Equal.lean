import Maxwell.Cost.SourceGrouping.WordEq
import Maxwell.Cost.SourceCircuit.RecordCleanup
import Maxwell.Cost.Structured.Primitive
import Maxwell.Cost.BinaryPrecision

namespace Maxwell.Cost.PhysicalMaterial.Membership
open Structured

private def rename : Equiv.Perm ℕ := (Equiv.swap 15 290).trans (Equiv.swap 22 291)
def equalProgram : BitRAM := SourceGrouping.WordEq.program.renameTapes rename

def equalCode : Code := .seq (.call equalProgram)
  (.seq (.call (TapeReset.program 290))
    (.seq (.call (TapeReset.program 291)) (Code.atom (.bitAnd 2 31 31))))

private theorem clear_end (target : ℕ) (input : List Bool) (tape : ℕ → Bool)
    (xs : List Bool) (origin : ℤ) (s : Store)
    (h : s.val.tapes target = BitTape.shiftedEnd xs origin) :
    ∃ t, Executes input tape (.call (TapeReset.program target)) (6*xs.length+6) s t ∧
      t.val.tapes = Function.update s.val.tapes target {BitTape.blank with head := origin} ∧
      BinaryPrecision.Frame {target} s.val t.val ∧ t.val.registers 31 = s.val.registers 31 := by
  let t := Store.ofState (TapeReset.finishAt target origin s.val)
  refine ⟨t,.call _ s _ _ (TapeReset.shifted_steps target origin input tape xs s.val s.property h)
    (by simp [TapeReset.program,TapeReset.finishAt]),rfl,?_,by simp [t,Store.ofState,TapeReset.finishAt]⟩
  refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
  intro i hi
  simp only [Finset.mem_singleton] at hi
  simp [t,Store.ofState,TapeReset.finishAt,hi]

private theorem shifted_compare (input : List Bool) (tape : ℕ → Bool)
    (xs ys : List Bool) (xo yo : ℤ) (s : BitRAMState) (hpc : s.pc = 0)
    (hx : s.tapes 15 = BitTape.shifted xs xo) (hy : s.tapes 22 = BitTape.shifted ys yo) :
    ∃ cost t, cost ≤ 15*(xs.length+ys.length+1)+1 ∧
      PricedSteps (SourceGrouping.WordEq.program.next input tape) cost s t ∧ t.pc = 15 ∧
      t.registers 31 = (xs == ys) ∧ t.tapes 15 = BitTape.shiftedEnd xs xo ∧
      t.tapes 22 = BitTape.shiftedEnd ys yo ∧ SourceGrouping.WordEq.frame s t := by
  have ei : PricedSteps (SourceGrouping.WordEq.program.next input tape) 1 s (s.setRegister 31 true) := by
    apply executeInstructions_sound (instructions := 1)
    simp [executeInstructions,BitRAM.next,SourceGrouping.WordEq.program,hpc]
  obtain ⟨cost,t,hcost,et,tpc,tbit,tx,ty,tf⟩ := SourceGrouping.WordEq.loop input tape xs ys
    (s.setRegister 31 true) (by simp [BitRAMState.setRegister,hpc])
    (by simpa [BitRAMState.setRegister,hx] using BitTape.shifted_represents xs xo)
    (by simpa [BitRAMState.setRegister,hy] using BitTape.shifted_represents ys yo)
  refine ⟨1+cost,t,by omega,ei.trans et,tpc,by simpa [BitRAMState.setRegister] using tbit,
    by simpa [BitRAMState.setRegister,hx,BitTape.shiftedEnd,BitTape.shifted] using tx,
    by simpa [BitRAMState.setRegister,hy,BitTape.shiftedEnd,BitTape.shifted] using ty,?_⟩
  apply SourceGrouping.WordEq.frame_trans (t := s.setRegister 31 true) _ tf
  refine ⟨rfl,rfl,rfl,rfl,rfl,fun _ _ _ => rfl,?_⟩
  intro i hi
  simp [BitRAMState.setRegister,show i ≠ 31 by omega]

set_option maxRecDepth 8192 in
theorem equal_executes (input : List Bool) (tape : ℕ → Bool) (x y : ℕ)
    (xo yo : ℤ) (s : Store)
    (hx : s.val.tapes 290 = BitTape.shifted x.bits xo)
    (hy : s.val.tapes 291 = BitTape.shifted y.bits yo) :
    ∃ cost t, cost ≤ 21*(x.bits.length+y.bits.length)+32 ∧
      Executes input tape equalCode cost s t ∧
      (t.val.registers 2 = true ↔ x = y) ∧
      t.val.tapes 290 = {BitTape.blank with head := xo} ∧
      t.val.tapes 291 = {BitTape.blank with head := yo} ∧
      BinaryPrecision.Frame {290,291} s.val t.val := by
  let initial := s.val.renameTapes rename.symm
  obtain ⟨cost,u,hcost,eu,upc,ubit,ux,uy,uf⟩ := shifted_compare input tape x.bits y.bits xo yo
    initial s.property
    (by simpa [initial,BitRAMState.renameTapes,rename,Equiv.swap_apply_def] using hx)
    (by simpa [initial,BitRAMState.renameTapes,rename,Equiv.swap_apply_def] using hy)
  let a := Store.ofState (u.renameTapes rename)
  have cancel : initial.renameTapes rename = s.val := by
    simp [initial,BitRAMState.renameTapes,Function.comp_def]
  have ep : PricedSteps (equalProgram.next input tape) cost s.val (u.renameTapes rename) := by
    simpa only [equalProgram,cancel] using eu.renameTapes rename
  have ea : Executes input tape (.call equalProgram) (cost+1) s a :=
    .call _ s _ _ ep (by simp [equalProgram,BitRAM.renameTapes,BitRAMState.renameTapes,upc,
      SourceGrouping.WordEq.program,BitRAMInstruction.renameTapes])
  have a290 : a.val.tapes 290 = BitTape.shiftedEnd x.bits xo := by
    simpa [a,Store.ofState,BitRAMState.renameTapes,rename,Equiv.swap_apply_def] using ux
  have a291 : a.val.tapes 291 = BitTape.shiftedEnd y.bits yo := by
    simpa [a,Store.ofState,BitRAMState.renameTapes,rename,Equiv.swap_apply_def] using uy
  have a31 : a.val.registers 31 = (x.bits == y.bits) := ubit
  have af : BinaryPrecision.Frame {290,291} s.val a.val := by
    refine ⟨uf.1,uf.2.1,uf.2.2.1,uf.2.2.2.1,uf.2.2.2.2.1,?_⟩
    intro i hi
    have hi290 : i ≠ 290 := by intro he; subst i; exact hi (by simp)
    have hi291 : i ≠ 291 := by intro he; subst i; exact hi (by simp)
    have h15 : rename.symm i ≠ 15 := by
      intro he
      have hh := congrArg rename he
      exact hi290 (by simpa only [Equiv.apply_symm_apply,show rename 15 = 290 by decide] using hh)
    have h22 : rename.symm i ≠ 22 := by
      intro he
      have hh := congrArg rename he
      exact hi291 (by simpa only [Equiv.apply_symm_apply,show rename 22 = 291 by decide] using hh)
    have h := uf.2.2.2.2.2.1 (rename.symm i) h15 h22
    simpa [a,Store.ofState,initial,BitRAMState.renameTapes,Function.comp_def] using h
  obtain ⟨b,eb,bt,bf,b31⟩ := clear_end 290 input tape x.bits xo a a290
  obtain ⟨c,ec,ct,cf,c31⟩ := clear_end 291 input tape y.bits yo b
    ((bf.tapes 291 (by decide)).trans a291)
  let t := Store.ofState (c.val.setRegister 2 (c.val.registers 31 && c.val.registers 31))
  have et := Executes.bitAnd input tape c 2 31 31
  have hbits : x.bits = y.bits ↔ x = y := by
    constructor
    · intro h
      simpa only [addressValue_bits] using congrArg addressValue h
    · rintro rfl; rfl
  refine ⟨cost+1+((6*x.bits.length+6)+((6*y.bits.length+6)+2)),t,by omega,
    ea.seq (eb.seq (ec.seq et)),?_,?_,?_,?_⟩
  · simp only [t,Store.ofState,BitRAMState.setRegister,Function.update_self,Bool.and_self,
      c31,b31,a31,beq_iff_eq,hbits]
  · simp [t,Store.ofState,BitRAMState.setRegister,ct,bt]
  · simp [t,Store.ofState,BitRAMState.setRegister,ct]
  · have last : BinaryPrecision.Frame {290,291} c.val t.val :=
      ⟨rfl,rfl,rfl,rfl,rfl,fun _ _ => rfl⟩
    exact (af.trans ((bf.mono (b := {290,291}) (by decide)).trans
      (cf.mono (b := {290,291}) (by decide)))).trans last

end Maxwell.Cost.PhysicalMaterial.Membership
