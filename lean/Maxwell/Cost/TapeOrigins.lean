import Maxwell.Cost.Structured.Primitive
import Maxwell.Cost.WordTransfer

/-! Work-tape origins are coordinate choices, not observable machine data.
Translating each tape's cells together with its head preserves every real
instruction and its exact charge. No runtime relocation is performed. -/
namespace Maxwell.Cost
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

def BitTape.translate (offset : ℤ) (t : BitTape):BitTape:=
  ⟨t.head+offset,fun j=>t.cells (j-offset)⟩

@[simp] theorem BitTape.translate_zero (t : BitTape):t.translate 0=t:=by
  cases t;simp [translate]

@[simp] theorem BitTape.translate_read (t : BitTape) (offset : ℤ):
    (t.translate offset).read=t.read:=by simp [translate,read]

theorem BitTape.translate_write (t : BitTape) (offset : ℤ) (symbol : Option Bool):
    (t.write symbol).translate offset=(t.translate offset).write symbol:=by
  cases t with
  | mk head cells =>
    unfold translate write
    congr 1
    funext j
    simp only [Function.update_apply]
    have he : j-offset=head ↔j=head+offset:=by omega
    simp only [he]

@[simp] theorem BitTape.translate_add (t : BitTape) (a b : ℤ):
    (t.translate a).translate b=t.translate (a+b):=by
  cases t with
  | mk head cells =>
    simp only [translate,add_assoc]
    congr 1
    funext j
    exact congrArg cells (by omega)

def BitRAMState.translateTapes (s : BitRAMState) (offset : ℕ→ℤ):BitRAMState:=
  {s with tapes:=fun i=>(s.tapes i).translate (offset i)}

@[simp] theorem BitRAMState.translateTapes_zero (s : BitRAMState):s.translateTapes (fun _=>0)=s:=by
  simp [translateTapes]

@[simp] theorem BitRAMState.translateTapes_inverse (s : BitRAMState) (offset : ℕ→ℤ):
    (s.translateTapes (fun i=>-offset i)).translateTapes offset=s:=by
  simp [translateTapes]

theorem BitRAMState.translateTapes_setTape (s : BitRAMState) (offset : ℕ→ℤ) (i : ℕ) (t : BitTape):
    (s.setTape i t).translateTapes offset=
      (s.translateTapes offset).setTape i (t.translate (offset i)):=by
  simp only [translateTapes,setTape]
  congr 1
  funext j
  by_cases he : j=i <;> simp [he]

theorem BitRAM.next_translateTapes (M : BitRAM) (input : List Bool) (randomTape : ℕ→Bool)
    (offset : ℕ→ℤ) (s t : BitRAMState) (extra : ℕ)
    (step : M.next input randomTape s=some ⟨t,extra⟩):
    M.next input randomTape (s.translateTapes offset)=some ⟨t.translateTapes offset,extra⟩:=by
  cases hi : M.code[s.pc]? with
  | none => simp [BitRAM.next,hi] at step
  | some instruction =>
    cases instruction <;> simp only [BitRAM.next,hi,Option.some.injEq,PricedStep.mk.injEq,reduceCtorEq] at step
    all_goals first | contradiction | obtain ⟨rfl,rfl⟩:=step
    all_goals simp [BitRAM.next,BitRAMState.translateTapes,hi,BitTape.translate_read,
      BitRAMState.setRegister,BitRAMState.setTape]

    case writeTape target register =>
      funext i
      by_cases he : i=target
      · subst i;simp [BitTape.translate_write]
      · simp [he]
    case eraseTape target =>
      funext i
      by_cases he : i=target
      · subst i;simp [BitTape.translate_write]
      · simp [he]
    case tapeLeft target =>
      funext i
      by_cases he : i=target
      · subst i;simp [BitTape.translate,sub_eq_add_neg,add_comm,add_left_comm]
      · simp [he]
    case tapeRight target =>
      funext i
      by_cases he : i=target
      · subst i;simp [BitTape.translate,add_comm,add_left_comm]
      · simp [he]
    case branch => rfl

theorem PricedSteps.translateTapes {M : BitRAM} {input : List Bool} {randomTape : ℕ→Bool}
    {cost : ℕ} {s t : BitRAMState} (run : PricedSteps (M.next input randomTape) cost s t)
    (offset : ℕ→ℤ):
    PricedSteps (M.next input randomTape) cost (s.translateTapes offset) (t.translateTapes offset):=by
  induction run with
  | refl => exact .refl _
  | step head _ tail => exact .step (M.next_translateTapes input randomTape offset _ _ _ head) tail

namespace Structured
def Store.translateTapes (s : Store) (offset : ℕ→ℤ):Store:=⟨s.val.translateTapes offset,s.property⟩

theorem Executes.translateTapes {input : List Bool} {randomTape : ℕ→Bool} {code : Code}
    {cost : ℕ} {s t : Store} (run : Executes input randomTape code cost s t) (offset : ℕ→ℤ):
    Executes input randomTape code cost (s.translateTapes offset) (t.translateTapes offset):=by
  induction run with
  | skip => exact .skip _
  | call body s t cost steps halt =>
    exact .call body (s.translateTapes offset) (t.translateTapes offset) cost (steps.translateTapes offset) halt
  | seq _ _ ih1 ih2 => exact ih1.seq ih2
  | yes test _ ih => exact .yes test ih
  | no test _ ih => exact .no test ih
  | done test => exact .done test
  | more test _ _ ih1 ih2 => exact .more test ih1 ih2
end Structured

#print axioms Structured.Executes.translateTapes
end Maxwell.Cost
