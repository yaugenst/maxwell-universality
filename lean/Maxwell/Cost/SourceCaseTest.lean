import Maxwell.Cost.MagnitudeMax.Zero
import Maxwell.Cost.BinaryPrecision
import Mathlib.Data.Nat.Size

/-! A shared source encoder test: zero RHS or at most one sparse entry.
It reads the actual count word and restores its head exactly. -/
namespace Maxwell.Cost.SourceCaseTest
open Structured RationalAccumulator

def code : Code := .seq (.atom (.tapeRight 79))
  (.seq (.atom (.readTape 79 1000 1001)) (.seq (.atom (.tapeLeft 79))
    (.seq (.atom (.bitNot 1002 90)) (.seq (.atom (.bitAnd 1003 1002 1001))
      (.atom (.bitNot 1004 1003))))))

theorem executes (n : ℕ) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hw : Word s.val 79 n) :
    ∃t,Executes input tape code 13 s t ∧
      t.val.registers 1004=(s.val.registers 90 || decide (n≤1)) ∧
      BinaryPrecision.Frame ∅ s.val t.val ∧ t.val.registers 90=s.val.registers 90 := by
  let a:=Store.ofState (s.val.setTape 79 {s.val.tapes 79 with head:=(s.val.tapes 79).head+1})
  let b:=Store.ofState (readTapeState a.val 79 1000 1001)
  let c:=Store.ofState (b.val.setTape 79 {b.val.tapes 79 with head:=(b.val.tapes 79).head-1})
  let d:=Store.ofState (c.val.setRegister 1002 (!c.val.registers 90))
  let e:=Store.ofState (d.val.setRegister 1003 (d.val.registers 1002 && d.val.registers 1001))
  let t:=Store.ofState (e.val.setRegister 1004 (!e.val.registers 1003))
  have ea : Executes input tape (.atom (.tapeRight 79)) 2 s a := Executes.tapeRight _ _ _ _
  have eb : Executes input tape (.atom (.readTape 79 1000 1001)) 3 a b := by
    apply Executes.atom (extra:=1)
    · simp [BitRAM.next,a.property,readTapeState]
    · simp [readTapeState,a.property]
  have ec : Executes input tape (.atom (.tapeLeft 79)) 2 b c := Executes.tapeLeft _ _ _ _
  have ed : Executes input tape (.atom (.bitNot 1002 90)) 2 c d := Executes.bitNot _ _ _ _ _
  have ee : Executes input tape (.atom (.bitAnd 1003 1002 1001)) 2 d e := Executes.bitAnd _ _ _ _ _ _
  have et : Executes input tape (.atom (.bitNot 1004 1003)) 2 e t := Executes.bitNot _ _ _ _ _
  have tapes : t.val.tapes=s.val.tapes := by
    funext i
    by_cases hi : i=79
    · subst i
      simp [t,e,d,c,b,a,Store.ofState,readTapeState,BitRAMState.setRegister,BitRAMState.setTape]
    · simp [t,e,d,c,b,a,Store.ofState,readTapeState,BitRAMState.setRegister,BitRAMState.setTape]
  obtain ⟨origin,word⟩:=hw
  have small : (!n.bits[1]?.isSome)=decide (n≤1) := by
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.not_eq_true',decide_eq_true_eq]
    rw [Option.isSome_eq_false_iff,Option.isNone_iff_eq_none,List.getElem?_eq_none_iff]
    rw [Nat.size_eq_bits_len,Nat.size_le]
    norm_num
  refine ⟨t,ea.seq (eb.seq (ec.seq (ed.seq (ee.seq et)))),?_,
    ⟨rfl,rfl,rfl,rfl,rfl,fun i _=>congrFun tapes i⟩,?_⟩
  · simp [t,e,d,c,b,a,Store.ofState,readTapeState,BitRAMState.setRegister,
      BitRAMState.setTape,word,BitTape.read,BitTape.shifted,Bool.not_and,small]
  · simp [t,e,d,c,b,a,Store.ofState,readTapeState,BitRAMState.setRegister,BitRAMState.setTape]

#print axioms executes
end Maxwell.Cost.SourceCaseTest
