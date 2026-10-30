import Maxwell.Cost.EmitNatural
import Maxwell.Cost.RationalAccumulator.Bank

/-! A natural coordinate is emitted in the signed-integer format by writing
its actual zero sign bit, then its natural word. No temporary integer array
or host-generated bit stream is supplied. -/
namespace Maxwell.Cost.EmitNonnegative
open Structured RationalAccumulator

def code (source : ℕ) : Code :=
  .seq (.atom (.literal 23 false)) (.seq (.atom (.output 23)) (EmitNatural.code source))

theorem executes (source n : ℕ) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hw : Word s.val source n) :
    ∃t,Executes input tape (code source) (20*n.bits.length+28) s t ∧
      t.val.output=(Codec.int (n:ℤ)).reverse++s.val.output ∧ EmitNatural.Frame s t := by
  let a := Store.ofState (s.val.setRegister 23 false)
  let b := Store.ofState {a.val with pc:=1,output:=a.val.registers 23::a.val.output}
  have e0 := Executes.literal input tape s 23 false
  have e1 := Executes.output input tape a 23
  obtain ⟨origin,hw⟩ := hw
  obtain ⟨t,e2,out,frame⟩ := EmitNatural.executes source n origin input tape b hw
  refine ⟨t,?_,?_,frame⟩
  · convert e0.seq (e1.seq e2) using 1 <;> first | rfl | omega
  · rw [out]
    change (Codec.nat n).reverse++false::s.val.output=(Codec.int (n:ℤ)).reverse++s.val.output
    simp [Codec.int,List.reverse_cons,List.append_assoc]

#print axioms executes
end Maxwell.Cost.EmitNonnegative
