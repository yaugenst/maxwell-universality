import Maxwell.Continuum.StoredSourceAmplitude
import Maxwell.Continuum.RationalDataflowIntegerEmit
import Maxwell.Continuum.StoredBitPayload

/-! The dyadic source coefficient and common template are emitted from
their actual stored words, with all input heads restored. -/
namespace Maxwell.Continuum.SourcePayload
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalDataflow
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384

def emitCode : Code := .seq (EmitNatural.code 4427)
  (.seq (IntegerEmit.code 0) (StoredBitPayload.code 992))
def payloadBits (P : ℕ) (z : ℤ) (template : List Bool) : List Bool :=
  Codec.nat P++Codec.int z++template

theorem emit_executes (P : ℕ) (z : ℤ) (template input : List Bool) (tape : ℕ→Bool)
    (s : Store) (precision : Word s.val 4427 P)
    (positive : Word s.val (positivePort 0) z.toNat)
    (negative : Word s.val (negativePort 0) (-z).toNat)
    (stored : BankArray.Word s.val 992 template) :
    ∃t,Executes input tape emitCode
      (20*(P.bits.length+z.natAbs.bits.length)+10*template.length+64) s t ∧
      t.val.output=(payloadBits P z template).reverse++s.val.output ∧ EmitNatural.Frame s t := by
  obtain ⟨po,pw⟩:=precision
  obtain ⟨a,e0,o0,f0⟩:=EmitNatural.executes 4427 P po input tape s pw
  obtain ⟨b,e1,o1,f1⟩:=IntegerEmit.executes 0 z input tape a
    (word_of_eq (congrFun f0.2.2.2.2 _) positive)
    (word_of_eq (congrFun f0.2.2.2.2 _) negative)
  have storedB:=BankArray.word_of_eq (congrFun (f1.2.2.2.2.trans f0.2.2.2.2) 992) stored
  obtain ⟨origin,word⟩:=storedB
  obtain ⟨t,e2,o2,f2⟩:=StoredBitPayload.executes 992 template origin input tape b word
  refine ⟨t,?_,?_,⟨f2.1.trans (f1.1.trans f0.1),f2.2.1.trans (f1.2.1.trans f0.2.1),
    f2.2.2.1.trans (f1.2.2.1.trans f0.2.2.1),
    f2.2.2.2.1.trans (f1.2.2.2.1.trans f0.2.2.2.1),
    f2.2.2.2.2.trans (f1.2.2.2.2.trans f0.2.2.2.2)⟩⟩
  · convert e0.seq (e1.seq e2) using 1 <;> first | rfl | omega
  · rw [o2,o1,o0]
    simp only [payloadBits,List.reverse_append,List.append_assoc]

#print axioms emit_executes
end Maxwell.Continuum.SourcePayload
