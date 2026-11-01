import Maxwell.Continuum.ContinuumDecoderSelectorPlan

namespace Maxwell.Continuum.DecoderSelectors
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def arithmeticWidth (B : ℕ):=2^plan.length*(B+1)
def costBound (B : ℕ):=3000*8^plan.length*(B+2)^2+
  (NatAssign.clogCost (arithmeticWidth B)+24000*(arithmeticWidth B+2)^2)

theorem executes (v : ℕ→ℕ) (B : ℕ) (hB : 10≤B)
    (width : ∀i∈ids,(v i).bits.length≤B)
    (hm : 0<v 501) (hN : 0<v 2245) (htau : 0<v 2237)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank ids v s.val) (scratch : NatAssign.Scratch s.val) :
    ∃cost t,Executes input tape code cost s t ∧ cost≤costBound B ∧
      NatAssign.Bank ids (result v) t.val ∧ NatAssign.Scratch t.val ∧
      (∀i∈ids,(result v i).bits.length≤2*(arithmeticWidth B+1)) ∧
      BinaryPrecision.Frame ({0,1,2,3}∪outputs) s.val t.val:=by
  obtain ⟨c0,a,e0,h0,ba,sa,f0⟩:=NatAssign.executes ids ids_lower plan valid v input tape s bank scratch
  have wa : ∀i∈ids,(value v i).bits.length≤arithmeticWidth B:=by
    intro i hi
    have hh:=NatAssign.values_width ids plan valid v B width (fun q hq=>(literals q hq).trans hB) i hi
    change (value v i).bits.length+1≤arithmeticWidth B at hh
    omega
  have positive : 0<value v 4700:=by rw [(values v).1];positivity
  obtain ⟨c1,b,e1,h1,bb,sb,wb,_,f1⟩:=NatAssign.clog_executes ids 4700 4710 4701 ids_lower
    (by decide) (by decide) (by decide) (by decide) (by decide) (value v) (arithmeticWidth B)
    positive wa input tape a ba sa
  have finishValid : ∀q∈[NatAssign.Instruction.add 4713 4701],q.Valid ids:=by
    simp [NatAssign.Instruction.Valid,ids,inputs,outputs]
  obtain ⟨c2,t,e2,h2,bt,st,f2⟩:=NatAssign.executes ids ids_lower [.add 4713 4701] finishValid
    (NatAssign.clogValues (value v) 4700 4710 4701) input tape b bb sb
  have bound0:=h0.trans (NatAssign.price_bound ids plan valid v B width (fun q hq=>(literals q hq).trans hB))
  have bound2:=h2.trans (NatAssign.price_bound ids [.add 4713 4701] finishValid _ (arithmeticWidth B)
    wb (by simp [NatAssign.Instruction.literalWidth]))
  change c2≤24000*(arithmeticWidth B+2)^2 at bound2
  refine ⟨c0+(c1+c2),t,e0.seq (e1.seq e2),Nat.add_le_add bound0 (Nat.add_le_add h1 bound2),bt,st,?_,?_⟩
  · intro i hi
    have hh:=NatAssign.values_width ids [.add 4713 4701] finishValid _ (arithmeticWidth B)
      wb (by simp [NatAssign.Instruction.literalWidth]) i hi
    change (result v i).bits.length+1≤2*(arithmeticWidth B+1) at hh
    omega
  · apply (f0.mono ?_).trans ((f1.mono (by decide)).trans (f2.mono ?_))
    · decide
    · decide

#print axioms executes
end Maxwell.Continuum.DecoderSelectors
