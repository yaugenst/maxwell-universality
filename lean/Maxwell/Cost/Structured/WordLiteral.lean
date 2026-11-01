import Maxwell.Cost.Structured.CounterClear
import Maxwell.Cost.BankArray.Common

/-! Replace a finite stored word by a literal natural, charging both old
word cleanup and new writes while preserving every other tape. -/
namespace Maxwell.Cost.Structured.WordLiteral
open RationalAccumulator

def code (target value : ℕ) : Code :=
  .seq (.call (TapeOps.clear target)) (BinaryPrecision.literalCode target value)

theorem executes (target value : ℕ) (input : List Bool) (tape : ℕ→Bool)
    (old : List Bool) (s : Store) (h : BankArray.Word s.val target old) :
    ∃t,Executes input tape (code target value) (6*old.length+10*value.bits.length+11) s t ∧
      Word t.val target value ∧ BinaryPrecision.Frame {target} s.val t.val := by
  obtain ⟨origin,word⟩ := h
  obtain ⟨u,e0,blank,f0⟩ := RuntimeCounter.clear_executes target input tape old origin s word
  obtain ⟨t,e1,out,f1⟩ := BinaryPrecision.literal target value input tape u blank
  refine ⟨t,?_,out,f0.trans f1⟩
  convert e0.seq e1 using 1 <;> first | rfl | omega

#print axioms executes
end Maxwell.Cost.Structured.WordLiteral
