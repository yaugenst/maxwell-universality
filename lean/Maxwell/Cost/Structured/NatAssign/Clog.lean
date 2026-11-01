import Maxwell.Cost.Structured.NatAssign.WordLength
import Maxwell.Cost.Structured.NatAssign.BankFrame
import Maxwell.Cost.PhysicalMaterial.FixedSubtract
import Maxwell.Codec.NaturalLength

/-! Compute the binary ceiling logarithm by copying the source, subtracting
one, and scanning its actual binary length. The source bank is retained. -/
namespace Maxwell.Cost.Structured.NatAssign
open RationalAccumulator (Word Blank)

def clogCode (source work target : ℕ) : Code :=
  .seq (code [.copy source work,.literal target 0])
    (.seq (PhysicalMaterial.FixedSubtract.code work 1) (WordLength.code work target))
def clogValues (v : ℕ→ℕ) (source work target : ℕ) : ℕ→ℕ :=
  Function.update (Function.update v work (v source-1)) target (Nat.clog 2 (v source))
def clogCost (B : ℕ) : ℕ := 3000*8^2*(B+2)^2+(1+(29*B+30)+(48*(B+1)^2+1))

theorem clog_executes (ids : Finset ℕ) (source work target : ℕ)
    (lower : ∀i∈ids,4 ≤ i) (hs : source∈ids) (hw : work∈ids) (ht : target∈ids)
    (hsw : source≠work) (hwt : work≠target)
    (v : ℕ→ℕ) (B : ℕ) (positive : 0<v source) (width : ∀i∈ids,(v i).bits.length≤B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : Bank ids v s.val) (scratch : Scratch s.val) :
    ∃cost t,Executes input tape (clogCode source work target) cost s t ∧ cost≤clogCost B ∧
      Bank ids (clogValues v source work target) t.val ∧ Scratch t.val ∧
      (∀i∈ids,(clogValues v source work target i).bits.length≤B) ∧
      Word t.val target (Nat.clog 2 (v source)) ∧
      BinaryPrecision.Frame {0,1,2,3,work,target} s.val t.val := by
  let xs : List Instruction := [.copy source work,.literal target 0]
  have valid : ∀q∈xs,q.Valid ids := by simp [xs,Instruction.Valid,hs,hw,ht,hsw]
  have literals : ∀q∈xs,q.AssignmentBound B := by simp [xs,Instruction.AssignmentBound]
  obtain ⟨c0,a,e0,h0,ba,sa,f0⟩ := executes ids lower xs valid v input tape s bank scratch
  have wa := values_assignment_width ids xs valid v B width literals
  have assign : values xs v=Function.update (Function.update v work (v source)) target 0 := rfl
  let va := values xs v
  have aw : Word a.val work (v source) := by
    simpa only [assign,Function.update_of_ne hwt,Function.update_self] using ba work hw
  obtain ⟨c1,b,e1,h1,bw,f1⟩ := PhysicalMaterial.FixedSubtract.executes work 1 (v source)
    (by omega) input tape a aw
  let vb := Function.update va work (v source-1)
  have bb : Bank ids vb b.val := by
    intro i hi
    by_cases same : i=work
    · subst i;simpa only [vb,Function.update_self] using bw
    · simpa only [vb,Function.update_of_ne same] using
        RationalAccumulator.word_of_eq (f1.tapes i (by simpa using same)) (ba i hi)
  have sb : Scratch b.val := by
    intro i hi
    exact RationalAccumulator.blank_of_eq (f1.tapes i (by simp;have := lower work hw;omega)) (sa i hi)
  have subWidth : (v source-1).bits.length≤B := by
    have h := Nat.size_le_size (Nat.sub_le (v source) 1)
    rw [←Nat.size_eq_bits_len,←Nat.size_eq_bits_len] at h
    exact h.trans (width source hs)
  have wb : ∀i∈ids,(vb i).bits.length≤B := by
    intro i hi
    by_cases same : i=work
    · subst i;simpa only [vb,Function.update_self] using subWidth
    · simpa only [vb,Function.update_of_ne same] using wa i hi
  have zero : vb target=0 := by simp [vb,va,assign,Ne.symm hwt]
  obtain ⟨c2,t,e2,h2,bt,st,wt,f2⟩ := wordLength_executes ids work target B hw ht hwt (lower target ht)
    vb zero wb input tape b bb sb
  have log : (v source-1).bits.length=Nat.clog 2 (v source) := by
    rw [←Codec.clog_two_succ,Nat.sub_add_cancel positive]
  have result : Function.update vb target (vb work).bits.length=clogValues v source work target := by
    funext i
    by_cases same : i=target
    · subst i;simp [vb,clogValues,log]
    · by_cases isWork : i=work
      · subst i;simp [vb,clogValues,hwt]
      · simp [vb,va,assign,clogValues,same,isWork]
  rw [result] at bt wt
  have firstCost : c0≤3000*8^2*(B+2)^2 := by
    have hp := price_bound ids xs valid v B width (by simp [xs,Instruction.literalWidth])
    exact h0.trans (by simpa only [xs,List.length_cons,List.length_nil] using hp)
  have secondCost : c1≤1+(29*B+30) := h1.trans (by
    unfold PhysicalMaterial.FixedSubtract.costBound
    have := width source hs
    omega)
  refine ⟨c0+(c1+c2),t,e0.seq (e1.seq e2),Nat.add_le_add firstCost (Nat.add_le_add secondCost h2),
    bt,st,wt,?_,?_⟩
  · simpa only [clogValues,Function.update_self] using bt target ht
  · apply (f0.mono ?_).trans ((f1.mono ?_).trans (f2.mono ?_))
    · simp [changes,xs,Instruction.target,Finset.subset_iff]
    · simp [Finset.subset_iff]
    · simp [Finset.subset_iff]

#print axioms clog_executes
end Maxwell.Cost.Structured.NatAssign
