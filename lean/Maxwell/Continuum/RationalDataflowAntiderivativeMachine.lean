import Maxwell.Continuum.RationalDataflowHornerMachine
import Maxwell.Continuum.RationalDataflowFixedWidths
import Maxwell.Continuum.RationalDataflowWordReplace

/-! A reusable finite antiderivative query with its runtime counter restored.
It evaluates x times the coefficient polynomial at x squared. -/
namespace Maxwell.Continuum.RationalDataflow.PartArray
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 2500000
set_option maxRecDepth 32768

theorem horner_protects_saved_count : hornerCode.protectsTape 206=true := by decide

def antiderivativeCode (point target : ℕ) : Code :=
  .seq (WordReplace.code 206 201)
    (.seq (Instruction.binary .mul 2 point point).code
      (.seq hornerCode (Instruction.binary .mul target 0 point).code))

def antiderivativeWidth (n W : ℕ) : ℕ := 2*hornerWidth n (2*W+1)+1

def antiderivativeState {n : ℕ} (a : Table n) (point target : ℕ) (v : ℕ→Parts) : ℕ→Parts :=
  let prepared := (Instruction.binary .mul 2 point point).update v
  let queried := iterate a 1 hornerBody (sumStart prepared 0) n
  (Instruction.binary .mul target 0 point).update queried

def antiderivativeCost (n W wordLength oldLength : ℕ) : ℕ :=
  6*oldLength+15*wordLength+21+operationCost W+
    hornerCost n (2*W+1) wordLength+operationCost (hornerWidth n (2*W+1))

theorem antiderivative_executes {n : ℕ} (a : Table n) (S : Finset ℕ)
    (h0 : 0∈S) (h1 : 1∈S) (h2 : 2∈S) (point target : ℕ)
    (hp : point∈S) (ht : target∈S) (hp0 : point≠0) (hp1 : point≠1) (hp2 : point≠2)
    (W : ℕ) (hW : 1≤W) (hmeta : a.MetadataWidth W)
    (haWidth : ∀ i, (a.get i).Width W) (haValid : ∀ i, (a.get i).Valid)
    (v : ℕ→Parts) (hv : WidthBank S W v) (hgood : Good S v)
    (input : List Bool) (tape : ℕ→Bool) (xs ys : List Bool)
    (hlen : xs.length≤W) (s : Store) (hn : addressValue xs=n)
    (hsaved : BankArray.Word s.val 206 xs) (hcount : BankArray.Word s.val 201 ys)
    (hs : RationalDataflow.Ready S v s) (ha : a.Ready s) :
    ∃ cost t output finalWord,
      Executes input tape (antiderivativeCode point target) cost s t ∧
      cost≤antiderivativeCost n W xs.length ys.length ∧
      RationalDataflow.Ready S output t ∧ a.Ready t ∧
      BankArray.Word t.val 206 xs ∧ BankArray.Word t.val 201 finalWord ∧
      finalWord.length=xs.length ∧ Good S output ∧
      WidthBank S (antiderivativeWidth n W) output ∧
      output target=(reverseHorner a ((v point).mul (v point)) n).mul (v point) ∧
      (∀ i, i≠0 → i≠1 → i≠2 → i≠target → output i=v i) ∧
      output=antiderivativeState a point target v := by
  have outside201 : 201∉workspace S := outside_workspace S 201 (by decide)
  have outside206 : 206∉workspace S := outside_workspace S 206 (by decide)
  obtain ⟨s0,e0,count0,f0⟩ := WordReplace.executes 206 201 (by decide)
    input tape xs ys s hsaved hcount
  have ready0 := hs.wordReplace_frame outside201 f0
  have array0 := ha.copy_frame (Or.inl rfl) f0
  have saved0 : BankArray.Word s0.val 206 xs :=
    BankArray.word_of_eq (f0.2.2.2.2.2.1 206 (by decide)) hsaved
  obtain ⟨origin,count0⟩ := count0
  let pre : Instruction := .binary .mul 2 point point
  have preValid : pre.Valid S := ⟨h2,hp,hp⟩
  obtain ⟨cp,s1,ep,hcp,ready1,fp⟩ := pre.executes S preValid v W hv trivial input tape s0 ready0
  have array1 := array0.arithmetic_frame S fp ready1.2
  have width1 := pre.update_width S preValid v W hv trivial
  have good1 := pre.update_good S preValid v hgood trivial
  have hWW : W≤2*W+1 := by omega
  obtain ⟨ch,s2,bank2,finalWord,eh,hch,ready2,array2,count2,length2,good2,width2,value2,keep2,bankEq⟩ :=
    horner_executes a S h0 h1 h2 (2*W+1) (by omega) (hmeta.mono hWW)
      (fun i => (haWidth i).mono hWW) haValid (pre.update v) width1 good1 input tape xs origin
      (hlen.trans hWW) s1 hn ((fp.tapes 201 outside201).trans count0) ready1 array1
  have point2 : bank2 point=v point := by
    rw [keep2 point hp0 hp1]
    exact Function.update_of_ne hp2 _ _
  have source1 : pre.update v 2=(v point).mul (v point) := by
    simp only [pre,Instruction.update,BinaryOp.eval,Function.update_self]
  let post : Instruction := .binary .mul target 0 point
  have postValid : post.Valid S := ⟨ht,h0,hp⟩
  obtain ⟨cf,t,ef,hcf,ready3,ff⟩ := post.executes S postValid bank2
    (hornerWidth n (2*W+1)) width2 trivial input tape s2 ready2
  have array3 := array2.arithmetic_frame S ff ready3.2
  have saved1 := BankArray.word_of_eq (fp.tapes 206 outside206) saved0
  have saved2 := BankArray.word_of_eq (eh.protectsTape 206 horner_protects_saved_count) saved1
  refine ⟨(6*ys.length+15*xs.length+21)+(cp+(ch+cf)),t,post.update bank2,finalWord,
    e0.seq (ep.seq (eh.seq ef)),?_,ready3,array3,
    BankArray.word_of_eq (ff.tapes 206 outside206) saved2,
    ⟨origin,(ff.tapes 201 outside201).trans count2⟩,length2,
    post.update_good S postValid bank2 good2 trivial,
    post.update_width S postValid bank2 _ width2 trivial,?_,?_,?_⟩
  · unfold antiderivativeCost
    omega
  · simp only [post,Instruction.update,BinaryOp.eval,Function.update_self]
    rw [value2,source1,point2]
  · intro i hi0 hi1 hi2 hit
    change Function.update bank2 target _ i=v i
    rw [Function.update_of_ne hit,keep2 i hi0 hi1]
    exact Function.update_of_ne hi2 _ _
  · rw [bankEq]
    rfl

theorem antiderivativeWidth_polynomial (n W : ℕ) :
    antiderivativeWidth n W≤16*(n+1)*(W+1) := by
  unfold antiderivativeWidth hornerWidth
  nlinarith

theorem antiderivativeCost_polynomial (n W wordLength oldLength : ℕ)
    (hlen : wordLength≤W) (hold : oldLength≤W) :
    antiderivativeCost n W wordLength oldLength≤2^122*(n+1)^3*(W+2)^2 := by
  have hh := hornerCost_polynomial n (2*W+1) wordLength
  have hw : 2*W+1+2≤2*(W+2) := by omega
  have hhs := Nat.pow_le_pow_left hw 2
  have hcost : 2^112*(n+1)^3*(2*W+1+2)^2≤2^114*(n+1)^3*(W+2)^2 := by
    have hm := Nat.mul_le_mul_left (2^112*(n+1)^3) hhs
    nlinarith only [hm]
  have hwh : hornerWidth n (2*W+1)+3≤8*(n+1)*(W+2) := by unfold hornerWidth; nlinarith
  have hw2 := Nat.pow_le_pow_left hwh 2
  have hp : 1≤(n+1)^3 := one_le_pow₀ (by omega)
  have hn : (n+1)^2≤(n+1)^3 := Nat.pow_le_pow_right (by omega) (by decide)
  have hn1 : n+1≤(n+1)^3 := le_self_pow₀ (by omega) (by decide : (3:ℕ)≠0)
  have hW2 : W+3≤2*(W+2) := by omega
  have hs := Nat.pow_le_pow_left hW2 2
  have hb : 1≤(W+2)^2 := one_le_pow₀ (by omega)
  have hbW : W≤(W+2)^2 := by nlinarith
  have hfinal : operationCost (hornerWidth n (2*W+1))≤2^106*(n+1)^3*(W+2)^2 := by
    unfold operationCost
    have hm := Nat.mul_le_mul_right (2^106*(W+2)^2) hn
    nlinarith only [hw2,hm]
  have hfirst : operationCost W≤2^102*(n+1)^3*(W+2)^2 := by
    unfold operationCost
    have hm := Nat.mul_le_mul_right (2^102*(W+2)^2) hp
    nlinarith only [hs,hm]
  have hcounter : (n+1)*(13*wordLength+15)+6*oldLength+15*wordLength+21≤
      70*(n+1)^3*(W+2)^2 := by
    have hmul := Nat.mul_le_mul hn1 (show 13*wordLength+15≤28*(W+2)^2 by nlinarith)
    have hmul2 := Nat.mul_le_mul_right ((W+2)^2) hp
    nlinarith only [hmul,hmul2,hlen,hold,hbW,hb]
  unfold antiderivativeCost
  nlinarith only [hh,hcost,hfirst,hfinal,hcounter,Nat.zero_le ((n+1)^3*(W+2)^2)]

#print axioms antiderivative_executes
#print axioms antiderivativeCost_polynomial
end Maxwell.Continuum.RationalDataflow.PartArray
