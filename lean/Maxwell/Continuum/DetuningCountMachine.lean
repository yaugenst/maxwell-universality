import Maxwell.Cost.Structured.NatAssign.Clog
import Maxwell.Continuum.Detuning

/-! Compute the draw count and dyadic precision from the actual source size,
spectral count and retained detuning denominator. -/
namespace Maxwell.Continuum.DetuningMachine
open Maxwell.Cost Maxwell.Cost.Structured
open RationalAccumulator (Word Blank)
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

def localIds : Finset ℕ := Finset.Icc 4500 4541
def ids : Finset ℕ := localIds∪{2211,2237,2245}
def workspace : Finset ℕ := {0,1,2,3}∪localIds
def prepare : List NatAssign.Instruction :=
  [.literal 4500 64,.copy 2211 4501,.multiply 2245 4501,.multiply 4500 4501]
def finishCount : List NatAssign.Instruction :=
  [.copy 4503 4540,.literal 4541 0,.literal 4508 1,
   .copy 4505 4506,.add 4503 4506,.add 4508 4506]
def prepared (v : ℕ→ℕ) : ℕ→ℕ := NatAssign.values prepare v
def counted (v : ℕ→ℕ) : ℕ→ℕ := NatAssign.clogValues (prepared v) 4501 4502 4503
def countedTau (v : ℕ→ℕ) : ℕ→ℕ := NatAssign.clogValues (counted v) 2237 4504 4505
def countValues (v : ℕ→ℕ) : ℕ→ℕ := NatAssign.values finishCount (countedTau v)
def countCode : Code := .seq (NatAssign.code prepare)
  (.seq (NatAssign.clogCode 4501 4502 4503)
    (.seq (NatAssign.clogCode 2237 4504 4505) (NatAssign.code finishCount)))
def prepareWidth (B : ℕ) : ℕ := 2^prepare.length*(B+8)
def countWidth (B : ℕ) : ℕ := 2^finishCount.length*(prepareWidth B+2)
def countCost (B : ℕ) : ℕ := 3000*8^prepare.length*(B+9)^2+
  (NatAssign.clogCost (prepareWidth B)+
    (NatAssign.clogCost (prepareWidth B)+3000*8^finishCount.length*(prepareWidth B+3)^2))

theorem ids_ge : ∀i∈ids,4 ≤ i := by simp [ids,localIds];omega
theorem prepare_valid : ∀a∈prepare,a.Valid ids := by
  simp [prepare,NatAssign.Instruction.Valid,ids,localIds]
theorem finishCount_valid : ∀a∈finishCount,a.Valid ids := by
  simp [finishCount,NatAssign.Instruction.Valid,ids,localIds]
theorem prepared_fields (v : ℕ→ℕ) : prepared v 4501=64*v 2211*v 2245 ∧
    prepared v 2237=v 2237 := by
  simp [prepared,prepare,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.value,NatAssign.Instruction.target]
  ring
theorem counted_fields (v : ℕ→ℕ) : counted v 4503=Detuning.randomBits (v 2211) (v 2245) ∧
    counted v 2237=v 2237 := by
  simp [counted,NatAssign.clogValues,prepared_fields v,Detuning.randomBits]
theorem countValues_fields (v : ℕ→ℕ) :
    countValues v 4540=Detuning.randomBits (v 2211) (v 2245) ∧ countValues v 4541=0 ∧
    countValues v 4503=Detuning.randomBits (v 2211) (v 2245) ∧
    countValues v 4506=Nat.clog 2 (v 2237)+Detuning.randomBits (v 2211) (v 2245)+1 := by
  simp [countValues,finishCount,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.value,NatAssign.Instruction.target,countedTau,NatAssign.clogValues,
    (counted_fields v).1,(counted_fields v).2]
  omega

theorem count_executes (v : ℕ→ℕ) (B : ℕ) (width : ∀i∈ids,(v i).bits.length≤B)
    (hm : 0<v 2211) (hN : 0<v 2245) (hden : 0<v 2237)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank ids v s.val) (scratch : NatAssign.Scratch s.val) :
    ∃cost t,Executes input tape countCode cost s t ∧ cost≤countCost B ∧
      NatAssign.Bank ids (countValues v) t.val ∧ NatAssign.Scratch t.val ∧
      (∀i∈ids,(countValues v i).bits.length≤countWidth B) ∧
      BinaryPrecision.Frame workspace s.val t.val := by
  obtain ⟨c0,a,e0,h0,ba,sa,f0⟩ := NatAssign.executes ids ids_ge prepare prepare_valid v
    input tape s bank scratch
  have w0 : ∀i∈ids,(prepared v i).bits.length ≤ prepareWidth B := by
    intro i hi
    have h := NatAssign.values_width ids prepare prepare_valid v (B+7)
      (fun i hi=>(width i hi).trans (by omega))
      (by simp [prepare,NatAssign.Instruction.literalWidth,
        show (64:ℕ).bits.length=7 by decide]) i hi
    exact (Nat.le_add_right _ 1).trans h
  have pos : 0<prepared v 4501 := by rw [(prepared_fields v).1];positivity
  obtain ⟨c1,b,e1,h1,bb,sb,w1,_,f1⟩ := NatAssign.clog_executes ids 4501 4502 4503 ids_ge
    (by decide) (by decide) (by decide) (by decide) (by decide) (prepared v) (prepareWidth B)
    pos w0 input tape a ba sa
  obtain ⟨c2,c,e2,h2,bc,sc,w2,_,f2⟩ := NatAssign.clog_executes ids 2237 4504 4505 ids_ge
    (by decide) (by decide) (by decide) (by decide) (by decide) (counted v) (prepareWidth B)
    (by simpa only [(counted_fields v).2] using hden) w1 input tape b bb sb
  obtain ⟨c3,t,e3,h3,bt,st,f3⟩ := NatAssign.executes ids ids_ge finishCount finishCount_valid
    (countedTau v) input tape c bc sc
  have h0' : c0≤3000*8^prepare.length*(B+9)^2 := by
    apply h0.trans
    exact NatAssign.price_bound ids prepare prepare_valid v (B+7)
      (fun i hi=>(width i hi).trans (by omega))
      (by simp [prepare,NatAssign.Instruction.literalWidth,
        show (64:ℕ).bits.length=7 by decide])
  have h3' : c3≤3000*8^finishCount.length*(prepareWidth B+3)^2 := by
    apply h3.trans
    exact NatAssign.price_bound ids finishCount finishCount_valid (countedTau v) (prepareWidth B+1)
      (fun i hi=>(w2 i hi).trans (by omega))
      (by simp [finishCount,NatAssign.Instruction.literalWidth])
  refine ⟨c0+(c1+(c2+c3)),t,e0.seq (e1.seq (e2.seq e3)),
    Nat.add_le_add h0' (Nat.add_le_add h1 (Nat.add_le_add h2 h3')),bt,st,?_,?_⟩
  · intro i hi
    have h := NatAssign.values_width ids finishCount finishCount_valid (countedTau v)
      (prepareWidth B+1) (fun i hi=>(w2 i hi).trans (by omega))
      (by simp [finishCount,NatAssign.Instruction.literalWidth]) i hi
    exact (Nat.le_add_right _ 1).trans h
  · exact (f0.mono (by decide+kernel)).trans ((f1.mono (by decide+kernel)).trans
      ((f2.mono (by decide+kernel)).trans (f3.mono (by decide+kernel))))

#print axioms count_executes
end Maxwell.Continuum.DetuningMachine
