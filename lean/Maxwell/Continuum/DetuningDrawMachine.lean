import Maxwell.Continuum.DetuningCountMachine
import Maxwell.Cost.RandomNatMachine
import Maxwell.Cost.Structured.TapeBlockSwap
import Maxwell.Cost.IndexedAddress

/-! Read the computed number of fair bits and form the dyadic midpoint's
integer numerator. The code and tape permutation are fixed. -/
namespace Maxwell.Continuum.DetuningMachine
open Maxwell.Cost Maxwell.Cost.Structured
open RationalAccumulator (Word Blank)
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

def drawRelocation : Equiv.Perm ℕ := TapeBlockSwap.permutation 240 2 4300 (by decide)
def finishDraw : List NatAssign.Instruction :=
  [.literal 4507 2,.copy 4541 4510,.multiply 4507 4510,.add 4508 4510]
def sampled (v : ℕ→ℕ) (j : ℕ) : ℕ→ℕ := Function.update (Function.update v 4540 0) 4541 j
def drawValues (v : ℕ→ℕ) (j : ℕ) : ℕ→ℕ := NatAssign.values finishDraw (sampled v j)
def drawCode : Code := .seq (RandomNatMachine.codeOn drawRelocation) (NatAssign.code finishDraw)
def drawWidth (n B : ℕ) : ℕ := 2^finishDraw.length*(B+n+3)
def drawCost (n B : ℕ) : ℕ := RandomNatMachine.costBound n+1+
  3000*8^finishDraw.length*(B+n+4)^2

theorem finishDraw_valid : ∀a∈finishDraw,a.Valid ids := by
  simp [finishDraw,NatAssign.Instruction.Valid,ids,localIds]
theorem drawValues_fields (v : ℕ→ℕ) (j : ℕ) (one : v 4508=1) :
    drawValues v j 4510=2*j+1 ∧ drawValues v j 4506=v 4506 ∧
    drawValues v j 4541=j := by
  simp [drawValues,finishDraw,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.value,NatAssign.Instruction.target,sampled,one]
  omega

theorem draw_executes (v : ℕ→ℕ) (n B : ℕ) (width : ∀i∈ids,(v i).bits.length≤B)
    (count : v 4540=n) (blank : v 4541=0)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank ids v s.val) (scratch : NatAssign.Scratch s.val) :
    let j := addressValue (RandomBitsMachine.bits tape s.val.randomCursor n)
    ∃cost t,Executes input tape drawCode cost s t ∧ cost≤drawCost n B ∧
      NatAssign.Bank ids (drawValues v j) t.val ∧ NatAssign.Scratch t.val ∧
      (∀i∈ids,(drawValues v j i).bits.length≤drawWidth n B) ∧
      t.val.randomCursor=s.val.randomCursor+n ∧
      t.val.address=s.val.address ∧ t.val.inputHead=s.val.inputHead ∧
      t.val.memory=s.val.memory ∧ t.val.output=s.val.output ∧
      (∀i,i∉workspace→t.val.tapes i=s.val.tapes i) := by
  let j := addressValue (RandomBitsMachine.bits tape s.val.randomCursor n)
  have r240 : drawRelocation 240=4540 := by decide
  have r241 : drawRelocation 241=4541 := by decide
  have wc : Word s.val (drawRelocation 240) n := by
    simpa only [r240,count] using bank 4540 (by decide)
  have wb : Blank s.val (drawRelocation 241) := by
    rw [r241]
    apply (RationalAccumulator.zero_word_iff_blank _ _).mp
    simpa only [blank] using bank 4541 (by decide)
  obtain ⟨c0,a,e0,h0,wa,ba,ra,fa⟩ := RandomNatMachine.executes_on drawRelocation input tape n s wc wb
  simp only [r240,r241] at wa ba fa
  have bankA : NatAssign.Bank ids (sampled v j) a.val := by
    intro i hi
    by_cases hi1 : i=4541
    · subst i;simpa only [sampled,Function.update_self] using wa
    · by_cases hi0 : i=4540
      · subst i
        simpa only [sampled,Function.update_self,Function.update_of_ne (by decide : 4540≠4541)] using
          (RationalAccumulator.zero_word_iff_blank _ _).mpr ba
      · simpa only [sampled,Function.update_of_ne hi0,Function.update_of_ne hi1] using
          RationalAccumulator.word_of_eq (fa.tapes i hi0 hi1) (bank i hi)
  have scratchA : NatAssign.Scratch a.val := by
    intro i hi
    exact RationalAccumulator.blank_of_eq (fa.tapes i (by omega) (by omega)) (scratch i hi)
  have jw : j.bits.length≤n := by
    rw [Nat.size_eq_bits_len]
    apply Nat.size_le.mpr
    simpa only [j,RandomBitsMachine.bits,List.length_map,List.length_range] using
      IndexedAddress.value_lt_pow_length (RandomBitsMachine.bits tape s.val.randomCursor n)
  have widthA : ∀i∈ids,(sampled v j i).bits.length≤B+n+2 := by
    intro i hi
    by_cases hi1 : i=4541
    · subst i;simp only [sampled,Function.update_self];omega
    · by_cases hi0 : i=4540
      · subst i;simp [sampled]
      · simpa only [sampled,Function.update_of_ne hi0,Function.update_of_ne hi1] using
          (width i hi).trans (by omega : B≤B+n+2)
  obtain ⟨c1,t,e1,h1,bt,st,ft⟩ := NatAssign.executes ids ids_ge finishDraw finishDraw_valid
    (sampled v j) input tape a bankA scratchA
  have price := NatAssign.price_bound ids finishDraw finishDraw_valid (sampled v j) (B+n+2)
    widthA (by simp [finishDraw,NatAssign.Instruction.literalWidth,
      show (2:ℕ).bits.length=2 by decide])
  refine ⟨c0+c1,t,e0.seq e1,Nat.add_le_add h0 (h1.trans price),bt,st,?_,
    ft.randomCursor.trans ra,ft.address.trans fa.address,ft.inputHead.trans fa.inputHead,
    ft.memory.trans fa.memory,ft.output.trans fa.output,?_⟩
  · intro i hi
    have h := NatAssign.values_width ids finishDraw finishDraw_valid (sampled v j) (B+n+2)
      widthA (by simp [finishDraw,NatAssign.Instruction.literalWidth,
        show (2:ℕ).bits.length=2 by decide]) i hi
    exact (Nat.le_add_right _ 1).trans h
  · intro i hi
    have low : i≠4540 ∧ i≠4541 := by
      simp only [workspace,localIds,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,
        Finset.mem_Icc,not_or] at hi
      omega
    exact (ft.tapes i (fun h=>hi ((show NatAssign.changes finishDraw⊆workspace by decide+kernel) h))).trans
      (fa.tapes i low.1 low.2)

#print axioms draw_executes
end Maxwell.Continuum.DetuningMachine
