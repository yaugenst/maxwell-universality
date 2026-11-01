import Maxwell.Cost.Structured.WordDifference
import Maxwell.Continuum.SourceRoutingPathRestore
import Maxwell.Continuum.SourceRoutingGeometryDivisionBounds

/-! Count an emitted path from its saved and current cursors. The reserved
header contributes one word, and every point contributes three words. -/
namespace Maxwell.Cost.RoutingPorts.Complete.GeometryPath
open Structured GeometryArithmetic
open RationalAccumulator (Word Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 1800000

def headerCountCode : Code := .seq (WordDifference.code 1253 1256 1230)
  (.seq (NatAssign.code [.literal 1231 3]) (divisionCode 1230 1231 1232 1233))

def headerCountValues (v : ℕ→ℕ) (start next : ℕ) : ℕ→ℕ :=
  divided (Function.update (Function.update v 1230 (next-start)) 1231 3) 1230 1231 1232 1233

theorem headerCount_width (v : ℕ→ℕ) (start next B : ℕ) (large : 2 ≤ B)
    (width : ∀j∈ids,(v j).bits.length ≤ B) (nextWidth : next.bits.length ≤ B) :
    ∀j∈ids,(headerCountValues v start next j).bits.length ≤ B := by
  apply divided_width _ 1230 1231 1232 1233 B (by decide)
  intro j hj
  by_cases h31 : j=1231
  · subst j
    simpa only [Function.update_self,show (3 : ℕ).bits.length=2 from rfl] using large
  by_cases h30 : j=1230
  · subst j
    simpa only [Function.update_of_ne (by decide : (1230 : ℕ)≠1231),Function.update_self] using
      (Maxwell.Continuum.RationalWords.bits_mono (Nat.sub_le next start)).trans nextWidth
  simpa only [Function.update_of_ne h31,Function.update_of_ne h30] using width j hj

theorem headerCount_other (v : ℕ→ℕ) (start next j : ℕ)
    (h30 : j≠1230) (h31 : j≠1231) (h32 : j≠1232) (h33 : j≠1233) :
    headerCountValues v start next j=v j := by
  simp only [headerCountValues,divided,Function.update_of_ne h33,Function.update_of_ne h32,
    Function.update_of_ne h31,Function.update_of_ne h30]

theorem headerCount_value (v : ℕ→ℕ) (start length : ℕ) :
    headerCountValues v start (start+1+3*length) 1232=length := by
  simp only [headerCountValues,divided,Function.update_of_ne (by decide : (1232 : ℕ)≠1233),
    Function.update_self,Function.update_of_ne (by decide : (1230 : ℕ)≠1231)]
  omega

theorem headerCount_executes (v : ℕ→ℕ) (start next B : ℕ) (ordered : start ≤ next)
    (large : 2 ≤ B) (width : ∀j∈ids,(v j).bits.length ≤ B)
    (startWidth : start.bits.length ≤ B) (nextWidth : next.bits.length ≤ B)
    (zero : ∀j∈Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,v j=0)
    (blankTarget : v 1230=0) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank ids v s.val) (ready : GeometryArray.Ready s.val)
    (privateBlank : Blank s.val 1249) (startWord : Word s.val 1256 start)
    (nextWord : Word s.val 1253 next) :
    ∃steps t,Executes input tape headerCountCode steps s t ∧ steps ≤ 2^103*(B+2)^2 ∧
      NatAssign.Bank ids (headerCountValues v start next) t.val ∧ GeometryArray.Ready t.val ∧
      Blank t.val 1249 ∧ BinaryPrecision.Frame work s.val t.val := by
  let v₀:=Function.update v 1230 (next-start)
  let v₁:=Function.update v₀ 1231 3
  have w₀ : ∀j∈ids,(v₀ j).bits.length ≤ B := by
    intro j hj
    by_cases same : j=1230
    · subst j
      exact (Maxwell.Continuum.RationalWords.bits_mono (Nat.sub_le next start)).trans nextWidth
    · simpa only [v₀,Function.update_of_ne same] using width j hj
  have w₁ : ∀j∈ids,(v₁ j).bits.length ≤ B := by
    intro j hj
    by_cases same : j=1231
    · subst j
      simpa only [v₁,Function.update_self,show (3 : ℕ).bits.length=2 from rfl] using large
    · simpa only [v₁,Function.update_of_ne same] using w₀ j hj
  obtain ⟨c₀,a,e₀,h₀,wa,sa,f₀⟩:=WordDifference.executes 1253 1256 1230
    (by decide) (by decide) (by decide) input tape next start ordered s nextWord startWord
    ((RationalAccumulator.zero_word_iff_blank _ _).mp (by simpa only [blankTarget] using bank 1230 (by decide)))
    (scratch ready)
  have ba : NatAssign.Bank ids v₀ a.val := by
    intro j hj
    by_cases same : j=1230
    · subst j;exact wa
    · change Word a.val j (Function.update v 1230 (next-start) j)
      rw [Function.update_of_ne same]
      exact RationalAccumulator.word_of_eq (f₀.tapes j (by
        simp only [Finset.mem_insert,Finset.mem_singleton]
        have h:=ids_lower j hj
        omega)) (bank j hj)
  have fa : BinaryPrecision.Frame work s.val a.val:=f₀.mono (by decide)
  have za:=ready_of_frame ready sa fa
  obtain ⟨c₁,b,e₁,h₁,bb,zb,f₁⟩:=stage [.literal 1231 3]
    (by simp [NatAssign.Instruction.Valid,ids,controls]) v₀ B w₀
    (by simp [NatAssign.Instruction.literalWidth];exact large) input tape a ba za
  have bb' : NatAssign.Bank ids v₁ b.val := by
    simpa only [NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,
      NatAssign.Instruction.value] using bb
  have fb : BinaryPrecision.Frame work a.val b.val := f₁.mono (by
    intro j hj
    simp only [work,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hj ⊢
    tauto)
  have z₁ : ∀j∈Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,v₁ j=0 := by
    intro j hj
    have small : j<1200 := by
      simp only [Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,
        Finset.mem_insert,Finset.mem_singleton] at hj
      omega
    simpa only [v₁,v₀,Function.update_of_ne (show j≠1231 by omega),
      Function.update_of_ne (show j≠1230 by omega)] using zero j hj
  obtain ⟨c₂,t,e₂,h₂,bt,zt,pt,f₂⟩:=divide 1230 1231 1232 1233
    (by decide) (by decide) (by decide) (by decide) (by decide) v₁ z₁ (by simp [v₁]) B w₁
    input tape b bb' zb (RationalAccumulator.blank_of_eq ((f₁.tapes 1249 (by decide)).trans
      (f₀.tapes 1249 (by decide))) privateBlank)
  refine ⟨_,t,e₀.seq (e₁.seq e₂),?_,bt,zt,pt,(fa.trans fb).trans f₂⟩
  change c₁ ≤ 3000*8^1*(B+2)^2 at h₁
  nlinarith only [h₀,h₁,h₂,startWidth,nextWidth]

#print axioms headerCount_executes
end Maxwell.Cost.RoutingPorts.Complete.GeometryPath
