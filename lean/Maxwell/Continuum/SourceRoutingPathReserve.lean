import Maxwell.Continuum.SourceRoutingPathReverseFooter

namespace Maxwell.Cost.RoutingPorts.Complete.GeometryPath
open Structured GeometryArithmetic
open RationalAccumulator (Word Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 1800000

def reserveCode : Code := .seq (loadCode 1253 1256)
  (.seq (loadCode 1253 1234) (.seq (NatAssign.code [.add 1219 1234]) GeometryPathReverse.footerCode))

def reserveWork : Finset ℕ := {1256}∪GeometryPathReverse.footerWork

theorem reserve_executes {q : ℕ} (p : GeometrySort.Plan q) (round index cursor B : ℕ)
    (indexBound : index ≤ q*q) (planBound : p.bound round ≤ B) (cursorBound : cursor.bits.length ≤ B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank ids (GeometrySort.seed p round index) s.val)
    (ready : GeometryArray.Ready s.val) (privateBlank : Blank s.val 1249)
    (cursorWord : Word s.val 1253 cursor) (savedBlank : Blank s.val 1256) :
    ∃steps t,Executes input tape reserveCode steps s t ∧ steps ≤ 2^116*(B+3)^2 ∧
      NatAssign.Bank ids (GeometrySort.seed p round index) t.val ∧ GeometryArray.Ready t.val ∧
      Blank t.val 1249 ∧ Word t.val 1253 (cursor+1) ∧ Word t.val 1256 cursor ∧
      BinaryPrecision.Frame reserveWork s.val t.val := by
  let v:=GeometrySort.seed p round index
  let out:=cursorValues v (cursor+1)
  obtain ⟨c₀,a,e₀,h₀,wa,f₀⟩:=copyWord_executes 1253 1256 0 cursor (by decide) input tape s
    cursorWord ((RationalAccumulator.zero_word_iff_blank _ _).mpr savedBlank)
  have ba:=bank_of_frame bank f₀ (by decide)
  have za:=ready.of_tapes (fun j hj => f₀.tapes j (by simp only [Finset.mem_singleton];omega))
  obtain ⟨c₁,b,e₁,h₁,bb,zb,pb,f₁⟩:=load_executes 1253 1234 (by decide) (by decide) v cursor
    input tape a ba za (RationalAccumulator.blank_of_eq (f₀.tapes 1249 (by decide)) privateBlank)
    (RationalAccumulator.word_of_eq (f₀.tapes 1253 (by decide)) cursorWord)
  have vw : ∀j∈ids,(v j).bits.length ≤ B := fun j hj =>
    (GeometrySort.seed_width p round index indexBound j hj).trans planBound
  have widthB:=cursorValues_width v cursor B vw cursorBound
  obtain ⟨c₂,c,e₂,h₂,bc,zc,f₂⟩:=stage [.add 1219 1234]
    (by simp [NatAssign.Instruction.Valid,ids,controls]) (cursorValues v cursor) B widthB
    (by simp [NatAssign.Instruction.literalWidth]) input tape b bb zb
  have values : NatAssign.values [.add 1219 1234] (cursorValues v cursor)=out := by
    simp [out,cursorValues,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.value,
      NatAssign.Instruction.target,v,GeometrySort.seed,Nat.add_comm]
  have bc' : NatAssign.Bank ids out c.val := by simpa only [values] using bc
  have fields : ∀j∈seedFields,out j=GeometrySort.seed p round index j := by
    intro j hj
    exact cursorValues_other v (cursor+1) j (by
      simp only [seedFields,Finset.mem_insert,Finset.mem_singleton] at hj;omega)
  have zero : ∀j∈Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,out j=0 := by
    intro j hj
    have small : j<1200 := by
      simp only [Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,
        Finset.mem_insert,Finset.mem_singleton] at hj
      omega
    change cursorValues v (cursor+1) j=0
    rw [cursorValues_other _ _ _ (by omega)]
    exact GeometrySort.seed_zero p round index j hj
  have nextWidth : (cursor+1).bits.length ≤ B+2 := by
    have h:=RationalAccumulator.bits_add_le cursor 1
    change (cursor+1).bits.length ≤ max cursor.bits.length 1+1 at h
    omega
  have outWidth:=cursorValues_width v (cursor+1) (B+2)
    (fun j hj => (vw j hj).trans (by omega)) nextWidth
  obtain ⟨c₃,t,e₃,h₃,bt,zt,pt,ct,f₃⟩:=GeometryPathReverse.footer_executes p round index cursor
    (B+2) out fields zero outWidth (by omega) input tape c bc' zc
    (RationalAccumulator.blank_of_eq (f₂.tapes 1249 (by decide)) pb)
    (RationalAccumulator.word_of_eq ((f₂.tapes 1253 (by decide)).trans
      ((f₁.tapes 1253 (by decide)).trans (f₀.tapes 1253 (by decide)))) cursorWord)
  refine ⟨c₀+(c₁+(c₂+c₃)),t,e₀.seq (e₁.seq (e₂.seq e₃)),?_,bt,zt,pt,ct,
    RationalAccumulator.word_of_eq ((f₃.tapes 1256 (by decide)).trans
      ((f₂.tapes 1256 (by decide)).trans (f₁.tapes 1256 (by decide)))) wa,
    (f₀.mono Finset.subset_union_left).trans ((f₁.mono (by decide)).trans
      ((f₂.mono (by
        intro j hj
        simp only [GeometryPathReverse.footerWork,work,
          Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hj ⊢
        tauto)).trans (f₃.mono Finset.subset_union_right)))⟩
  change c₂ ≤ 3000*8^1*(B+2)^2 at h₂
  norm_num [show (0 : ℕ).bits.length=0 from rfl] at h₀
  norm_num [v,GeometrySort.seed,show (0 : ℕ).bits.length=0 from rfl] at h₁
  have h₂' : c₂ ≤ 3000*8^1*(B+3)^2:=h₂.trans (by gcongr;omega)
  have h₃' : c₃ ≤ 2^114*(B+3)^2 := calc
    c₃ ≤ 2^112*(B+2+2)^2 := h₃
    _ ≤ 2^112*(2*(B+3))^2 := by gcongr;omega
    _ = 2^114*(B+3)^2 := by ring
  nlinarith only [h₀,h₁,h₂',h₃',cursorBound]

#print axioms reserve_executes
end Maxwell.Cost.RoutingPorts.Complete.GeometryPath
