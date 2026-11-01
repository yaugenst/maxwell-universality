import Maxwell.Continuum.SourceRoutingPathRetreat
import Maxwell.Continuum.SourceRoutingPathPredecessor
import Maxwell.Continuum.SourceRoutingPathReverseFooter

/-! One actual reverse layer: retreat its stored addresses, recover the
predecessor port, emit that strand backwards, and restore the control bank. -/
namespace Maxwell.Cost.RoutingPorts.Complete.GeometryPathReverse
open Structured GeometryArithmetic GeometryPath Maxwell.Logical.Routing
open RationalAccumulator (Word Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 3200000

def stepCode (transpose : Bool) : Code := .seq retreat.code
  (.seq (PhysicalMaterial.FixedSubtract.code 1255 1)
    (.seq predecessorCode (.seq (emitCode transpose true) footerCode)))

def stepWork : Finset ℕ := {1253,1255}∪wordWork
def stepBound {q : ℕ} (p : GeometryHistory.Plan q) (k level cursor width base n : ℕ) : ℕ :=
  emitBound (p.layer k) (k+1) level cursor width base n+
    (p.layer (k+1)).bound (k+2)+(level+1).bits.length

theorem step_executes {q : ℕ} (p : GeometryHistory.Plan q) (k : ℕ) (saved : SortArrays.Keys q)
    (fit : GeometrySort.Fits p.width saved) (current : Port q)
    (level cursor width base n : ℕ) (clock : List Bool) (transpose : Bool)
    (levelBound : level ≤ 6*q) (widthPositive : 0<width) (clockLength : clock.length=width)
    (coordinateWidth : (1024*q+1).bits.length ≤ width)
    (room : cursor+3*RowLayer.pathLength (SortArrays.arraySelection (k+1) saved)
      (RowLayer.destination (SortArrays.arraySelection (k+1) saved) current) ≤ n)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank ids (GeometrySort.seed (p.layer (k+1)) (k+2) (finProdFinEquiv current).val) s.val)
    (ready : GeometryArray.Ready s.val) (privateBlank : Blank s.val 1249)
    (metadata : GeometrySort.Metadata (p.layer (k+1)) s.val)
    (output : OutputMetadata width base clock s.val)
    (levelWord : Word s.val 1255 (level+1)) (cursorWord : Word s.val 1253 cursor)
    (source : BitArray.Represents s.val.memory (p.slab k) p.width (IncidenceEncoding.words p.width saved)) :
    let previous := RowLayer.destination (SortArrays.arraySelection (k+1) saved) current
    ∃steps t,Executes input tape (stepCode transpose) steps s t ∧
      steps ≤ 2^230*(stepBound p k level cursor width base n+3)^2 ∧
      NatAssign.Bank ids (GeometrySort.seed (p.layer k) (k+1) (finProdFinEquiv previous).val) t.val ∧
      GeometryArray.Ready t.val ∧ Blank t.val 1249 ∧ GeometrySort.Metadata (p.layer k) t.val ∧
      OutputMetadata width base clock t.val ∧ Word t.val 1255 level ∧
      Word t.val 1253 (cursor+3*RowLayer.pathLength (SortArrays.arraySelection (k+1) saved) previous) ∧
      t.val.memory=MemoryWord.writeBits s.val.memory (base+cursor*width)
        (emittedBits (p.layer k) (k+1) saved (finProdFinEquiv previous) level cursor width transpose true) ∧
      ArchiveFrame stepWork s.val t.val := by
  dsimp only
  let previous := RowLayer.destination (SortArrays.arraySelection (k+1) saved) current
  let nextCursor := cursor+3*RowLayer.pathLength (SortArrays.arraySelection (k+1) saved) previous
  let B := stepBound p k level cursor width base n
  have emitSmall : emitBound (p.layer k) (k+1) level cursor width base n ≤ B := by
    dsimp only [B,stepBound];omega
  have oldSmall : (p.layer (k+1)).bound (k+2) ≤ B := by dsimp only [B,stepBound];omega
  have newSmall : (p.layer k).bound (k+1) ≤ B := by dsimp only [B,stepBound,emitBound,prepareBound];omega
  have levelSmall : (level+1).bits.length ≤ B := by dsimp only [B,stepBound];omega
  obtain ⟨c₀,a,e₀,h₀,ba,za,pa,f₀⟩ := retreat_executes p k (finProdFinEquiv current).val
    (finProdFinEquiv current).isLt.le input tape s bank ready privateBlank
  obtain ⟨c₁,b,e₁,h₁,lb,f₁⟩ := PhysicalMaterial.FixedSubtract.executes 1255 1 (level+1)
    (by omega) input tape a (RationalAccumulator.word_of_eq (f₀.tapes 1255 (by decide)) levelWord)
  have bb := bank_of_frame ba f₁ (by decide)
  have zb := za.of_tapes (fun j hj => f₁.tapes j (by simp only [Finset.mem_singleton];omega))
  have fb : ArchiveFrame stepWork s.val b.val :=
    ((ArchiveFrame.of_binary f₀).mono (by decide)).trans ((ArchiveFrame.of_binary f₁).mono (by decide))
  have mbOld := metadata.frame fb (by decide)
  have mb : GeometrySort.Metadata (p.layer k) b.val := ⟨mbOld.width,mbOld.clock⟩
  obtain ⟨c₂,c,e₂,h₂,bc,zc,pc,mc,mem₂,f₂⟩ := predecessor_executes (p.layer k) (k+1)
    saved fit (finProdFinEquiv current) input tape b bb zb
    (RationalAccumulator.blank_of_eq (f₁.tapes 1249 (by decide)) pa)
    mb (by rw [f₁.memory,f₀.memory];exact source)
  simp only [Equiv.symm_apply_apply] at bc
  have fc := fb.trans (f₂.mono (by decide))
  have lc : Word c.val 1255 level := by
    simpa only [Nat.add_sub_cancel] using
      RationalAccumulator.word_of_eq (f₂.tapes 1255 (by decide) (by decide)) lb
  have oc : OutputMetadata width base clock c.val :=
    ⟨RationalAccumulator.word_of_eq (fc.tapes 1250 (by decide) (by decide)) output.wordWidth,
      RationalAccumulator.word_of_eq (fc.tapes 1252 (by decide) (by decide)) output.baseWord,
      BankArray.word_of_eq (fc.tapes 1251 (by decide) (by decide)) output.clockWord⟩
  have cc : Word c.val 1253 cursor :=
    RationalAccumulator.word_of_eq ((f₂.tapes 1253 (by decide) (by decide)).trans
      ((f₁.tapes 1253 (by decide)).trans (f₀.tapes 1253 (by decide)))) cursorWord
  obtain ⟨c₃,d,e₃,h₃,bd,zd,pd,md,od,mem₃,f₃⟩ := emit_executes (p.layer k) (k+1) saved fit
    (finProdFinEquiv previous) level cursor width base n clock transpose levelBound widthPositive clockLength
    coordinateWidth (by simpa only [Equiv.symm_apply_apply] using room) input tape c bc zc pc mc oc lc cc
    (by rw [mem₂,f₁.memory,f₀.memory];exact source) true
  let v := cursorValues (emissionValues (p.layer k) (k+1) saved (finProdFinEquiv previous) level cursor transpose) nextCursor
  have nb : n.bits.length ≤ B := by dsimp only [B,stepBound,emitBound];omega
  have cb : cursor.bits.length ≤ B :=
    (Maxwell.Continuum.RationalWords.bits_mono (show cursor ≤ n by omega)).trans nb
  have nextBound : nextCursor.bits.length ≤ B := (Maxwell.Continuum.RationalWords.bits_mono room).trans nb
  have vb : ∀j∈ids,(v j).bits.length ≤ 2^50*(B+3) := by
    apply cursorValues_width
    · intro j hj
      have h := emission_width (p.layer k) (k+1) saved fit (finProdFinEquiv previous) level cursor transpose j hj
      have prep : prepareBound (p.layer k) (k+1) level cursor ≤ B := by
        dsimp only [B,stepBound,emitBound];omega
      exact h.trans (by omega)
    · omega
  obtain ⟨c₄,t,e₄,h₄,bt,zt,pt,ct,f₄⟩ := footer_executes (p.layer k) (k+1)
    (finProdFinEquiv previous).val cursor (2^50*(B+3)) v
    (emission_fields _ _ _ _ _ _ _ _) (emission_quotient_zero _ _ _ _ _ _ _ _)
    vb (by omega) input tape d (by simpa only [Equiv.symm_apply_apply] using bd) zd pd
    (RationalAccumulator.word_of_eq (f₃.tapes 1253 (by decide) (by decide)) cc)
  have finalFrame := fc.trans ((f₃.mono (by decide)).trans ((ArchiveFrame.of_binary f₄).mono (by decide)))
  refine ⟨c₀+(c₁+(c₂+(c₃+c₄))),t,e₀.seq (e₁.seq (e₂.seq (e₃.seq e₄))),?_,bt,zt,pt,
    md.frame (ArchiveFrame.of_binary f₄) (by decide),
    ⟨RationalAccumulator.word_of_eq (f₄.tapes 1250 (by decide)) od.wordWidth,
      RationalAccumulator.word_of_eq (f₄.tapes 1252 (by decide)) od.baseWord,
      BankArray.word_of_eq (f₄.tapes 1251 (by decide)) od.clockWord⟩,
    RationalAccumulator.word_of_eq ((f₄.tapes 1255 (by decide)).trans
      (f₃.tapes 1255 (by decide) (by decide))) lc,ct,?_,finalFrame⟩
  · have aCost := h₀.trans (Nat.mul_le_mul_left (2^152) (Nat.pow_le_pow_left (show (p.layer (k+1)).bound (k+2)+2 ≤ B+3 by omega) 2))
    have cCost := h₂.trans (Nat.mul_le_mul_left (2^188) (Nat.pow_le_pow_left (Nat.add_le_add_right newSmall 3) 2))
    have dCost := h₃.trans (Nat.mul_le_mul_left (2^226) (Nat.pow_le_pow_left (Nat.add_le_add_right emitSmall 3) 2))
    have tCost : c₄ ≤ 2^214*(B+3)^2 := calc
      c₄ ≤ 2^112*(2^50*(B+3)+2)^2 := h₄
      _ ≤ 2^112*(2^51*(B+3))^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
      _ = 2^214*(B+3)^2 := by ring
    dsimp only [PhysicalMaterial.FixedSubtract.costBound] at h₁
    change c₀+(c₁+(c₂+(c₃+c₄))) ≤ 2^230*(B+3)^2
    nlinarith only [aCost,cCost,dCost,tCost,h₁,levelSmall]
  · rw [f₄.memory,mem₃,mem₂,f₁.memory,f₀.memory]

#print axioms step_executes
end Maxwell.Cost.RoutingPorts.Complete.GeometryPathReverse
