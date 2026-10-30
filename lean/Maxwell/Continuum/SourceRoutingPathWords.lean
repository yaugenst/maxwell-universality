import Maxwell.Continuum.SourceRoutingPathWordsData

namespace Maxwell.Cost.RoutingPorts.Complete.GeometryPath
open Structured GeometryArithmetic
open RationalAccumulator (Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

theorem words_executes (entries : List Entry) (width base B n cursor : ℕ) (clock : List Bool)
    (positive : 0<width) (clockLength : clock.length=width) (room : cursor+entries.length ≤ n)
    (v : ℕ→ℕ) (one : v 1219=1) (zero : v 1235=0)
    (bankWidth : ∀j∈GeometryArithmetic.ids,(v j).bits.length ≤ B)
    (literal : ∀e∈entries,e.2.bits.length ≤ B)
    (fit : ∀e∈entries,(entryValue v e).bits.length ≤ width)
    (widthBound : width ≤ B) (baseBound : base.bits.length ≤ B) (sizeBound : n.bits.length ≤ B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank GeometryArithmetic.ids (cursorValues v cursor) s.val)
    (ready : GeometryArray.Ready s.val) (privateBlank : Blank s.val 1249)
    (metadata : OutputMetadata width base clock s.val) :
    ∃steps t,Executes input tape (wordsCode entries) steps s t ∧
      steps ≤ (entries.length+1)*2^28*(B+3)^2 ∧
      NatAssign.Bank GeometryArithmetic.ids (cursorValues v (cursor+entries.length)) t.val ∧
      GeometryArray.Ready t.val ∧ Blank t.val 1249 ∧ OutputMetadata width base clock t.val ∧
      t.val.memory=MemoryWord.writeBits s.val.memory (base+cursor*width) (entryBits width v entries) ∧
      ArchiveFrame wordWork s.val t.val := by
  induction entries generalizing cursor s with
  | nil =>
    refine ⟨1,s,.skip s,?_,bank,ready,privateBlank,metadata,rfl,ArchiveFrame.refl _ _⟩
    simp only [List.length_nil,Nat.zero_add,Nat.one_mul]
    nlinarith
  | cons e es ih =>
    have here : cursor<n := by simp only [List.length_cons] at room;omega
    have cursorBound : cursor.bits.length ≤ B :=
      (Maxwell.Continuum.RationalWords.bits_mono (Nat.le_of_lt here)).trans sizeBound
    let i : Fin n := ⟨cursor,here⟩
    obtain ⟨c0,a,e0,h0,ba,za,a1249,ma,_,memory,frame⟩:=word_executes e.1 e.2 width base B clock
      (GeometryArray.snapshot s.val.memory base width n) i positive clockLength (cursorValues v cursor)
      (by simp [cursorValues,i]) (by simpa only [cursorValues_other v cursor 1219 (by decide)] using one)
      (by simpa only [cursorValues_other v cursor 1235 (by decide)] using zero)
      (cursorValues_width v cursor B bankWidth cursorBound) (literal e (by simp))
      (by simpa only [cursorValues_axis,entryValue] using fit e (by simp))
      widthBound baseBound input tape s bank ready privateBlank metadata
      (GeometryArray.snapshot_represents _ _ _ _)
    have bankNext : NatAssign.Bank GeometryArithmetic.ids (cursorValues v (cursor+1)) a.val := by
      simpa only [i,cursorValues_update] using ba
    obtain ⟨c1,t,e1,h1,bt,zt,t1249,mt,memt,ft⟩:=ih (cursor+1)
      (by simp only [List.length_cons] at room;omega)
      (fun e he => literal e (by simp [he])) (fun e he => fit e (by simp [he]))
      a bankNext za a1249 ma
    refine ⟨c0+c1,t,e0.seq e1,?_,?_,zt,t1249,mt,?_,frame.trans ft⟩
    · simp only [List.length_cons]
      nlinarith only [h0,h1]
    · simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using bt
    · rw [memt,memory]
      simp only [cursorValues_axis,entryBits,List.flatMap_cons]
      have address : base+(cursor+1)*width=base+cursor*width+
          (IncidenceEncoding.word width (entryValue v e)).length := by
        rw [IncidenceEncoding.word_length];ring
      rw [address]
      exact writeBits_append _ _ _ _

#print axioms words_executes
end Maxwell.Cost.RoutingPorts.Complete.GeometryPath
