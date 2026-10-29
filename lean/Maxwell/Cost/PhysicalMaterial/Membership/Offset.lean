import Maxwell.Cost.PhysicalMaterial.Membership.Equal
import Maxwell.Cost.DecoderConstants.Helpers

namespace Maxwell.Cost.PhysicalMaterial.Membership
open Structured RationalAccumulator

def Ready (s : BitRAMState) : Prop := ∀ i, i < 10 → Blank s i

def offsetWork (target : ℕ) : Finset ℕ := {0,1,2,3,target,292}

def offsetCode (source target amount : ℕ) : Code :=
  .seq (.call (WordTransfer.clone source target))
    (.seq (BinaryPrecision.literalCode 292 amount)
      (.seq (DecoderConstants.addCode 292 target) (.call (TapeOps.clear 292))))

private theorem stored_frame {target : ℕ} {s t : BitRAMState}
    (h : StoredProduct.Frame target s t) : BinaryPrecision.Frame (offsetWork target) s t := by
  refine ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,?_⟩
  intro i hi
  have hh : i ≠ 0 ∧ i ≠ 1 ∧ i ≠ 2 ∧ i ≠ 3 ∧ i ≠ target := by
    simp only [offsetWork,Finset.mem_insert,Finset.mem_singleton,not_or] at hi
    tauto
  exact h.2.2.2.2.2.1 i (by omega) hh.2.2.2.2

set_option maxRecDepth 8192 in
theorem offset_general (source target amount : ℕ) (hs : 10 ≤ source)
    (ht : 10 ≤ target) (hst : source ≠ target) (ht292 : target ≠ 292)
    (input : List Bool) (tape : ℕ → Bool) (x : ℕ) (s : Store)
    (hw : Word s.val source x) (hblank : Blank s.val target) (h292 : Blank s.val 292)
    (hr : Ready s.val) :
    ∃ cost t, cost ≤ 220*(x.bits.length+amount.bits.length+4) ∧
      Executes input tape (offsetCode source target amount) cost s t ∧
      Word t.val target (x+amount) ∧ Blank t.val 292 ∧ Ready t.val ∧
      BinaryPrecision.Frame (offsetWork target) s.val t.val := by
  obtain ⟨a,ea,aw,af,asmall⟩ := DecoderConstants.cloneStored source target (by omega) (by omega)
    hst input tape x s hw hblank
  obtain ⟨b,eb,bw,bf⟩ := BinaryPrecision.literal 292 amount input tape a
    (blank_of_eq (af.2.2.2.2.2.1 292 (by decide) (Ne.symm ht292)) h292)
  have bsmall (i : ℕ) (hi : i < 4) : Blank b.val i :=
    blank_of_eq ((bf.tapes i (by simp; omega)).trans (asmall i hi)) (hr i (by omega))
  obtain ⟨ac,c,hac,ec,cw,csmall,cf⟩ := DecoderConstants.add 292 target (by decide) (by omega)
    (Ne.symm ht292) input tape amount x b bw
    (word_of_eq (bf.tapes target (by simpa using ht292)) aw) bsmall
  obtain ⟨t,et,t292,tf,tsmall⟩ := DecoderConstants.clearStored 292 (by decide) input tape amount c
    (word_of_eq (cf.2.2.2.2.2.1 292 (by decide) (Ne.symm ht292)) bw)
  have af' := stored_frame af
  have bf' := bf.mono (show ({292} : Finset ℕ) ⊆ offsetWork target by simp [offsetWork])
  have cf' := stored_frame cf
  have tf' : BinaryPrecision.Frame (offsetWork target) c.val t.val := by
    refine ⟨tf.1,tf.2.1,tf.2.2.1,tf.2.2.2.1,tf.2.2.2.2.1,?_⟩
    intro i hi
    simp only [offsetWork,Finset.mem_insert,Finset.mem_singleton,not_or] at hi
    exact tf.2.2.2.2.2.1 i (by omega) hi.2.2.2.2.2
  have all := ((af'.trans bf').trans cf').trans tf'
  refine ⟨15*x.bits.length+17+(10*amount.bits.length+7+(ac+(6*amount.bits.length+4))),t,by omega,
    ea.seq (eb.seq (ec.seq et)),?_,t292,?_,all⟩
  · have tw := word_of_eq (tf.2.2.2.2.2.1 target (by omega) ht292) cw
    simpa only [Nat.add_comm] using tw
  · intro i hi
    by_cases hsmall : i < 4
    · exact blank_of_eq (tsmall i hsmall) (csmall i hsmall)
    · exact blank_of_eq (all.tapes i (by
        simp only [offsetWork,Finset.mem_insert,Finset.mem_singleton,not_or]
        omega)) (hr i hi)


theorem offset_executes (source target amount : ℕ) (hs : 10 ≤ source)
    (ht : target = 290 ∨ target = 291) (hst : source ≠ target) (_hs292 : source ≠ 292)
    (input : List Bool) (tape : ℕ → Bool) (x : ℕ) (s : Store)
    (hw : Word s.val source x) (hblank : Blank s.val target) (h292 : Blank s.val 292)
    (hr : Ready s.val) :
    ∃ cost t, cost ≤ 220*(x.bits.length+amount.bits.length+4) ∧
      Executes input tape (offsetCode source target amount) cost s t ∧
      Word t.val target (x+amount) ∧ Blank t.val 292 ∧ Ready t.val ∧
      BinaryPrecision.Frame (offsetWork target) s.val t.val :=
  offset_general source target amount hs (by omega) hst (by omega) input tape x s hw hblank h292 hr

end Maxwell.Cost.PhysicalMaterial.Membership
