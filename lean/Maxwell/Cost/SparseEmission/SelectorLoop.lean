import Maxwell.Cost.SparseEmission.Selector
import Maxwell.Cost.SparseEmission.SelectorEntries
import Maxwell.Cost.Structured.CountedShifted

namespace Maxwell.Cost.SparseEmission.SelectorLoop
open Structured

def code : Code := CountedShifted.code 113 Selector.code
def work : Finset ℕ := {105,110,111,112,113,114}

structure Ready (clock : List Bool) (clockOrigin : ℤ) (s : Store) : Prop where
  clockWord : s.val.tapes 93 = BitTape.shifted clock clockOrigin
  left : s.val.tapes 111 = BitTape.blank
  right : s.val.tapes 112 = BitTape.blank
  temporary : s.val.tapes 114 = BitTape.blank

theorem ready_counter {clock : List Bool} {origin : ℤ} {s t : Store}
    (h : Counted.Frame 113 s t) (hr : Ready clock origin s) : Ready clock origin t :=
  ⟨(h.2.2.2.2.2.1 93 (by decide)).trans hr.clockWord,
    (h.2.2.2.2.2.1 111 (by decide)).trans hr.left,
    (h.2.2.2.2.2.1 112 (by decide)).trans hr.right,
    (h.2.2.2.2.2.1 114 (by decide)).trans hr.temporary⟩

theorem frame_counter {s t : Store} (h : Counted.Frame 113 s t) :
    SourceCircuit.Frame work s.val t.val :=
  ⟨h.2.1,h.2.2.2.1,h.2.2.2.2.1,fun i _ hi => h.2.2.2.2.2.1 i (by simp_all [work]),
    h.2.2.2.2.2.2 23 (by omega) (by omega) (by omega) (by omega),
    fun i hi => h.2.2.2.2.2.2 i (by omega) (by omega) (by omega) (by omega)⟩

theorem executes (input : List Bool) (randomTape : ℕ → Bool)
    (width : ℕ) (outputs : List ℕ) (clock preceding : List Bool)
    (origin rowOrigin clockOrigin : ℤ) (s : Store)
    (hc : clock.length = width) (hroom : outputs.length < 2^width)
    (hready : Ready clock clockOrigin s)
    (hrow : s.val.tapes 113 = BitTape.shifted (SourceCircuit.fixedWidth width outputs.length) rowOrigin)
    (h105 : s.val.tapes 105 = BitTape.atEnd (outputs.flatMap (SourceCircuit.fixedWidth width)))
    (h110 : s.val.tapes 110 = BitTape.shifted preceding origin) :
    ∃ cost t finalWord, cost ≤ (outputs.length+1)*(100*width+110) ∧
      Executes input randomTape code cost s t ∧
      t.val.tapes 105 = BitTape.blank ∧
      t.val.tapes 110 = BitTape.shifted (entriesWire width (selectorEntries 0 outputs)++preceding)
        (origin-(entriesWire width (selectorEntries 0 outputs)).length) ∧
      t.val.tapes 113 = BitTape.shifted finalWord rowOrigin ∧ finalWord.length = width ∧
      Ready clock clockOrigin t ∧ t.val.registers 29 = false ∧
      t.val.address = s.val.address ∧ t.val.memory = s.val.memory ∧
      SourceCircuit.Frame work s.val t.val ∧
      (∀ i, i ∉ work → t.val.tapes i = s.val.tapes i) := by
  induction outputs using List.reverseRecOn generalizing preceding origin s with
  | nil =>
    obtain ⟨t,et,tw,tfalse,tf⟩ := CountedShifted.test_executes 113 rowOrigin input randomTape s
      (SourceCircuit.fixedWidth width 0) hrow
    have hz : t.val.registers 29 = false := tfalse.mpr (SourceCircuit.fixedWidth_value width 0 hroom)
    refine ⟨13*width+15,t,subtractBit true (SourceCircuit.fixedWidth width 0),by simp; omega,
      ?_,?_,?_,tw,by simp,ready_counter tf hready,hz,tf.1,tf.2.2.1,frame_counter tf,?_⟩
    · convert et.seq (Executes.done hz) using 1 <;> first | rfl | simp
    · simpa [BitTape.atEnd,BitTape.ofList,BitTape.blank] using (tf.2.2.2.2.2.1 105 (by decide)).trans h105
    · simpa [selectorEntries,entriesWire] using (tf.2.2.2.2.2.1 110 (by decide)).trans h110
    · intro i hi; exact tf.2.2.2.2.2.1 i (by simp_all [work])
  | append_singleton outputs parent ih =>
    have hlen : (outputs++[parent]).length = outputs.length+1 := by simp
    obtain ⟨a,ea,aWord,aFalse,af⟩ := CountedShifted.test_executes 113 rowOrigin input randomTape s
      (SourceCircuit.fixedWidth width (outputs.length+1)) (by simpa using hrow)
    have hv : addressValue (SourceCircuit.fixedWidth width (outputs.length+1)) = outputs.length+1 :=
      SourceCircuit.fixedWidth_value _ _ (by simpa using hroom)
    have hpred : subtractBit true (SourceCircuit.fixedWidth width (outputs.length+1)) =
        SourceCircuit.fixedWidth width outputs.length :=
      SourceCircuit.fixedWidth_eq (by simp) (by rw [subtractBit_pred _ (by omega),hv]; omega)
    have aRow : a.val.tapes 113 = BitTape.shifted (SourceCircuit.fixedWidth width outputs.length) rowOrigin := by
      simpa only [hpred] using aWord
    have aTrue : a.val.registers 29 = true := by
      cases ht : a.val.registers 29 with
      | true => rfl
      | false => have := aFalse.mp ht; omega
    have ar := ready_counter af hready
    obtain ⟨b,eb,b105,b110,b111,b112,b114,ba,bm,bf,bk⟩ := Selector.executes input randomTape
      (SourceCircuit.fixedWidth width outputs.length) (SourceCircuit.fixedWidth width parent)
      (outputs.flatMap (SourceCircuit.fixedWidth width)) clock preceding origin rowOrigin clockOrigin a
      (by simp) (by simpa using hc)
      (by simpa [List.flatMap_append] using (af.2.2.2.2.2.1 105 (by decide)).trans h105)
      ((af.2.2.2.2.2.1 110 (by decide)).trans h110) ar.left ar.right ar.temporary aRow ar.clockWord
    let entry : Logical.RationalCode.Entry := ⟨outputs.length,parent,1⟩
    have bArchive : b.val.tapes 110 = BitTape.shifted (entryWire width entry++preceding)
        (origin-(entryWire width entry).length) := by
      norm_num [entry,entryWire,valueBits,two_mul,add_assoc] at b110 ⊢
      exact b110
    have br : Ready clock clockOrigin b :=
      ⟨(bk 93 (by decide)).trans ar.clockWord,b111,b112,b114⟩
    obtain ⟨restCost,t,finalWord,restBound,er,t105,t110,t113,tLength,tr,tFalse,ta,tm,tf,tk⟩ := ih
      (entryWire width entry++preceding) (origin-(entryWire width entry).length) b
      (by simp only [List.length_append,List.length_singleton] at hroom; omega) br
      ((bk 113 (by decide)).trans aRow) b105 bArchive
    have archive : t.val.tapes 110 = BitTape.shifted
        (entriesWire width (selectorEntries 0 (outputs++[parent]))++preceding)
        (origin-(entriesWire width (selectorEntries 0 (outputs++[parent]))).length) := by
      simpa [selectorEntries_append,selectorEntries,entriesWire_append,entriesWire,entry,
        List.append_assoc,List.length_append,Nat.cast_add,sub_sub,add_comm] using t110
    have keep (i : ℕ) (hi : i ∉ work) : t.val.tapes i = s.val.tapes i :=
      ((tk i hi).trans (bk i (by simp_all [work,Selector.work]))).trans
        (af.2.2.2.2.2.1 i (by simp_all [work]))
    change Executes input randomTape (.seq (Counted.test 113) (.loop 29 (.seq Selector.code (Counted.test 113))))
      restCost b t at er
    cases er with
    | seq restTest restLoop =>
      refine ⟨_,t,finalWord,?_,ea.seq (Executes.more aTrue (eb.seq restTest) restLoop),
        t105,archive,t113,tLength,tr,tFalse,ta.trans (ba.trans af.1),
        tm.trans (bm.trans af.2.2.1),(frame_counter af).trans ((bf.mono (by decide)).trans tf),keep⟩
      simp only [SourceCircuit.fixedWidth_length] at *
      simp only [List.length_append,List.length_singleton]
      nlinarith

end Maxwell.Cost.SparseEmission.SelectorLoop
