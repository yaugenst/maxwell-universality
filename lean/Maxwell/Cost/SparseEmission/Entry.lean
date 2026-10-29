import Maxwell.Cost.SparseEmission.Prepend
import Maxwell.Cost.SparseEmission.CopyEnd
import Maxwell.Cost.SparseEmission.Encoding

namespace Maxwell.Cost.SparseEmission.Entry
open Structured
open SourceCircuit (Frame)

def code (parent : ℕ) (negative half : Bool) : Code :=
  .seq (Prepend.literals 110 [negative,half])
    (.seq (Prepend.code parent 93 110)
      (.seq (CopyEnd.code 113 114) (Prepend.code 114 93 110)))

def work (parent : ℕ) : Finset ℕ := {parent,110,114}

/-- One sparse entry is formed only by reading the actual row and parent
words. Temporary words are consumed, leaving reusable blank scratch. -/
theorem executes (parent : ℕ) (hparent : parent = 111 ∨ parent = 112)
    (negative half : Bool) (input : List Bool) (randomTape : ℕ → Bool)
    (row column clock preceding : List Bool) (origin rowOrigin clockOrigin : ℤ) (s : Store)
    (hlen : column.length = row.length) (hcLen : clock.length = row.length)
    (ha : s.val.tapes 110 = BitTape.shifted preceding origin)
    (hr : s.val.tapes 113 = BitTape.shifted row rowOrigin)
    (hp : s.val.tapes parent = BitTape.atEnd column)
    (hc : s.val.tapes 93 = BitTape.shifted clock clockOrigin)
    (h114 : s.val.tapes 114 = BitTape.blank) :
    ∃ t, Executes input randomTape (code parent negative half) (50*row.length+54) s t ∧
      t.val.tapes 110 = BitTape.shifted (row++column++[negative,half]++preceding)
        (origin-(2*row.length+2)) ∧
      t.val.tapes parent = BitTape.blank ∧ t.val.tapes 114 = BitTape.blank ∧
      t.val.address = s.val.address ∧ t.val.memory = s.val.memory ∧
      Frame (work parent) s.val t.val ∧
      (∀ i, i ∉ work parent → t.val.tapes i = s.val.tapes i) := by
  obtain ⟨a,ea,atapes,aa,am,af⟩ := Prepend.literals_executes 110 [negative,half] preceding origin
    input randomTape s ha
  have aParent : a.val.tapes parent = BitTape.atEnd column := by
    simpa [atapes,show parent ≠ 110 by omega] using hp
  have aClock : a.val.tapes 93 = BitTape.shifted clock clockOrigin := by simpa [atapes] using hc
  obtain ⟨b,eb,bp,ba,baAddress,bm,bf,bkeep⟩ := Prepend.executes parent 93 110
    (by omega) (by omega) (by decide) input randomTape column ([negative,half]++preceding) clock
      (origin-2) clockOrigin a (by omega) aParent (by simp [atapes]) aClock
  have bRow : b.val.tapes 113 = BitTape.shifted row rowOrigin := by
    rw [bkeep 113 (by omega) (by decide)]
    simpa [atapes] using hr
  have b114 : b.val.tapes 114 = BitTape.blank := by
    rw [bkeep 114 (by omega) (by decide)]
    simpa [atapes] using h114
  obtain ⟨c,ec,c114,caAddress,cm,cf,ckeep⟩ := CopyEnd.executes 113 114 (by decide)
    input randomTape row rowOrigin b bRow b114
  have cArchive : c.val.tapes 110 = BitTape.shifted (column++([negative,half]++preceding))
      (origin-2-column.length) := (ckeep 110 (by decide)).trans ba
  have cClock : c.val.tapes 93 = BitTape.shifted clock clockOrigin :=
    (ckeep 93 (by decide)).trans ((bkeep 93 (by omega) (by decide)).trans aClock)
  obtain ⟨t,et,t114,ta,taAddress,tm,tf,tkeep⟩ := Prepend.executes 114 93 110
    (by decide) (by decide) (by decide) input randomTape row
      (column++([negative,half]++preceding)) clock (origin-2-column.length) clockOrigin c hcLen
      c114 cArchive cClock
  have keep (i : ℕ) (hi : i ∉ work parent) : t.val.tapes i = s.val.tapes i := by
    simp only [work,Finset.mem_insert,Finset.mem_singleton,not_or] at hi
    rw [tkeep i hi.2.2 hi.2.1, ckeep i hi.2.2, bkeep i hi.1 hi.2.1]
    simp [atapes,hi.2.1]
  have frame : Frame (work parent) s.val t.val :=
    ((af.mono (by simp [work])).trans (bf.mono (by simp [work]))).trans
      ((cf.mono (by simp [work])).trans (tf.mono (by
        intro i hi
        simp only [Finset.mem_insert,Finset.mem_singleton] at hi
        rcases hi with rfl | rfl <;> simp [work])))
  refine ⟨t,?_,?_,?_,t114,taAddress.trans (caAddress.trans (baAddress.trans aa)),
    tm.trans (cm.trans (bm.trans am)),frame,keep⟩
  · convert ea.seq (eb.seq (ec.seq et)) using 1 <;> first | rfl | simp only [List.length_cons,List.length_nil]; omega
  · simpa [hlen,List.append_assoc,Nat.cast_add,Nat.cast_mul,sub_sub,add_assoc,add_comm,add_left_comm,
      two_mul] using ta
  · exact (tkeep parent (by omega) (by omega)).trans ((ckeep parent (by omega)).trans bp)

end Maxwell.Cost.SparseEmission.Entry
