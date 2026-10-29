import Maxwell.Cost.CalibrationMatrix.SplitIndex
import Maxwell.Cost.CalibrationMatrix.CubeDecode
import Maxwell.Cost.CalibrationMatrix.TestEntry

/-! Decode the actual row-major cursor to both physical stencil edges. -/
namespace Maxwell.Cost.CalibrationMatrix.GeneratedCoordinates
open Structured BankArray
open RationalAccumulator (Blank)
open Maxwell.Defect.FiniteStencil Maxwell.Spectral.Lattice
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

def rawBanks : Finset ℕ := {150,151,152,153,170,171,172,173}
def work : Finset ℕ := Finset.range 10 ∪ {70,71,72,123,124} ∪ rawBanks

def WorkBlank (s : BitRAMState) : Prop := ∀ i ∈ work, Blank s i

def Operands (s : BitRAMState) (raw : Fin 7 → List Bool) (direction : List Bool) : Prop :=
  Word s 150 (raw 0) ∧ Word s 151 (raw 1) ∧ Word s 152 (raw 2) ∧ Word s 153 (raw 3) ∧
  Word s 171 (raw 4) ∧ Word s 172 (raw 5) ∧ Word s 173 (raw 6) ∧ Word s 170 direction

def code : Code := .seq (SplitIndex.code 122 102)
  (.seq (Entry.decodeCode 121 123 150) (.seq (Entry.decodeCode 121 124 170)
    (.seq (.call (TapeOps.clear 123)) (.call (TapeOps.clear 124)))))

/-- Both edge coordinates are generated from the real flattened array
cursor. The two quotient/remainder index words are then erased. -/
theorem executes (input : List Bool) (tape : ℕ → Bool) (R : ℕ)
    (i j : Fin (3*cubeWidth R^3)) (radix dimension index : List Bool)
    (hrvalue : addressValue radix = cubeWidth R)
    (hdvalue : addressValue dimension = 3*cubeWidth R^3)
    (hivalue : addressValue index = i.val*(3*cubeWidth R^3)+j.val)
    (s : Store) (hr : Word s.val 121 radix) (hn : Word s.val 122 dimension)
    (hi : Word s.val 102 index) (hb : WorkBlank s.val) :
    ∃ cost t raw direction, cost ≤ 5000*(radix.length+dimension.length+index.length+3)^2 ∧
      Executes input tape code cost s t ∧ Operands t.val raw direction ∧
      addressValue (raw 0) = (radixCubeEmbedding R i).1.val ∧
      addressValue direction = (radixCubeEmbedding R j).1.val ∧
      unsignedEdge R (radixCubeEmbedding R i).1 (TestEntry.rowValues raw) = radixCubeEmbedding R i ∧
      unsignedEdge R (radixCubeEmbedding R j).1 (TestEntry.columnValues raw) = radixCubeEmbedding R j ∧
      (∀ k, (raw k).length ≤ radix.length+dimension.length+index.length) ∧
      direction.length ≤ dimension.length+index.length ∧
      (∀ k ∈ work, k ∉ rawBanks → Blank t.val k) ∧ BinaryPrecision.Frame work s.val t.val := by
  have hnpos : 0 < 3*cubeWidth R^3 := by unfold cubeWidth; positivity
  obtain ⟨a,m,row,column,hca,ea,hmrow,hmcol,hrval,hcval,hrlen,hclen,hms,hm72,hf⟩ :=
    SplitIndex.executes 122 102 (by decide) (by decide) input tape dimension index
      (by rw [hdvalue]; exact hnpos) s hn hi (fun k hk => hb k (by simp [work]; omega))
      (hb 72 (by decide)) (hb 123 (by decide)) (hb 124 (by decide))
  have rowValue : addressValue row = i.val := by
    rw [hrval,hivalue,hdvalue,Nat.add_div hnpos,Nat.mul_div_cancel _ hnpos,
      Nat.div_eq_of_lt j.isLt,Nat.add_zero]
    simp [Nat.mod_eq_of_lt j.isLt,Nat.not_le_of_gt j.isLt]
  have columnValue : addressValue column = j.val := by
    rw [hcval,hivalue,hdvalue]
    simp [Nat.add_mod,Nat.mod_eq_of_lt j.isLt]
  have firstBlank (k : ℕ) (hk : k < 5 ∨ k = 70 ∨ k = 71 ∨ k = 72 ∨ (150 ≤ k ∧ k < 154)) :
      Blank m.val k := by
    by_cases hs : k < 5
    · exact hms k hs
    by_cases h72 : k = 72
    · subst k; exact hm72
    apply hf.blank (by simp [SplitIndex.changes]; omega)
    exact hb k (by simp [work,rawBanks]; omega)
  obtain ⟨b,n,rx,ry,rz,rd,hcb,eb,hnrd,hnrx,hnry,hnrz,hrd,hredge,hrdl,hrxl,hryl,hrzl,hns,hg⟩ :=
    Entry.decode_coordinates 123 150 (by decide) (by decide) input tape R i radix row
      hrvalue rowValue m (hf.word (by decide) hr) hmrow firstBlank
  have secondBlank (k : ℕ) (hk : k < 5 ∨ k = 70 ∨ k = 71 ∨ k = 72 ∨ (170 ≤ k ∧ k < 174)) :
      Blank n.val k := by
    by_cases hs : k < 5 ∨ k = 70 ∨ k = 71 ∨ k = 72
    · exact hns k hs
    apply hg.blank (by simp [Entry.decodeChanges,Entry.exportChanges]; omega)
    apply hf.blank (by simp [SplitIndex.changes]; omega)
    exact hb k (by simp [work,rawBanks]; omega)
  obtain ⟨c,p,cx,cy,cz,cd,hcc,ec,hpcd,hpcx,hpcy,hpcz,hcd,hcedge,hcdl,hcxl,hcyl,hczl,hps,hh⟩ :=
    Entry.decode_coordinates 124 170 (by decide) (by decide) input tape R j radix column
      hrvalue columnValue n (hg.word (by decide) (hf.word (by decide) hr))
      (hg.word (by decide) hmcol) secondBlank
  have pRow := hh.word (by decide) (hg.word (by decide) hmrow)
  have pCol := hh.word (by decide) (hg.word (by decide) hmcol)
  obtain ⟨q,eq,hqrow,hq⟩ := HeaderWords.clear 123 input tape row p pRow
  obtain ⟨t,et,htcol,ht⟩ := HeaderWords.clear 124 input tape column q (hq.word (by simp) pCol)
  let raw : Fin 7 → List Bool := ![rd,rx,ry,rz,cx,cy,cz]
  have finalRow (k : ℕ) (hk : 150 ≤ k ∧ k ≤ 153) {word : List Bool} (hw : Word n.val k word) :
      Word t.val k word := ht.word (by simp; omega) (hq.word (by simp; omega)
        (hh.word (by simp [Entry.decodeChanges,Entry.exportChanges]; omega) hw))
  have finalCol (k : ℕ) (hk : 170 ≤ k ∧ k ≤ 173) {word : List Bool} (hw : Word p.val k word) :
      Word t.val k word := ht.word (by simp; omega) (hq.word (by simp; omega) hw)
  have rvalues : TestEntry.rowValues raw = Entry.coordinateValues rx ry rz := by
    funext k; fin_cases k <;> rfl
  have cvalues : TestEntry.columnValues raw = Entry.coordinateValues cx cy cz := by
    funext k; fin_cases k <;> rfl
  have f0 : BinaryPrecision.Frame work s.val m.val := hf.mono (by decide)
  have f1 : BinaryPrecision.Frame work m.val n.val := hg.mono (by decide)
  have f2 : BinaryPrecision.Frame work n.val p.val := hh.mono (by decide)
  have f3 : BinaryPrecision.Frame work p.val q.val := hq.mono (by decide)
  have f4 : BinaryPrecision.Frame work q.val t.val := ht.mono (by decide)
  refine ⟨a+(b+(c+(6*row.length+4+(6*column.length+4)))),t,raw,cd,?_,
    ea.seq (eb.seq (ec.seq (eq.seq et))),?_,hrd,hcd,?_,?_,?_,?_,?_,
    (((f0.trans f1).trans f2).trans f3).trans f4⟩
  · have hsum : dimension.length+index.length ≤ radix.length+dimension.length+index.length := by omega
    have hrow : radix.length+row.length ≤ radix.length+dimension.length+index.length := by omega
    have hcol : radix.length+column.length ≤ radix.length+dimension.length+index.length := by omega
    have ca : a ≤ 700*(radix.length+dimension.length+index.length+3)^2 :=
      hca.trans (by gcongr)
    have cb : b ≤ 2000*(radix.length+dimension.length+index.length+3)^2 :=
      hcb.trans (by gcongr)
    have cc : c ≤ 2000*(radix.length+dimension.length+index.length+3)^2 :=
      hcc.trans (by gcongr)
    nlinarith
  · exact ⟨finalRow 150 (by decide) hnrd,finalRow 151 (by decide) hnrx,
      finalRow 152 (by decide) hnry,finalRow 153 (by decide) hnrz,
      finalCol 171 (by decide) hpcx,finalCol 172 (by decide) hpcy,
      finalCol 173 (by decide) hpcz,finalCol 170 (by decide) hpcd⟩
  · simpa only [rvalues] using hredge
  · simpa only [cvalues] using hcedge
  · intro k
    fin_cases k <;> dsimp [raw] <;> omega
  · omega
  · intro k hk hraw
    by_cases h123 : k = 123
    · subst k; exact ht.blank (by simp) hqrow
    by_cases h124 : k = 124
    · subst k; exact htcol
    apply ht.blank (by simp; omega)
    apply hq.blank (by simp; omega)
    by_cases hsmall : k < 5 ∨ k = 70 ∨ k = 71 ∨ k = 72
    · exact hps k hsmall
    have hrange : 5 ≤ k ∧ k < 10 := by
      simp only [work,rawBanks,Finset.mem_union,Finset.mem_range,Finset.mem_insert,
        Finset.mem_singleton,not_or] at hk hraw
      omega
    apply hh.blank (by simp [Entry.decodeChanges,Entry.exportChanges]; omega)
    apply hg.blank (by simp [Entry.decodeChanges,Entry.exportChanges]; omega)
    apply hf.blank (by simp [SplitIndex.changes]; omega)
    exact hb k hk

end Maxwell.Cost.CalibrationMatrix.GeneratedCoordinates
