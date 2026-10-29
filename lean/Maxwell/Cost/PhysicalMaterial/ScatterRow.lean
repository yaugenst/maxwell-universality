import Maxwell.Cost.PhysicalMaterial.ScatterList
import Maxwell.Cost.PhysicalMaterial.DescriptorClear

namespace Maxwell.Cost.PhysicalMaterial.Scatter
open Structured RationalAccumulator
set_option maxHeartbeats 2200000

def anchor {n : ℕ} (d : Descriptors.Data n) (i : Fin n) (j : Fin 3) : ℕ :=
  Descriptors.value d i ⟨j.val, by omega⟩

def recordWork : Finset ℕ := Descriptors.targets ∪ work ∪ {302}
structure RecordFrame (s t : BitRAMState) : Prop where
  inputHead : t.inputHead = s.inputHead
  randomCursor : t.randomCursor = s.randomCursor
  output : t.output = s.output
  tapes : ∀ i, i = 4 ∨ 10 ≤ i → i ∉ recordWork → t.tapes i = s.tapes i

theorem RecordFrame.refl (s : BitRAMState) : RecordFrame s s := ⟨rfl, rfl, rfl, fun _ _ _ => rfl⟩
theorem RecordFrame.trans {s t u : BitRAMState} (h : RecordFrame s t) (k : RecordFrame t u) : RecordFrame s u :=
  ⟨k.inputHead.trans h.inputHead, k.randomCursor.trans h.randomCursor, k.output.trans h.output,
    fun i hi hn => (k.tapes i hi hn).trans (h.tapes i hi hn)⟩

def recordCode (points : List Point) : Code := .seq Descriptors.readCode
  (.seq (listCode points) (.seq Descriptors.clearCode (BankArray.incrementCode 302)))
def recordBudget (points : List Point) (B : ℕ) : ℕ := 101000*(B+2)^2+listBudget points B

/-- One pass over one actual descriptor: read its five fields, scatter its
fixed prototype, reclaim the fields, and advance the descriptor index. -/
theorem record {n cells : ℕ} (d : Descriptors.Data n) (l : Dense.Layout cells)
    (points : List Point) (locations : Fin n → Point → Fin cells)
    (nums dens : Vector (List Bool) cells) (ny nz B : ℕ)
    (hd : d.Sized B) (hl : l.Sized B) (hwidth : d.width = l.width)
    (hsep : SeparatedData d l) (hcells : cells < 2^B)
    (i : Fin n) (hindex : ∀ p ∈ points, flatIndex (anchor d i) p ny nz = (locations i p).val)
    (hroom : ∀ p ∈ points, ∀ j, 0 ≤ (anchor d i j : ℤ)+p j)
    (hnyB : ny.bits.length ≤ B) (hnzB : nz.bits.length ≤ B)
    (input : List Bool) (tape : ℕ → Bool) (index : List Bool)
    (hi : addressValue index = i.val) (hil : index.length ≤ B) (s : Store)
    (hs : PointReady s.val) (hsd : Descriptors.Stored d s.val) (hsl : Dense.Stored l nums dens s.val)
    (hsi : BankArray.Word s.val 302 index) (hbank : Descriptors.Bank s.val (fun _ => 0))
    (hny : Word s.val 251 ny) (hnz : Word s.val 252 nz) :
    ∃ cost t, cost ≤ recordBudget points B ∧ Executes input tape (recordCode points) cost s t ∧
      PointReady t.val ∧ Descriptors.Stored d t.val ∧ Descriptors.Bank t.val (fun _ => 0) ∧
      Dense.Stored l
        (scatterWords nums (points.map (locations i))
          (FixedWidth.bits (addressValue l.width) (Descriptors.value d i 3).bits))
        (scatterWords dens (points.map (locations i))
          (FixedWidth.bits (addressValue l.width) (Descriptors.value d i 4).bits)) t.val ∧
      BankArray.Word t.val 302 (Increment.bits index) ∧ RecordFrame s.val t.val ∧ Dense.Outside l s.val t.val := by
  obtain ⟨rc, a, hrc, er, har, had, hav, fa⟩ := Descriptors.read d i B hd input tape index hi hil
    s hs.1 hsd hsi hbank
  have hap : PointReady a.val :=
    ⟨har, blank_of_eq (fa.tapes 37 (by omega) (by decide)) hs.2.1,
      blank_of_eq (fa.tapes 292 (by omega) (by decide)) hs.2.2.1,
      blank_of_eq (fa.tapes 322 (by omega) (by decide)) hs.2.2.2.1,
      fun j => blank_of_eq (fa.tapes (324+j.val) (by omega) (by simp [Descriptors.targets]; omega)) (hs.2.2.2.2 j)⟩
  have hal : Dense.Stored l nums dens a.val :=
    ⟨BankArray.word_of_eq (fa.tapes 300 (by omega) (by decide)) hsl.width,
      BankArray.word_of_eq (fa.tapes 301 (by omega) (by decide)) hsl.clock,
      BankArray.word_of_eq (fa.tapes 320 (by omega) (by decide)) hsl.numBase,
      BankArray.word_of_eq (fa.tapes 321 (by omega) (by decide)) hsl.denBase,
      by simpa only [fa.memory] using hsl.nums, by simpa only [fa.memory] using hsl.dens⟩
  have hanchor (j : Fin 3) : Word a.val (294+j.val) (anchor d i j) := by
    fin_cases j
    · exact hav 0
    · exact hav 1
    · exact hav 2
  have vb (j : Fin 5) : (Descriptors.value d i j).bits.length ≤ B :=
    (Descriptors.value_bits d i j s.val hsd).trans hd.2.1
  have vfit (j : Fin 5) : (Descriptors.value d i j).bits.length ≤ addressValue l.width := by
    rw [← hwidth]
    exact Descriptors.value_bits d i j s.val hsd
  have ab (j : Fin 3) : (anchor d i j).bits.length ≤ B := vb ⟨j.val, by omega⟩
  obtain ⟨lc, b, hlc, el, hbp, hbl, fb, ob⟩ := list_executes l nums dens (anchor d i) points (locations i)
    ny nz B (Descriptors.value d i 3) (Descriptors.value d i 4) hl hcells hindex ab hroom hnyB hnzB
    (vfit 3) (vfit 4) input tape a hap hal hanchor
    (word_of_eq (fa.tapes 251 (by omega) (by decide)) hny)
    (word_of_eq (fa.tapes 252 (by omega) (by decide)) hnz) (hav 3) (hav 4)
  have hbd : Descriptors.Stored d b.val := preserve_descriptors d l hsep had ob
    (fun j hj => fb.tapes j (by omega) (by simp [work]; omega))
  have hbv : Descriptors.Bank b.val (Descriptors.value d i) := by
    intro j
    exact word_of_eq (fb.tapes (Descriptors.targetTape j)
      (by have := Descriptors.targetTape_bounds j; omega) (by fin_cases j <;> decide)) (hav j)
  obtain ⟨cc, c, hcc, ec, hcr, hcv, fc⟩ := Descriptors.clear input tape (Descriptors.value d i) B vb b hbp.1 hbv
  have hcp : PointReady c.val :=
    ⟨hcr, blank_of_eq (fc.tapes 37 (by omega) (by decide)) hbp.2.1,
      blank_of_eq (fc.tapes 292 (by omega) (by decide)) hbp.2.2.1,
      blank_of_eq (fc.tapes 322 (by omega) (by decide)) hbp.2.2.2.1,
      fun j => blank_of_eq (fc.tapes (324+j.val) (by omega) (by simp [Descriptors.targets]; omega)) (hbp.2.2.2.2 j)⟩
  have hcd := hbd.of_frame fc
  have hcl : Dense.Stored l _ _ c.val :=
    ⟨BankArray.word_of_eq (fc.tapes 300 (by omega) (by decide)) hbl.width,
      BankArray.word_of_eq (fc.tapes 301 (by omega) (by decide)) hbl.clock,
      BankArray.word_of_eq (fc.tapes 320 (by omega) (by decide)) hbl.numBase,
      BankArray.word_of_eq (fc.tapes 321 (by omega) (by decide)) hbl.denBase,
      by simpa only [fc.memory] using hbl.nums, by simpa only [fc.memory] using hbl.dens⟩
  have hci : BankArray.Word c.val 302 index := BankArray.word_of_eq
    ((fc.tapes 302 (by omega) (by decide)).trans ((fb.tapes 302 (by omega) (by decide)).trans
      (fa.tapes 302 (by omega) (by decide)))) hsi
  obtain ⟨ic, t, hic, ei, hti, _, htm, _, keep, fi⟩ := BankArray.increment_bank
    302 (by decide) input tape index c hci hcr.scratch
  have htp : PointReady t.val :=
    ⟨(fun j hj => blank_of_eq (keep j (by omega)) (hcr j hj)),
      blank_of_eq (keep 37 (by decide)) hcp.2.1,
      blank_of_eq (keep 292 (by decide)) hcp.2.2.1,
      blank_of_eq (keep 322 (by decide)) hcp.2.2.2.1,
      fun j => blank_of_eq (keep (324+j.val) (by omega)) (hcp.2.2.2.2 j)⟩
  refine ⟨rc+(lc+(cc+ic)), t, ?_, er.seq (el.seq (ec.seq ei)), htp, ?_, ?_, ?_, hti, ?_,
    (((Dense.Outside.of_memory l fa.memory).trans ob).trans (Dense.Outside.of_memory l fc.memory)).trans
      (Dense.Outside.of_memory l htm)⟩
  · dsimp only [recordBudget]
    nlinarith
  · refine ⟨BankArray.word_of_eq (keep 300 (by decide)) hcd.width,
      BankArray.word_of_eq (keep 301 (by decide)) hcd.clock, ?_, ?_⟩
    · intro j
      exact BankArray.word_of_eq (keep (Descriptors.baseTape j) (by simp only [Descriptors.baseTape]; omega)) (hcd.bases j)
    · intro j
      simpa only [htm] using hcd.arrays j
  · intro j
    exact word_of_eq (keep (Descriptors.targetTape j) (by have := Descriptors.targetTape_bounds j; omega)) (hcv j)
  · exact ⟨BankArray.word_of_eq (keep 300 (by decide)) hcl.width,
      BankArray.word_of_eq (keep 301 (by decide)) hcl.clock,
      BankArray.word_of_eq (keep 320 (by decide)) hcl.numBase,
      BankArray.word_of_eq (keep 321 (by decide)) hcl.denBase,
      by simpa only [htm] using hcl.nums, by simpa only [htm] using hcl.dens⟩
  · refine ⟨fi.1.trans (fc.inputHead.trans (fb.inputHead.trans fa.inputHead)),
      fi.2.1.trans (fc.randomCursor.trans (fb.randomCursor.trans fa.randomCursor)),
      fi.2.2.1.trans (fc.output.trans (fb.output.trans fa.output)), ?_⟩
    intro j hj hn
    have hout : j ∉ Descriptors.targets ∧ j ∉ work ∧ j ≠ 302 := by
      simpa only [recordWork, Finset.mem_union, Finset.mem_singleton, not_or, and_assoc] using hn
    exact (keep j hout.2.2).trans ((fc.tapes j hj hout.1).trans
      ((fb.tapes j hj hout.2.1).trans (fa.tapes j hj hout.1)))

end Maxwell.Cost.PhysicalMaterial.Scatter
