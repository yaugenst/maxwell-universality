import Maxwell.Continuum.CalibrationSeedRootTableState
import Maxwell.Continuum.NaturalBankImportWord

/-! One descending table row: normalize the actual countdown word, run
the six producers, and extend the verified part of the stored coefficient table. -/
namespace Maxwell.Continuum.Calibration.SeedRoot
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

def tableBodyCode : Code := .seq (NaturalImport.code 801 780) rowEmissionCode
def tableBodyCost (B : ℕ) : ℕ := 37*B+39+rowEmissionCost B

theorem TableState.step_executes {M D B r : ℕ} {a : PartArray.Table (2*(2*D+1)^3)}
    {v : ℕ→Parts} {s : Store} (h : TableState M D B a v (r+1) s)
    (hB : 2≤B) (width : WidthBank slots B (resetParts v)) (good : Good slots (resetParts v))
    (metadata : a.MetadataWidth B) (entryWidth : ∀i,(a.get i).Width B) (entryValid : ∀i,(a.get i).Valid)
    (xs : List Bool) (hvalue : addressValue xs=r) (hlen : xs.length≤B)
    (input : List Bool) (tape : ℕ→Bool) (counter : BankArray.Word s.val 801 xs) :
    ∃cost t,Executes input tape tableBodyCode cost s t ∧ cost≤tableBodyCost B ∧
      Nonempty (TableState M D B a v r t) ∧ t.val.tapes 801=s.val.tapes 801 ∧
      t.val.inputHead=s.val.inputHead ∧ t.val.randomCursor=s.val.randomCursor ∧ t.val.output=s.val.output := by
  let row : Fin (ArrayDecodeMachine.aliasRowCount (3*M+D)) := ⟨r,by have :=h.remaining_le;omega⟩
  obtain ⟨c0,u,e0,h0,nu,f0⟩ := NaturalImport.executes rowIds 801 780 (by decide) (by decide)
    h.numbers xs input tape s h.natural counter
  rw [hvalue] at nu
  let n := Function.update h.numbers 780 r
  have indexWidth : r.bits.length≤B := by
    rw [←hvalue,Nat.size_eq_bits_len]
    exact (Nat.size_le.mpr (Subtraction.addressValue_lt_pow_length xs)).trans hlen
  have nw : ∀i∈rowIds,(n i).bits.length≤B := by
    intro i hi
    by_cases he : i=780
    · subst i
      exact indexWidth
    · simpa only [n,Function.update_of_ne he] using h.naturalWidth i hi
  have ru : Ready slots (resetParts v) u := by
    constructor
    · intro i hi
      have ne : i≠780 := by
        intro he
        subst i
        exact (by decide : 780∉RationalDataflow.ids slots) hi
      exact RationalAccumulator.word_of_eq (f0.tapes i (by simpa using ne)) (h.raw.1 i hi)
    · intro i hi
      exact RationalAccumulator.blank_of_eq (f0.tapes i (by simp;omega)) (h.raw.2 i hi)
  have four := RationalAccumulator.blank_of_eq (f0.tapes 4 (by decide)) h.four
  have arrays := PartArray.arrays_high_word (by decide : 216≤780) h.cache h.ready f0
  obtain ⟨c1,t,w,e1,h1,nt,nwt,keep,rt,zt,ta,tb,inp,rnd,out,tapes,entries⟩ := rowEmission_executes
    M D a h.table row n v B hB (by simpa [n] using h.size) (by simpa [n] using h.degree)
    (by simp [n,row]) (by simpa [n] using h.dimension) (by simpa [n] using h.side) nw width good
    metadata entryWidth entryValid h.metadata h.positive h.fits h.separated h.disjoint input tape u nu ru four arrays.1 arrays.2
  obtain ⟨mw,mp,mn,md,mc⟩ := phasesTable_metadata M D a row
    (decodedCoordinates (3*M+D) (3*row.val)) v phases h.table
  change (emittedRow M D a row v h.table).width=h.table.width at mw
  change (emittedRow M D a row v h.table).basePositive=h.table.basePositive at mp
  change (emittedRow M D a row v h.table).baseNegative=h.table.baseNegative at mn
  change (emittedRow M D a row v h.table).baseDenominator=h.table.baseDenominator at md
  change (emittedRow M D a row v h.table).clock=h.table.clock at mc
  have next : TableState M D B a v r t := {
    table := emittedRow M D a row v h.table
    remaining_le := by have :=h.remaining_le;omega
    numbers := w
    natural := nt
    naturalWidth := nwt
    size := (keep 750 (by decide)).trans (by simpa [n] using h.size)
    degree := (keep 751 (by decide)).trans (by simpa [n] using h.degree)
    dimension := (keep 785 (by decide)).trans (by simpa [n] using h.dimension)
    side := (keep 786 (by decide)).trans (by simpa [n] using h.side)
    raw := rt
    four := zt
    cache := ta
    ready := tb
    metadata := ⟨by simpa only [mw] using h.metadata.width,by simpa only [mp] using h.metadata.basePositive,
      by simpa only [mn] using h.metadata.baseNegative,by simpa only [md] using h.metadata.baseDenominator,
      by simpa only [mc] using h.metadata.clock⟩
    positive := by simpa only [mw] using h.positive
    fits := by simpa only [mw] using h.fits
    separated := by simpa only [PartArray.Table.Separated,mw,mp,mn,md] using h.separated
    disjoint := by simpa only [PartArray.Table.SeparatedFrom,mw,mp,mn,md] using h.disjoint
    correct := by
      intro q hq j p
      by_cases same : row=q
      · subst q
        exact emittedRow_get M D a row v h.table (fun p hp=>(entries p hp).2.mono h.fits) j p
      · rw [emittedRow_other M D a row q same v h.table j p]
        apply h.correct q _ j p
        have different : q.val≠r := fun he=>same (Fin.ext he.symm)
        omega }
  refine ⟨c0+c1,t,e0.seq e1,?_,⟨next⟩,
    (tapes 801 (by decide) (by decide)).trans (f0.tapes 801 (by decide)),
    inp.trans f0.inputHead,rnd.trans f0.randomCursor,out.trans f0.output⟩
  have old := h.naturalWidth 780 (by decide)
  unfold tableBodyCost
  omega

#print axioms TableState.step_executes
end Maxwell.Continuum.Calibration.SeedRoot
