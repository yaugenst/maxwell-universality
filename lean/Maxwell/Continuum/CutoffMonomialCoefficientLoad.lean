import Maxwell.Continuum.CutoffMonomialCoefficients
import Maxwell.Continuum.RationalDataflowLaneCopy

/-! The actual indexed copy puts profile coefficients in the fourth lane,
while preserving all initialized polynomial coefficients and the sentinel. -/
namespace Maxwell.Continuum.Calibration.RawCutoff
open RationalDataflow RationalDataflow.PartArray Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 2500000
set_option maxRecDepth 16384

theorem monomialCoefficientLoad_other {D : ℕ} (a : Table D) (b : Table (4*(D+1)))
    (k i : ℕ) (hi : ∀r,4*r+7≠i) :
    (laneCopyTable a b 4 7 k).getD i=b.getD i := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [laneCopyTable,Table.setD_getD_ne _ _ _ _ (hi _)]
    exact ih

theorem monomialCoefficientLoad_partial {D : ℕ} (a : Table D) (b : Table (4*(D+1)))
    (hfit : ∀r : Fin D,(a.getD r.val).Width (addressValue b.width))
    (k : ℕ) (hk : k≤D) :
    ∀r : Fin D,D-k≤r.val → (laneCopyTable a b 4 7 k).getD (4*r.val+7)=a.getD r.val := by
  induction k with
  | zero => intro r hr;omega
  | succ k ih =>
    intro r hr
    have hkd : k<D := by omega
    have hrow : D-1-k<D := by omega
    by_cases he : r.val=D-1-k
    · rw [laneCopyTable,he]
      apply Table.setD_getD_eq _ _ (by omega)
      simpa only [(laneCopyTable_metadata a b 4 7 k).1] using hfit ⟨D-1-k,hrow⟩
    · rw [laneCopyTable,Table.setD_getD_ne _ _ _ _ (by omega)]
      exact ih hkd.le r (by omega)

theorem monomialCoefficientLoad_coefficients {D : ℕ} (a : Table D) (b : Table (4*(D+1)))
    (hfit : ∀r : Fin D,(a.getD r.val).Width (addressValue b.width)) :
    MonomialCoefficientsStored (laneCopyTable a b 4 7 D) a.getD := by
  intro r
  exact monomialCoefficientLoad_partial a b hfit D le_rfl r (by omega)

theorem monomialCoefficientLoad_stored {D : ℕ} (a : Table D) (b : Table (4*(D+1)))
    (x : MonomialState D) (h : MonomialStored b x) (k : ℕ) :
    MonomialStored (laneCopyTable a b 4 7 k) x := by
  refine ⟨?_,?_⟩
  · exact (monomialCoefficientLoad_other a b k 1 (by intro r;omega)).trans h.1
  · intro r
    refine ⟨?_,?_,?_⟩
    · exact (monomialCoefficientLoad_other a b k (4*r.val+4) (by intro s;omega)).trans (h.2 r).1
    · exact (monomialCoefficientLoad_other a b k (4*r.val+5) (by intro s;omega)).trans (h.2 r).2.1
    · exact (monomialCoefficientLoad_other a b k (4*r.val+6) (by intro s;omega)).trans (h.2 r).2.2

theorem monomialCoefficientLoad_executes {D : ℕ} (a : Table D) (b : Table (4*(D+1)))
    (B : ℕ) (hB : 0<B) (haMeta : a.MetadataWidth B) (hbMeta : b.MetadataWidth B)
    (hslot : B≤addressValue b.width) (hsep : b.Separated) (hdisjoint : a.SeparatedFrom b)
    (x : MonomialState D) (hx : MonomialStored b x)
    (v : ℕ→Parts) (hv : WidthBank (Finset.range 8) B v)
    (input : List Bool) (tape : ℕ→Bool) (xs : List Bool) (origin : ℤ)
    (hlen : xs.length≤B) (s : Store) (hn : addressValue xs=D)
    (hcount : s.val.tapes 201=BitTape.shifted xs origin)
    (hs : RationalDataflow.Ready (Finset.range 8) v s) (ha : a.Ready s) (hb : b.OutputReady s)
    (hblank : ∀i∈RowIndex.ids,RationalAccumulator.Blank s.val i) :
    ∃ cost t finalWord, Executes input tape (laneCopyCode 4 7 1) cost s t ∧
      cost≤(D+1)*(13*xs.length+15)+D*(2^32*(B+12)^2) ∧
      RationalDataflow.Ready (Finset.range 8) (laneCopyValues a 1 v D) t ∧
      WidthBank (Finset.range 8) B (laneCopyValues a 1 v D) ∧ a.Ready t ∧
      (laneCopyTable a b 4 7 D).OutputReady t ∧
      (∀i∈RowIndex.ids,RationalAccumulator.Blank t.val i) ∧
      t.val.tapes 201=BitTape.shifted finalWord origin ∧ finalWord.length=xs.length ∧
      MonomialStored (laneCopyTable a b 4 7 D) x ∧
      MonomialCoefficientsStored (laneCopyTable a b 4 7 D) a.getD := by
  obtain ⟨cost,t,word,ex,hcost,rt,wt,at',bt,zt,hword,hl⟩ := laneCopy_executes a b 4 7 1
    (Finset.range 8) (by decide) B hB haMeta hbMeta hslot hsep hdisjoint
    (by intro r hr;omega) v hv input tape xs origin hlen s hn hcount hs ha hb hblank
  refine ⟨cost,t,word,ex,?_,rt,wt,at',bt,zt,hword,hl,
    monomialCoefficientLoad_stored a b x hx D,monomialCoefficientLoad_coefficients a b ?_⟩
  · simpa only [show (4:ℕ).bits.length=3 from by decide,show (7:ℕ).bits.length=3 from by decide,
      show B+3+3+6=B+12 by omega] using hcost
  · intro r
    simpa only [Table.getD,dite_eq_left r.isLt] using (a.get_width B haMeta s ha r).mono hslot

#print axioms monomialCoefficientLoad_executes
end Maxwell.Continuum.Calibration.RawCutoff
