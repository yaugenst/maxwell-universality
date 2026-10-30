import Maxwell.Continuum.CutoffMonomialOuterLoop
import Maxwell.Continuum.CutoffCacheBoundary

/-! The same fixed cache recurrence retains both actual allocated bounds. -/
namespace Maxwell.Continuum.Calibration.RawCutoff
open RationalDataflow RationalDataflow.PartArray Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 3500000
set_option maxRecDepth 32768

theorem monomialOuter_bounded_executes {D W H : ℕ} (a : MonomialCache D) (coeff : ℕ→Parts)
    (hw : ∀r<D,(coeff r).Width W) (hc : ∀r,(coeff r).Valid) (ha : a.Valid W coeff 0) (hb : a.EndsBefore H)
    (xs : List Bool) (hn : addressValue xs=D) (hlen : xs.length≤monomialWorkingWidth D W)
    (input : List Bool) (tape : ℕ→Bool) (origin : ℤ) (s : Store)
    (hs : a.Ready W 0 xs s) (hcount : s.val.tapes 207=BitTape.shifted xs origin) :
    ∃ (cost : ℕ) (t : Store) (finalWord : List Bool) (b : MonomialCache D),
      Executes input tape monomialOuterCode cost s t ∧
      cost≤monomialOuterCost D W xs.length ∧ b.Valid W coeff D ∧ b.Ready W D xs t ∧ b.EndsBefore H ∧
      t.val.tapes 207=BitTape.shifted finalWord origin ∧ finalWord.length=xs.length := by
  let inv : ℕ→Store→Prop := fun remaining st => remaining≤D ∧
    ∃b : MonomialCache D,b.Valid W coeff (D-remaining) ∧ b.Ready W (D-remaining) xs st ∧ b.EndsBefore H
  have stable : ∀r s t,CountedShifted.Frame 207 s t → inv r s → inv r t := by
    intro r s t f hh
    obtain ⟨b,hb,hr,hend⟩ := hh.2
    exact ⟨hh.1,b,hb,hr.outer_count_frame f,hend⟩
  have step : ∀r ys st,inv (r+1) st → st.val.tapes 207=BitTape.shifted ys origin →
      addressValue ys=r → ys.length=xs.length →
      ∃ cost t,Executes input tape monomialOuterStepCode cost st t ∧ inv r t ∧
        t.val.tapes 207=BitTape.shifted ys origin ∧
        cost≤2^116*(D+1)*(monomialWorkingWidth D W+16)^2 := by
    intro r ys st hh hword _ _
    obtain ⟨b,hb,hr,hend⟩ := hh.2
    have hlt : D-(r+1)<D := by have := hh.1;omega
    have heq : D-(r+1)+1=D-r := by have := hh.1;omega
    obtain ⟨cost,t,ex,hcst,rt,ft⟩ := monomialOuterStep_executes b coeff hw hc (D-(r+1)) hlt
      hb xs hn hlen input tape st hr
    refine ⟨cost,t,ex,⟨by omega,b.next (D-(r+1)),?_,?_,hend.next _⟩,ft.trans hword,hcst⟩
    · simpa only [heq] using hb.next hlt hw hc
    · simpa only [heq] using rt
  obtain ⟨cost,t,finalWord,ex,hfinal,hword,hl,_,hcost⟩ := counted_executes_sized 207 origin
    monomialOuterStepCode input tape xs.length inv
    (fun _ => 2^116*(D+1)*(monomialWorkingWidth D W+16)^2) stable step D xs s hn hcount rfl
    ⟨le_rfl,a,by simpa only [Nat.sub_self] using ha,by simpa only [Nat.sub_self] using hs,hb⟩
  obtain ⟨b,hb,hr,hend⟩ := hfinal.2
  exact ⟨cost,t,finalWord,b,ex,by simpa only [monomialOuterCost,Finset.sum_const,Finset.card_range,
    smul_eq_mul] using hcost,by simpa only [Nat.sub_zero] using hb,
    by simpa only [Nat.sub_zero] using hr,hend,hword,hl⟩


#print axioms monomialOuter_bounded_executes
end Maxwell.Continuum.Calibration.RawCutoff
