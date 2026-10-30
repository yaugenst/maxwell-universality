import Maxwell.Continuum.CutoffMonomialOuterStep
import Maxwell.Continuum.CutoffMonomialPassCost

/-! A single fixed Boolean program traverses the runtime profile table.
All nested row passes execute, with polynomial costs derived from the actual
unreduced Chebyshev and weighted-sum recurrences. -/
namespace Maxwell.Continuum.Calibration.RawCutoff
open RationalDataflow RationalDataflow.PartArray Maxwell.Cost Maxwell.Cost.Structured Profile
set_option maxHeartbeats 3500000
set_option maxRecDepth 32768
set_option exponentiation.threshold 1024

def monomialOuterCode : Code := countedProgram 207 monomialOuterStepCode

def monomialOuterCost (D W len : ℕ) : ℕ :=
  (D+1)*(13*len+15)+D*(2^116*(D+1)*(monomialWorkingWidth D W+16)^2)

theorem MonomialCache.Ready.outer_count_frame {D W j : ℕ} {a : MonomialCache D}
    {xs : List Bool} {s t : Store} (h : a.Ready W j xs s) (f : CountedShifted.Frame 207 s t) :
    a.Ready W j xs t := by
  have ff : BinaryPrecision.Frame monomialControlPorts s.val t.val := by
    refine ⟨f.1,f.2.1,f.2.2.1,f.2.2.2.1,f.2.2.2.2.1,?_⟩
    intro i hi
    exact f.2.2.2.2.2.1 i (by intro he;subst i;exact hi (by decide))
  have hz : NatAssign.Scratch t.val := fun i hi =>
    RationalAccumulator.blank_of_eq (f.2.2.2.2.2.1 i (by omega)) (h.bank.2 i hi)
  have at' := monomialControl_table_frame h.current ff hz
  refine ⟨monomialControl_rational_frame h.bank ff hz,at',
    monomialControl_output_frame h.spare ff at'.scratch at'.seven,?_,
    RationalAccumulator.blank_of_eq (f.2.2.2.2.2.1 216 (by decide)) h.swapBlank,
    BankArray.word_of_eq (f.2.2.2.2.2.1 206 (by decide)) h.saved,?_,
    RationalAccumulator.word_of_eq (f.2.2.2.2.2.1 208 (by decide)) h.index,
    RationalAccumulator.word_of_eq (f.2.2.2.2.2.1 209 (by decide)) h.one⟩
  · intro i hi
    apply RationalAccumulator.blank_of_eq (f.2.2.2.2.2.1 i _) (h.indexBlanks i hi)
    simp only [RowIndex.ids,Finset.mem_insert,Finset.mem_singleton] at hi
    omega
  · obtain ⟨ys,hl,hy⟩ := h.count
    exact ⟨ys,hl,BankArray.word_of_eq (f.2.2.2.2.2.1 201 (by decide)) hy⟩

theorem monomialOuter_executes {D W : ℕ} (a : MonomialCache D) (coeff : ℕ→Parts)
    (hw : ∀r<D,(coeff r).Width W) (hc : ∀r,(coeff r).Valid) (ha : a.Valid W coeff 0)
    (xs : List Bool) (hn : addressValue xs=D) (hlen : xs.length≤monomialWorkingWidth D W)
    (input : List Bool) (tape : ℕ→Bool) (origin : ℤ) (s : Store)
    (hs : a.Ready W 0 xs s) (hcount : s.val.tapes 207=BitTape.shifted xs origin) :
    ∃ (cost : ℕ) (t : Store) (finalWord : List Bool) (b : MonomialCache D),
      Executes input tape monomialOuterCode cost s t ∧
      cost≤monomialOuterCost D W xs.length ∧ b.Valid W coeff D ∧ b.Ready W D xs t ∧
      t.val.tapes 207=BitTape.shifted finalWord origin ∧ finalWord.length=xs.length := by
  let inv : ℕ→Store→Prop := fun remaining st => remaining≤D ∧
    ∃b : MonomialCache D,b.Valid W coeff (D-remaining) ∧ b.Ready W (D-remaining) xs st
  have stable : ∀r s t,CountedShifted.Frame 207 s t → inv r s → inv r t := by
    intro r s t f hh
    obtain ⟨b,hb,hr⟩ := hh.2
    exact ⟨hh.1,b,hb,hr.outer_count_frame f⟩
  have step : ∀r ys st,inv (r+1) st → st.val.tapes 207=BitTape.shifted ys origin →
      addressValue ys=r → ys.length=xs.length →
      ∃ cost t,Executes input tape monomialOuterStepCode cost st t ∧ inv r t ∧
        t.val.tapes 207=BitTape.shifted ys origin ∧
        cost≤2^116*(D+1)*(monomialWorkingWidth D W+16)^2 := by
    intro r ys st hh hword _ _
    obtain ⟨b,hb,hr⟩ := hh.2
    have hlt : D-(r+1)<D := by have := hh.1;omega
    have heq : D-(r+1)+1=D-r := by have := hh.1;omega
    obtain ⟨cost,t,ex,hcst,rt,ft⟩ := monomialOuterStep_executes b coeff hw hc (D-(r+1)) hlt
      hb xs hn hlen input tape st hr
    refine ⟨cost,t,ex,⟨by omega,b.next (D-(r+1)),?_,?_⟩,ft.trans hword,hcst⟩
    · simpa only [heq] using hb.next hlt hw hc
    · simpa only [heq] using rt
  obtain ⟨cost,t,finalWord,ex,hfinal,hword,hl,_,hcost⟩ := counted_executes_sized 207 origin
    monomialOuterStepCode input tape xs.length inv
    (fun _ => 2^116*(D+1)*(monomialWorkingWidth D W+16)^2) stable step D xs s hn hcount rfl
    ⟨le_rfl,a,by simpa only [Nat.sub_self] using ha,by simpa only [Nat.sub_self] using hs⟩
  obtain ⟨b,hb,hr⟩ := hfinal.2
  exact ⟨cost,t,finalWord,b,ex,by simpa only [monomialOuterCost,Finset.sum_const,Finset.card_range,
    smul_eq_mul] using hcost,by simpa only [Nat.sub_zero] using hb,
    by simpa only [Nat.sub_zero] using hr,hword,hl⟩

theorem monomialOuterCost_polynomial (D W len : ℕ) (hlen : len≤monomialWorkingWidth D W) :
    monomialOuterCost D W len≤2^144*(D+1)^6*(W+1)^2 := by
  have hb := monomialWorkingWidth_polynomial D W
  have hc : (D+1)*(13*len+15)≤2^13*(D+1)^3*(W+1) := by
    calc
      _≤(D+1)*(16*(monomialWorkingWidth D W+16)) := by gcongr;omega
      _≤(D+1)*(16*(2^9*(D+1)^2*(W+1))) := by gcongr
      _=2^13*(D+1)^3*(W+1) := by ring
  have hl : D*(2^116*(D+1)*(monomialWorkingWidth D W+16)^2)≤2^134*(D+1)^6*(W+1)^2 := by
    calc
      _≤(D+1)*(2^116*(D+1)*(monomialWorkingWidth D W+16)^2) := by gcongr;omega
      _≤(D+1)*(2^116*(D+1)*(2^9*(D+1)^2*(W+1))^2) := by gcongr
      _=2^134*(D+1)^6*(W+1)^2 := by ring
  have hd : (D+1)^3≤(D+1)^6 := Nat.pow_le_pow_right (by omega) (by decide)
  have hw : W+1≤(W+1)^2 := le_self_pow₀ (by omega) (by decide : (2:ℕ)≠0)
  have hs := Nat.mul_le_mul_left (2^13) (Nat.mul_le_mul hd hw)
  unfold monomialOuterCost
  nlinarith only [hc,hl,hs]

theorem monomialOuterCost_precision (N len : ℕ)
    (hlen : len≤monomialWorkingWidth (profileDegree N) (272*(N+1))) :
    monomialOuterCost (profileDegree N) (272*(N+1)) len≤2^352*(N+1)^14 := by
  have hd := profileDegree_bound N
  have h1 : 1≤(N+1)^2 := one_le_pow₀ (by omega)
  have hd' : profileDegree N+1≤2^31*(N+1)^2 := by nlinarith
  have hw : 272*(N+1)+1≤2^9*(N+1) := by omega
  calc
    _≤2^144*(profileDegree N+1)^6*(272*(N+1)+1)^2 := monomialOuterCost_polynomial _ _ _ hlen
    _≤2^144*(2^31*(N+1)^2)^6*(2^9*(N+1))^2 := by gcongr
    _=2^348*(N+1)^14 := by ring
    _≤2^352*(N+1)^14 := Nat.mul_le_mul_right _ (by norm_num)

theorem monomialOuter_computes {D W : ℕ} (a : MonomialCache D) (coeff : ℕ→Parts)
    (hw : ∀r<D,(coeff r).Width W) (hc : ∀r,(coeff r).Valid) (ha : a.Valid W coeff 0)
    (xs : List Bool) (hn : addressValue xs=D) (hlen : xs.length≤monomialWorkingWidth D W)
    (input : List Bool) (tape : ℕ→Bool) (origin : ℤ) (s : Store)
    (hs : a.Ready W 0 xs s) (hcount : s.val.tapes 207=BitTape.shifted xs origin) :
    ∃ (t : Store) (b : MonomialCache D),
      (runPriced (monomialOuterCode.compile.next input tape) (monomialOuterCost D W xs.length+1) s.val).finished=
        some (t.place monomialOuterCode.size) ∧
      (runPriced (monomialOuterCode.compile.next input tape) (monomialOuterCost D W xs.length+1) s.val).instructions≤
        monomialOuterCost D W xs.length ∧ b.Valid W coeff D ∧ b.Ready W D xs t ∧
      MonomialStored b.current (monomialState D coeff D) := by
  obtain ⟨cost,t,_,b,ex,hcost,hb,hr,_,_⟩ := monomialOuter_executes a coeff hw hc ha xs hn hlen
    input tape origin s hs hcount
  obtain ⟨hrun,hsteps⟩ := ex.compiled_run (monomialOuterCost D W xs.length+1) (by omega)
  exact ⟨t,b,hrun,hsteps ▸ hcost,hb,hr,hb.stored⟩

#print axioms monomialOuter_computes
#print axioms monomialOuterCost_precision
end Maxwell.Continuum.Calibration.RawCutoff
