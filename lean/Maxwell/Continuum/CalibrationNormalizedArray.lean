import Maxwell.Continuum.CalibrationNormalizedArrayState

/-! A single fixed counted program materializes every normalized rational
coordinate of the current power buffer. Raw word bounds are derived at
each iteration from the original arrays and one computed common scale. -/

namespace Maxwell.Continuum.Calibration.PowerMachine.NormalizedEntry

open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.CalibrationMatrix
open RationalDataflow RationalDataflow.PartArray
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

def arrayBody : Code := .seq code writeCode
def arrayCode : Code := countedProgram 140 arrayBody
def arrayCost (n B length : ℕ) : ℕ := (n+1)*(13*length+15)+n*(2^25*(B+5)^2)

theorem array_executes {n : ℕ} (a : CalibrationMatrix.Data n n) (b : Table n)
    (scale denominator B : ℕ) (hB : 0<B) (haSize : a.Sized B) (hbMeta : b.MetadataWidth B)
    (hscale : addressValue a.width+scale.bits.length≤B) (hden : denominator.bits.length≤B)
    (hslot : B≤addressValue b.width) (hsep : b.Separated) (hdisjoint : SeparatedFrom a b)
    (v : ℕ → ℕ) (hvs : v 551=scale) (hvd : v 552=denominator)
    (hv : ∀ k∈ids, (v k).bits.length≤B)
    (input : List Bool) (tape : ℕ → Bool) (xs : List Bool) (origin : ℤ)
    (hlen : xs.length≤B) (s : Store) (hn : addressValue xs=n)
    (hcount : s.val.tapes 140=BitTape.shifted xs origin)
    (hs : NatAssign.Bank ids v s.val) (ha : CalibrationMatrix.Stored a s.val) (hb : b.OutputReady s) :
    ∃ cost t finalWord w, Executes input tape arrayCode cost s t ∧
      cost≤arrayCost n B xs.length ∧ CalibrationMatrix.Stored a t.val ∧
      (b.filled (entry a scale denominator) 0).OutputReady t ∧
      NatAssign.Bank ids w t.val ∧ w 551=scale ∧ w 552=denominator ∧
      (∀ k∈ids, (w k).bits.length≤B) ∧
      t.val.tapes 140=BitTape.shifted finalWord origin ∧ finalWord.length=xs.length := by
  let value := entry a scale denominator
  let inv : ℕ → Store → Prop := fun remaining st => remaining≤n ∧
    CalibrationMatrix.Stored a st.val ∧ (b.filled value remaining).OutputReady st ∧
      ∃ w, NatAssign.Bank ids w st.val ∧ w 551=scale ∧ w 552=denominator ∧
        ∀ k∈ids, (w k).bits.length≤B
  have stable : ∀ r s t, CountedShifted.Frame 140 s t → inv r s → inv r t := by
    intro r s t f hh
    obtain ⟨hr,ha',hb',w,hw,hws,hwd,hwidth⟩ := hh
    exact ⟨hr,stored_count_frame ha' f,output_count_frame hb' f,w,
      bank_count_frame hw f,hws,hwd,hwidth⟩
  have step : ∀ r ys st, inv (r+1) st → st.val.tapes 140=BitTape.shifted ys origin →
      addressValue ys=r → ys.length=xs.length →
      ∃ cost out, Executes input tape arrayBody cost st out ∧ inv r out ∧
        out.val.tapes 140=BitTape.shifted ys origin ∧ cost≤2^25*(B+5)^2 := by
    intro r ys st hh hword hvalue hlength
    obtain ⟨hr,ha',hb',w,hw,hws,hwd,hwidth⟩ := hh
    have hrn : r<n := by omega
    let i : Fin n := ⟨r,hrn⟩
    obtain ⟨cr,u,er,hcr,br,zr,sevenr,ar,fr⟩ := executes a B i haSize w hwidth
      input tape ys hvalue (by omega) st ha' hb'.scratch hb'.seven hw ⟨origin,hword⟩
    have outputReady := output_read_frame hb' fr zr sevenr
    have ewidth : (entry a (w 551) (w 552) i).Width B := by
      rw [hws,hwd]
      exact entry_width a scale denominator B hscale hden ar i
    have fit : (storedEntry (values a i w)).Width (addressValue b.width) := by
      rw [storedEntry_values]
      exact ewidth.mono hslot
    have index1 : u.val.tapes 140=BitTape.shifted ys origin :=
      (fr.tapes 140 (by decide) (by decide) (by decide)).trans hword
    obtain ⟨cw,t,ew,hcw,bw,bt,mt,ft⟩ := write_executes (b.filled value (r+1)) (values a i w) i
      (hB.trans_le hslot) fit hsep input tape ys hvalue u br outputReady ⟨origin,index1⟩
    have arrayStored : CalibrationMatrix.Stored a t.val :=
      stored_write_frame ar hdisjoint i (storedEntry (values a i w)) mt ft
    have evalue : storedEntry (values a i w)=value i := by
      rw [storedEntry_values,hws,hwd]
    have output : (b.filled value r).OutputReady t := by
      rw [evalue,Table.filled_step] at bt
      exact bt
    have hnextS : values a i w 551=scale := by simpa [values] using hws
    have hnextD : values a i w 552=denominator := by simpa [values] using hwd
    refine ⟨cr+cw,t,er.seq ew,⟨by omega,arrayStored,output,values a i w,bw,hnextS,hnextD,
      values_width a i w B hwidth ewidth⟩,
      (ft.2.2.2.1 140 (Or.inr (by decide)) (by decide)).trans index1,?_⟩
    change cw≤(b.filled value (r+1)).writeCost ys (storedEntry (values a i w)) at hcw
    have writeBound := (b.filled value (r+1)).writeCost_bound B
      ⟨hbMeta.width,hbMeta.basePositive,hbMeta.baseNegative,hbMeta.baseDenominator,hbMeta.clock⟩
      ys (by omega) (storedEntry (values a i w))
    nlinarith only [hcr,hcw,writeBound]
  have initial : inv n s :=
    ⟨le_rfl,ha,by simpa only [Table.filled_initial] using hb,v,hs,hvs,hvd,hv⟩
  obtain ⟨cost,t,finalWord,he,final,hword,hl,_,hcost⟩ := counted_executes_sized 140 origin
    arrayBody input tape xs.length inv (fun _ => 2^25*(B+5)^2) stable step n xs s
    hn hcount rfl initial
  obtain ⟨_,arrayStored,bt,w,bw,hws,hwd,hwidth⟩ := final
  refine ⟨cost,t,finalWord,w,he,?_,arrayStored,bt,bw,hws,hwd,hwidth,hword,hl⟩
  simpa only [Finset.sum_const,Finset.card_range,smul_eq_mul,arrayCost] using hcost

theorem output_value {n : ℕ} (a : CalibrationMatrix.Data n n) (b : Table n)
    (scale denominator : ℕ) {s : BitRAMState} (ha : CalibrationMatrix.Stored a s)
    (hscale : addressValue a.width+scale.bits.length≤addressValue b.width)
    (hden : denominator.bits.length≤addressValue b.width) (i : Fin n) :
    ((b.filled (entry a scale denominator) 0).get i).value=
      ((addressValue (a.vectorPositive.get i):ℚ)-addressValue (a.vectorNegative.get i))*
        ((scale:ℚ)/denominator) := by
  rw [Table.filled_get b _ (entry_width a scale denominator _ hscale hden ha),entry_value]

#print axioms array_executes
#print axioms output_value

end Maxwell.Continuum.Calibration.PowerMachine.NormalizedEntry
