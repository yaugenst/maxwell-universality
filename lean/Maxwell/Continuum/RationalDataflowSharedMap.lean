import Maxwell.Continuum.RationalDataflowSharedMapState
import Maxwell.Continuum.RationalDataflowArrayOutputCost

/-! One fixed program converts every runtime coefficient and writes all output channels. -/
namespace Maxwell.Continuum.RationalDataflow.PartArray
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 3500000
set_option maxRecDepth 8192

def sharedMapBody : Code := .seq (readCode 1) (.seq (SharedConversion.convertCode 0 1 2) (writeCode 1))
def sharedMapCode : Code := countedProgram 201 sharedMapBody
def sharedMapCost (n B wordLength : ℕ) : ℕ :=
  (n+1)*(13*wordLength+15)+n*(2^105*(B+5)^2)

theorem sharedMap_executes {n : ℕ} (a b : Table n) (W B : ℕ) (hW : 1≤W)
    (haWidth : ∀ i, (a.get i).Width W) (haValid : ∀ i, (a.get i).Valid)
    (haMeta : a.MetadataWidth B) (hbMeta : b.MetadataWidth B)
    (hbudget : sharedWidth n W≤B) (hslot : sharedWidth n W≤addressValue b.width)
    (hsep : b.Separated) (hdisjoint : a.SeparatedFrom b)
    (v : ℕ→Parts) (hv : WidthBank sharedSlots (sharedWidth n W) v)
    (hD : (v 0).positive=SharedTable.denominator a.get)
    (input : List Bool) (tape : ℕ→Bool) (xs : List Bool) (origin : ℤ)
    (hlen : xs.length≤B) (s : Store) (hn : addressValue xs=n)
    (hcount : s.val.tapes 201=BitTape.shifted xs origin)
    (hs : SharedConversion.Ready sharedSlots v s) (ha : a.Ready s) (hb : b.OutputReady s) :
    ∃ cost t finalWord, Executes input tape sharedMapCode cost s t ∧
      cost≤sharedMapCost n B xs.length ∧
      SharedConversion.Ready sharedSlots (sharedState a v n) t ∧ a.Ready t ∧
      (b.filled (SharedTable.integerParts a.get) 0).OutputReady t ∧
      t.val.tapes 201=BitTape.shifted finalWord origin ∧ finalWord.length=xs.length := by
  let value : Fin n→Parts := SharedTable.integerParts a.get
  let inv : ℕ→Store→Prop := fun remaining st =>
    remaining≤n ∧ SharedConversion.Ready sharedSlots (sharedState a v (n-remaining)) st ∧
      a.Ready st ∧ (b.filled value remaining).OutputReady st
  have stable : ∀ r s t, CountedShifted.Frame 201 s t → inv r s → inv r t := by
    intro r s t f hh
    exact ⟨hh.1,sharedReady_count_frame hh.2.1 f,hh.2.2.1.count_frame f,hh.2.2.2.count_frame f⟩
  have step : ∀ r ys st, inv (r+1) st → st.val.tapes 201=BitTape.shifted ys origin →
      addressValue ys=r → ys.length=xs.length →
      ∃ cost out, Executes input tape sharedMapBody cost st out ∧ inv r out ∧
        out.val.tapes 201=BitTape.shifted ys origin ∧ cost≤2^105*(B+5)^2 := by
    intro r ys st hh hword hvalue hlength
    have hr : r<n := by have := hh.1; omega
    let k := n-(r+1)
    have hk : k<n := by dsimp [k]; omega
    have hindex : n-1-k=r := by dsimp [k]; omega
    have hnext : k+1=n-r := by dsimp [k]; omega
    have hget : a.getD (n-1-k)=a.get ⟨r,hr⟩ := by simp only [hindex,Table.getD,dite_eq_left hr]
    obtain ⟨cr,t1,er,hcr,r1,a1,_,f1⟩ := read_executes a sharedSlots 1 (by decide)
      (sharedState a v k) input tape ys ⟨r,hr⟩ hvalue st hh.2.1.rational hh.2.2.1 ⟨origin,hword⟩
    have r1' : RationalDataflow.Ready sharedSlots (sharedLoaded a v k) t1 := by
      simpa only [sharedLoaded,sharedState,programLoaded,hget] using r1
    have e1 : SharedConversion.Ready sharedSlots (sharedLoaded a v k) t1 :=
      sharedReady_read_frame hh.2.1 f1 (er.protectsTape 4 read_one_protects_four) r1'
    have b1 := hh.2.2.2.read_frame f1 a1.scratch a1.seven
    have hload : (sharedLoaded a v k 1).Valid := by
      simpa only [sharedLoaded,programLoaded,Function.update_self,hget] using haValid ⟨r,hr⟩
    have loadWidth := (sharedLoaded_width a v W hW haWidth hv hD k hk).mono hbudget
    obtain ⟨cc,t2,ec,hcc,e2,f2⟩ := SharedConversion.convert_executes sharedSlots 0 1 2
      (by decide) (by decide) (by decide) (by decide) _ hload B
      (by unfold sharedWidth at hbudget; nlinarith) loadWidth input tape t1 e1
    have a2 := a1.shared_frame sharedSlots f2 e2.2
    have b2 := b1.shared_frame sharedSlots f2 a2.scratch a2.seven
    have e2' : SharedConversion.Ready sharedSlots (sharedState a v (k+1)) t2 := e2
    have converted : sharedState a v (k+1) 1=value ⟨r,hr⟩ := by
      simpa only [hindex] using sharedState_entry a v hD k hk
    have fit : (sharedState a v (k+1) 1).Width (addressValue b.width) :=
      (sharedState_width a v W hW haWidth hv hD (k+1) (by omega) 1 (by decide)).mono hslot
    have index1 : t1.val.tapes 201=BitTape.shifted ys origin :=
      (f1.tapes 201 (by decide) (by decide)).trans hword
    have index2 : t2.val.tapes 201=BitTape.shifted ys origin :=
      (f2.tapes 201 (outside_shared_changed sharedSlots 201 (by decide))).trans index1
    obtain ⟨cw,t3,ew,hcw,e3,b3,m3,f3⟩ := write_executes (b.filled value (r+1)) sharedSlots 1
      (by decide) (sharedState a v (k+1)) ⟨r,hr⟩ (by
        change 0<addressValue b.width
        unfold sharedWidth at hslot
        nlinarith) fit hsep input tape ys hvalue t2 e2' b2 ⟨origin,index2⟩
    have a3 := a2.write_output_frame hdisjoint ⟨r,hr⟩ (sharedState a v (k+1) 1) m3 f3 b3.scratch b3.seven
    have b3' : (b.filled value r).OutputReady t3 := by
      rw [converted,Table.filled_step] at b3
      exact b3
    have e3' : SharedConversion.Ready sharedSlots (sharedState a v (n-r)) t3 := by
      rwa [hnext] at e3
    refine ⟨cr+(cc+cw),t3,er.seq (ec.seq ew),⟨by omega,e3',a3,b3'⟩,
      (f3.2.2.2.1 201 (Or.inr (by decide)) (by decide)).trans index2,?_⟩
    have before := (sharedState_width a v W hW haWidth hv hD k hk.le).mono hbudget
    have readBound := a.readCost_bound B haMeta ys (by omega) _ (before 1 (by decide))
    change cw≤(b.filled value (r+1)).writeCost ys (sharedState a v (k+1) 1) at hcw
    have writeBound := (b.filled value (r+1)).writeCost_bound B
      ⟨hbMeta.width,hbMeta.basePositive,hbMeta.baseNegative,hbMeta.baseDenominator,hbMeta.clock⟩ ys (by omega)
      (sharedState a v (k+1) 1)
    have hcc' : cc≤2^102*(B+5)^2 := hcc.trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega : B+2≤B+5) 2))
    calc
      _ ≤ (2^20+2^102+2^20)*(B+5)^2 := by nlinarith only [hcr,readBound,hcc',hcw,writeBound]
      _ ≤ _ := Nat.mul_le_mul_right _ (by norm_num)
  have initial : inv n s := by
    refine ⟨le_rfl,?_,ha,?_⟩
    · simpa only [Nat.sub_self,sharedState,programIterate] using hs
    · simpa only [Table.filled_initial] using hb
  obtain ⟨cost,t,finalWord,hex,hfinal,hword,hl,_,hcost⟩ := counted_executes_sized 201 origin
    sharedMapBody input tape xs.length inv (fun _ => 2^105*(B+5)^2) stable step n xs s
    hn hcount rfl initial
  refine ⟨cost,t,finalWord,hex,?_,?_,hfinal.2.2.1,hfinal.2.2.2,hword,hl⟩
  · simpa only [Finset.sum_const,Finset.card_range,smul_eq_mul,sharedMapCost] using hcost
  · simpa only [Nat.sub_zero] using hfinal.2.1

#print axioms sharedMap_executes
end Maxwell.Continuum.RationalDataflow.PartArray
