import Maxwell.Continuum.CutoffMonomialAntiderivative

/-! Actual strided cache reads and output writes construct the coefficient
table used by the fixed cutoff query. All scalar inverse and intermediate
width bounds follow from the generated cache entries. -/
namespace Maxwell.Continuum.Calibration.RawCutoff
open RationalDataflow RationalDataflow.PartArray Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384
attribute [local irreducible] scaleInitial antiderivativeScaleControl

def monomialAntiderivativeCost (n W wordLength : ℕ) : ℕ :=
  (n+1)*(13*wordLength+15)+n*rowMapStepCost 4 3 (scaleWorkingWidth n W)
    [(6,1)] antiderivativeScaleControl

theorem monomialAntiderivative_executes {n : ℕ} (a : Table (4*(n+1))) (b : Table n)
    (W : ℕ) (hw : ∀i:Fin n,(a.getD (4*i.val+6)).Width W)
    (hv : ∀i:Fin n,(a.getD (4*i.val+6)).Valid)
    (haMeta : a.MetadataWidth (scaleWorkingWidth n W))
    (hbMeta : b.MetadataWidth (scaleWorkingWidth n W))
    (hslot : scaleWorkingWidth n W≤addressValue b.width)
    (hsep : b.Separated) (hdisjoint : a.SeparatedFrom b)
    (input : List Bool) (tape : ℕ→Bool) (xs : List Bool) (origin : ℤ)
    (hlen : xs.length≤scaleWorkingWidth n W) (s : Store) (hn : addressValue xs=n)
    (hcount : s.val.tapes 201=BitTape.shifted xs origin)
    (hs : RationalDataflow.Ready scaleSlots (scaleInitial n) s)
    (ha : a.Ready s) (hb : b.OutputReady s)
    (hblank : ∀i∈RowIndex.ids,RationalAccumulator.Blank s.val i) :
    ∃ cost t finalWord,Executes input tape monomialAntiderivativeCode cost s t ∧
      cost≤monomialAntiderivativeCost n W xs.length ∧
      RationalDataflow.Ready scaleSlots
        (iterate (monomialTotalTable a) 1 antiderivativeScaleControl (scaleInitial n) n) t ∧
      a.Ready t ∧ (b.filled (monomialAntiderivativeValues a) 0).OutputReady t ∧
      (∀i∈RowIndex.ids,RationalAccumulator.Blank t.val i) ∧
      t.val.tapes 201=BitTape.shifted finalWord origin ∧ finalWord.length=xs.length := by
  have hw' : ∀i,(monomialTotalTable a).get i |>.Width W := by
    intro i
    rw [monomialTotalTable_get]
    exact hw i
  have hv' : ∀i,((monomialTotalTable a).get i).Valid := by
    intro i
    rw [monomialTotalTable_get]
    exact hv i
  have hSB : scaleStateWidth n W≤scaleWorkingWidth n W := by
    unfold scaleWorkingWidth
    omega
  obtain ⟨cost,t,finalWord,ex,hcost,rt,at',bt,zt,hword,hl⟩ := rowMap_executes a b scaleSlots
    4 3 [(6,1)] (by simp [scaleSlots]) (by decide)
    antiderivativeScaleControl antiderivativeScaleControl_valid 0 (by decide) (scaleInitial n)
    (scaleWorkingWidth n W) (by unfold scaleWorkingWidth;omega)
    haMeta hbMeta hslot hsep hdisjoint
    (fun k hk => by
      rw [monomialTotal_iterate a _ k hk.le]
      exact (scale_iterate_width (monomialTotalTable a) W hw' k hk.le).mono hSB)
    (fun k hk => by
      rw [monomialTotal_loaded a _ k hk]
      exact scale_loaded_widthTrace (monomialTotalTable a) W hw' k hk)
    (fun k hk => by
      rw [monomialTotal_loaded a _ k hk]
      exact scale_loaded_good (monomialTotalTable a) hv' k hk)
    (fun k hk => by
      rw [monomialTotal_loaded a _ k hk]
      exact scale_loaded_admissible (monomialTotalTable a) k hk)
    (by intro k hk x hx;simp only [List.mem_singleton] at hx;subst x;simp only;omega)
    input tape xs origin hlen s hn hcount hs ha hb hblank
  refine ⟨cost,t,finalWord,ex,hcost,?_,at',bt,zt,hword,hl⟩
  simpa only [monomialTotal_iterate a _ n le_rfl] using rt

theorem monomialAntiderivative_output {n : ℕ} (a : Table (4*(n+1))) (b : Table n) (W : ℕ)
    (hw : ∀i:Fin n,(a.getD (4*i.val+6)).Width W)
    (hv : ∀i:Fin n,(a.getD (4*i.val+6)).Valid)
    (hslot : scaleStateWidth n W≤addressValue b.width) (i : Fin n) :
    ((b.filled (monomialAntiderivativeValues a) 0).get i).Width (scaleStateWidth n W) ∧
    ((b.filled (monomialAntiderivativeValues a) 0).get i).Valid ∧
    (b.filled (monomialAntiderivativeValues a) 0).get i=monomialAntiderivativeValues a i := by
  have hfit : ∀j,(monomialAntiderivativeValues a j).Width (addressValue b.width) :=
    fun j => (monomialAntiderivativeValues_width a W hw j).mono hslot
  rw [Table.filled_get b _ hfit]
  exact ⟨monomialAntiderivativeValues_width a W hw i,monomialAntiderivativeValues_valid a hv i,rfl⟩

theorem monomialAntiderivativeCost_polynomial (n W wordLength : ℕ)
    (hlen : wordLength≤scaleWorkingWidth n W) :
    monomialAntiderivativeCost n W wordLength≤2^140*(n+1)^3*(W+2)^2 := by
  let B := scaleWorkingWidth n W
  have hB : B≤2^11*(n+1)*(W+2) := by
    dsimp [B,scaleWorkingWidth,scaleStateWidth]
    nlinarith
  have hp : 1≤(n+1)*(W+2) := Nat.succ_le_of_lt (by positivity)
  have hB12 : B+12≤2^12*(n+1)*(W+2) := by nlinarith
  have hb : 1≤(B+12)^2 := one_le_pow₀ (by omega)
  have hC : rowMapStepCost 4 3 B [(6,1)] antiderivativeScaleControl≤2^106*(B+12)^2 := by
    unfold rowMapStepCost rowFoldStepCost rowPlanCost operationCost
    rw [antiderivativeScaleControl_steps,show (4:ℕ).bits.length=3 from rfl]
    norm_num
    have hm1 := Nat.pow_le_pow_left (by omega : B+3≤B+12) 2
    have hm2 := Nat.pow_le_pow_left (by omega : B+6≤B+12) 2
    have hm3 := Nat.pow_le_pow_left (by omega : B+11≤B+12) 2
    nlinarith only [hm1,hm2,hm3,hb]
  have hcounter : (n+1)*(13*wordLength+15)≤32*(n+1)*(B+12)^2 := by
    have hlen' : wordLength≤B := hlen
    have hs : B+1≤(B+12)^2 := by nlinarith
    nlinarith only [hlen',hs]
  have hcost : monomialAntiderivativeCost n W wordLength≤2^107*(n+1)*(B+12)^2 := by
    unfold monomialAntiderivativeCost
    have hm := Nat.mul_le_mul_left n hC
    nlinarith only [hm,hcounter,Nat.zero_le ((B+12)^2)]
  have hm := Nat.mul_le_mul_left (2^107*(n+1)) (Nat.pow_le_pow_left hB12 2)
  calc
    _ ≤ 2^107*(n+1)*(B+12)^2 := hcost
    _ ≤ 2^107*(n+1)*(2^12*(n+1)*(W+2))^2 := hm
    _ ≤ 2^140*(n+1)^3*(W+2)^2 := by ring_nf;omega

#print axioms monomialAntiderivative_executes
#print axioms monomialAntiderivativeCost_polynomial
end Maxwell.Continuum.Calibration.RawCutoff
