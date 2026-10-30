import Maxwell.Continuum.CutoffMonomialAntiderivativeMachine
import Maxwell.Continuum.CutoffScalePreparationCost
import Maxwell.Continuum.RationalDataflowTableHeaderSwap

/-! One fixed program initializes the antiderivative arithmetic, converts
the actual strided cache, and exchanges the table descriptors. The resulting
ordinary input table is ready for the cutoff query program. -/
namespace Maxwell.Continuum.Calibration.RawCutoff
open RationalDataflow RationalDataflow.PartArray Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 3500000
set_option maxRecDepth 32768
attribute [local irreducible] scaleInitial antiderivativeScaleControl

def antiderivativePreparationCode : Code :=
  .seq scalePreparationCode (.seq monomialAntiderivativeCode headerSwapCode)

def antiderivativePreparationCost (n W len oldlen : ℕ) : ℕ :=
  scalePreparationCost n W len oldlen+monomialAntiderivativeCost n W len+
    256*(scaleWorkingWidth n W+1)

theorem monomialAntiderivative_protects_saved :
    monomialAntiderivativeCode.protectsTape 206=true := by
  unfold monomialAntiderivativeCode antiderivativeScaleControl
  decide

theorem monomialAntiderivative_protects_swap :
    monomialAntiderivativeCode.protectsTape 216=true := by
  unfold monomialAntiderivativeCode antiderivativeScaleControl
  decide

theorem antiderivativePreparation_executes {n : ℕ} (a : Table (4*(n+1))) (b : Table n)
    (W : ℕ) (hnpos : 0<n)
    (hw : ∀i:Fin n,(a.getD (4*i.val+6)).Width W)
    (hv : ∀i:Fin n,(a.getD (4*i.val+6)).Valid)
    (haMeta : a.MetadataWidth (scaleWorkingWidth n W))
    (hbMeta : b.MetadataWidth (scaleWorkingWidth n W))
    (hslot : scaleWorkingWidth n W≤addressValue b.width)
    (hsep : b.Separated) (hdisjoint : a.SeparatedFrom b)
    (v : ℕ→Parts) (hvw : WidthBank scaleSlots W v) (hvg : Good scaleSlots v)
    (input : List Bool) (tape : ℕ→Bool) (xs ys : List Bool)
    (hlen : xs.length≤scaleWorkingWidth n W) (s : Store) (hn : addressValue xs=n)
    (hsaved : BankArray.Word s.val 206 xs) (hcount : BankArray.Word s.val 201 ys)
    (hs : RationalDataflow.Ready scaleSlots v s) (ha : a.Ready s) (hb : b.OutputReady s)
    (hblank : ∀i∈RowIndex.ids,RationalAccumulator.Blank s.val i)
    (hswap : RationalAccumulator.Blank s.val 216) :
    ∃ cost t finalWord,Executes input tape antiderivativePreparationCode cost s t ∧
      cost≤antiderivativePreparationCost n W xs.length ys.length ∧
      RationalDataflow.Ready scaleSlots
        (iterate (monomialTotalTable a) 1 antiderivativeScaleControl (scaleInitial n) n) t ∧
      (b.filled (monomialAntiderivativeValues a) 0).Ready t ∧ a.OutputReady t ∧
      BankArray.Word t.val 206 xs ∧ BankArray.Word t.val 201 finalWord ∧
      finalWord.length=xs.length ∧ RationalAccumulator.Blank t.val 216 := by
  obtain ⟨c0,s0,e0,hc0,r0,saved0,count0⟩ := scalePreparation_executes n W hnpos v hvw hvg
    input tape xs ys hn s hs hsaved hcount
  have a0 := scalePreparation_table_frame ha e0 r0.2
  have b0 := scalePreparation_output_frame hb e0 a0.scratch a0.seven
  have z0 : ∀i∈RowIndex.ids,RationalAccumulator.Blank s0.val i := by
    intro i hi
    apply RationalAccumulator.blank_of_eq (scalePreparation_keeps e0 i _) (hblank i hi)
    simp only [RowIndex.ids,Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl <;> simp
  have swap0 := RationalAccumulator.blank_of_eq (scalePreparation_keeps e0 216 (by simp)) hswap
  obtain ⟨origin,count0⟩ := count0
  obtain ⟨c1,s1,finalWord,e1,hc1,r1,a1,b1,_,count1,hl⟩ := monomialAntiderivative_executes a b W hw hv
    haMeta hbMeta hslot hsep hdisjoint input tape xs origin hlen s0 hn count0 r0 a0 b0 z0
  have saved1 := BankArray.word_of_eq (e1.protectsTape 206 monomialAntiderivative_protects_saved) saved0
  have swap1 := RationalAccumulator.blank_of_eq
    (e1.protectsTape 216 monomialAntiderivative_protects_swap) swap0
  have meta1 : (b.filled (monomialAntiderivativeValues a) 0).MetadataWidth (scaleWorkingWidth n W) :=
    ⟨hbMeta.width,hbMeta.basePositive,hbMeta.baseNegative,hbMeta.baseDenominator,hbMeta.clock⟩
  obtain ⟨c2,t,e2,hc2,rt,bt,at',zt,ft⟩ := headerSwap_executes a
    (b.filled (monomialAntiderivativeValues a) 0) (scaleWorkingWidth n W) haMeta meta1
    scaleSlots _ input tape s1 r1 a1 b1 swap1
  refine ⟨c0+(c1+c2),t,finalWord,e0.seq (e1.seq e2),?_,rt,bt,at',?_,?_,hl,zt⟩
  · unfold antiderivativePreparationCost
    omega
  · exact BankArray.word_of_eq (ft.tapes 206 (by decide)) saved1
  · exact BankArray.word_of_eq (ft.tapes 201 (by decide)) ⟨origin,count1⟩

theorem antiderivativePreparationCost_polynomial (n W len oldlen : ℕ)
    (hlen : len≤W) (hold : oldlen≤W) :
    antiderivativePreparationCost n W len oldlen≤2^142*(n+W+4)^5 := by
  let Z := n+W+4
  have hZ : 1≤Z := by dsimp [Z];omega
  have hn : n+1≤Z := by dsimp [Z];omega
  have hW : W+2≤Z := by dsimp [Z];omega
  have hlen' : len≤scaleWorkingWidth n W := by unfold scaleWorkingWidth scaleStateWidth;omega
  have hscale := scalePreparationCost_polynomial n W len oldlen hlen hold
  have hmap := monomialAntiderivativeCost_polynomial n W len hlen'
  have hprod : (n+1)^3*(W+2)^2≤Z^5 := by
    have h := Nat.mul_le_mul (Nat.pow_le_pow_left hn 3) (Nat.pow_le_pow_left hW 2)
    simpa only [←pow_add] using h
  have hmap' : monomialAntiderivativeCost n W len≤2^140*Z^5 :=
    hmap.trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left (2^140) hprod)
  have h35 : Z^3≤Z^5 := Nat.pow_le_pow_right hZ (by decide)
  have h15 : Z≤Z^5 := le_self_pow₀ hZ (by decide)
  have hhead : 256*(scaleWorkingWidth n W+1)≤2^20*Z := by
    dsimp [Z,scaleWorkingWidth,scaleStateWidth]
    omega
  have hscale' : scalePreparationCost n W len oldlen≤2^128*Z^5 :=
    hscale.trans (Nat.mul_le_mul_left _ h35)
  have hhead' := hhead.trans (Nat.mul_le_mul_left (2^20) h15)
  unfold antiderivativePreparationCost
  change _≤2^142*Z^5
  nlinarith only [hmap',hscale',hhead',Nat.zero_le (Z^5)]

#print axioms antiderivativePreparation_executes
#print axioms antiderivativePreparationCost_polynomial
end Maxwell.Continuum.Calibration.RawCutoff
