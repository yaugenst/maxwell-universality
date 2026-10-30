import Maxwell.Continuum.CutoffMonomialLoaded
import Maxwell.Continuum.RationalDataflowWordReplace

/-! A fixed initializer writes every cache row, reloads the runtime coefficient
count, and copies either the profile rows or the first cache's coefficient lane. -/
namespace Maxwell.Continuum.Calibration.RawCutoff
open RationalDataflow RationalDataflow.PartArray Maxwell.Cost Maxwell.Cost.Structured
open RationalAccumulator (Blank)
set_option maxHeartbeats 4500000
set_option maxRecDepth 32768

def cacheSourceStride (second : Bool) : ℕ := if second then 4 else 1
def cacheSourceOffset (second : Bool) : ℕ := if second then 7 else 0

def monomialInitializeCode (second : Bool) : Code := .seq (WordReplace.code 725 201)
  (.seq monomialSeedCode (.seq (WordReplace.code 720 201)
    (laneCopyRowsCode (cacheSourceStride second) (cacheSourceOffset second) 4 7 1)))

def monomialInitializeCost (D B oldlen : ℕ) : ℕ :=
  6*oldlen+15*(4*(D+1)).bits.length+21+
    monomialSeedCost D B (4*(D+1)).bits.length+
    (6*(4*(D+1)).bits.length+15*D.bits.length+21)+
    (D+1)*(13*D.bits.length+15)+D*(2^32*(B+18)^2)

theorem seed_protects_cache_ports : ([216,720,725]:List ℕ).all
    (fun i => monomialSeedCode.protectsTape i)=true := by decide

theorem copyRows_protects_cache_ports (second : Bool) : ([216,720,725]:List ℕ).all
    (fun i => (laneCopyRowsCode (cacheSourceStride second) (cacheSourceOffset second) 4 7 1).protectsTape i)=true := by
  cases second <;> decide

theorem monomialInitialize_executes {n D : ℕ} (a : Table n) (b : Table (4*(D+1)))
    (second : Bool) (B V : ℕ) (hD : 2≤D) (hV : 1≤V) (hVB : V≤B)
    (haMeta : a.MetadataWidth B) (hbMeta : b.MetadataWidth B)
    (hslot : B≤addressValue b.width) (hsep : b.Separated) (hdisjoint : a.SeparatedFrom b)
    (hsource : ∀r<D,cacheSourceStride second*r+cacheSourceOffset second<n)
    (hDbits : D.bits.length≤B) (hsizebits : (4*(D+1)).bits.length≤B)
    (coeff : ℕ→Parts) (hcoeff : ∀r<D,a.getD (cacheSourceStride second*r+cacheSourceOffset second)=coeff r)
    (hc : ∀r<D,(coeff r).Valid) (hw : ∀r<D,(coeff r).Width V)
    (v : ℕ→Parts) (hv : WidthBank (Finset.range 8) V v) (hg : Good (Finset.range 8) v)
    (input : List Bool) (tape : ℕ→Bool) (oldWord : List Bool) (s : Store)
    (hs : RationalDataflow.Ready (Finset.range 8) v s) (ha : a.Ready s) (hb : b.OutputReady s)
    (hcount : BankArray.Word s.val 201 oldWord)
    (hdegree : RationalAccumulator.Word s.val 720 D)
    (hsize : RationalAccumulator.Word s.val 725 (4*(D+1)))
    (hblank : ∀i∈RowIndex.ids,Blank s.val i) (hswap : Blank s.val 216) :
    ∃cost t finalWord,Executes input tape (monomialInitializeCode second) cost s t ∧
      cost≤monomialInitializeCost D B oldWord.length ∧
      RationalDataflow.Ready (Finset.range 8)
        (loadedMonomialValues a D (cacheSourceStride second) (cacheSourceOffset second) v) t ∧
      a.Ready t ∧
      (loadedMonomialTable a b (cacheSourceStride second) (cacheSourceOffset second)).OutputReady t ∧
      (∀i∈RowIndex.ids,Blank t.val i) ∧ Blank t.val 216 ∧
      BankArray.Word t.val 201 finalWord ∧ finalWord.length=D.bits.length ∧
      RationalAccumulator.Word t.val 720 D ∧ RationalAccumulator.Word t.val 725 (4*(D+1)) ∧
      WidthBank (Finset.range 8) V
        (loadedMonomialValues a D (cacheSourceStride second) (cacheSourceOffset second) v) ∧
      Good (Finset.range 8)
        (loadedMonomialValues a D (cacheSourceStride second) (cacheSourceOffset second) v) ∧
      MonomialStored (loadedMonomialTable a b (cacheSourceStride second) (cacheSourceOffset second))
        (monomialState D coeff 0) ∧
      MonomialCoefficientsStored
        (loadedMonomialTable a b (cacheSourceStride second) (cacheSourceOffset second)) coeff := by
  obtain ⟨s0,e0,c0,f0⟩ := WordReplace.executes 725 201 (by decide) input tape
    (4*(D+1)).bits oldWord s hsize hcount
  have r0 := hs.wordReplace_frame (outside_workspace _ _ (by decide)) f0
  have a0 := ha.copy_frame (Or.inl rfl) f0
  have b0 := hb.copy_frame (Or.inl rfl) f0 a0.scratch a0.seven
  have z0 : ∀i∈RowIndex.ids,Blank s0.val i := by
    intro i hi
    exact RationalAccumulator.blank_of_eq (f0.2.2.2.2.2.1 i (by
      simp only [RowIndex.ids,Finset.mem_insert,Finset.mem_singleton] at hi;omega)) (hblank i hi)
  obtain ⟨origin,c0⟩ := c0
  obtain ⟨c1,s1,w1,e1,hc1,r1,a1,b1,z1,cw1,lw1⟩ := monomialSeed_executes a b hD B
    (hV.trans hVB) hbMeta hslot hsep hdisjoint (Finset.range 8) (by decide) v (hv.mono hVB)
    input tape (4*(D+1)).bits origin hsizebits s0 (addressValue_bits _) c0 r0 a0 b0 z0
  have seed_keep (i : ℕ) (hi : i∈([216,720,725]:List ℕ)) :=
    e1.protectsTape i (List.all_eq_true.mp seed_protects_cache_ports i hi)
  have degree1 : RationalAccumulator.Word s1.val 720 D := RationalAccumulator.word_of_eq
    ((seed_keep 720 (by decide)).trans (f0.2.2.2.2.2.1 720 (by decide))) hdegree
  obtain ⟨s2,e2,c2,f2⟩ := WordReplace.executes 720 201 (by decide) input tape
    D.bits w1 s1 degree1 ⟨origin,cw1⟩
  have r2 := r1.wordReplace_frame (outside_workspace _ _ (by decide)) f2
  have a2 := a1.copy_frame (Or.inl rfl) f2
  have b2 := b1.copy_frame (Or.inl rfl) f2 a2.scratch a2.seven
  have z2 : ∀i∈RowIndex.ids,Blank s2.val i := by
    intro i hi
    exact RationalAccumulator.blank_of_eq (f2.2.2.2.2.2.1 i (by
      simp only [RowIndex.ids,Finset.mem_insert,Finset.mem_singleton] at hi;omega)) (z1 i hi)
  have hm := monomialSeedTable_metadata b
  have bm := Profile.Runtime.tableMetadata_width hm hbMeta
  have bs := Profile.Runtime.tableMetadata_separated hm hsep
  have bd : a.SeparatedFrom (monomialSeedTable b) := by
    simpa only [Table.SeparatedFrom,hm.1,hm.2.1,hm.2.2.1,hm.2.2.2.1] using hdisjoint
  obtain ⟨origin2,c2⟩ := c2
  obtain ⟨c3,t,word,e3,hc3,r3,_,a3,b3,z3,cw3,lw3⟩ := laneCopyRows_executes a
    (monomialSeedTable b) D (cacheSourceStride second) (cacheSourceOffset second) 4 7 1
    (Finset.range 8) (by decide) B (by omega) haMeta bm (by simpa only [hm.1] using hslot) bs bd hsource (by intro r hr;omega)
    (Function.update v 0 (Parts.literal 1))
    ((hv.update 0 ((Parts.literal_width RationalWords.width_one).mono hV)).mono hVB)
    input tape D.bits origin2 hDbits s2 (addressValue_bits _) c2 r2 a2 b2 z2
  have copy_keep (i : ℕ) (hi : i∈([216,720,725]:List ℕ)) :=
    e3.protectsTape i (List.all_eq_true.mp (copyRows_protects_cache_ports second) i hi)
  have keep (i : ℕ) (hi : i∈([216,720,725]:List ℕ)) : t.val.tapes i=s.val.tapes i :=
    (copy_keep i hi).trans ((f2.2.2.2.2.2.1 i (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi;omega)).trans
      ((seed_keep i hi).trans (f0.2.2.2.2.2.1 i (by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi;omega))))
  have sourceWidth (r : ℕ) (hr : r<D) :
      (a.getD (cacheSourceStride second*r+cacheSourceOffset second)).Width V := by
    rw [hcoeff r hr];exact hw r hr
  have sourceValid (r : ℕ) (hr : r<D) :
      (a.getD (cacheSourceStride second*r+cacheSourceOffset second)).Valid := by
    rw [hcoeff r hr];exact hc r hr
  have bounds := loadedMonomialValues_bounds a D (cacheSourceStride second)
    (cacheSourceOffset second) V (Finset.range 8) v hV hv hg sourceWidth sourceValid
  have correct := loadedMonomialTable_correct a b (cacheSourceStride second) (cacheSourceOffset second)
    hD (hV.trans (hVB.trans hslot))
    (fun r => (sourceWidth r.val r.isLt).mono (hVB.trans hslot)) coeff hcoeff
  refine ⟨_,t,word,e0.seq (e1.seq (e2.seq e3)),?_,r3,a3,b3,z3,
    RationalAccumulator.blank_of_eq (keep 216 (by decide)) hswap,⟨origin2,cw3⟩,lw3,
    RationalAccumulator.word_of_eq (keep 720 (by decide)) hdegree,
    RationalAccumulator.word_of_eq (keep 725 (by decide)) hsize,
    bounds.1,bounds.2.1,correct.1,correct.2⟩
  have hstride : (cacheSourceStride second).bits.length≤3 := by cases second <;> decide
  have hoffset : (cacheSourceOffset second).bits.length≤3 := by cases second <;> decide
  have hp : (B+(cacheSourceStride second).bits.length+(cacheSourceOffset second).bits.length+
      (4:ℕ).bits.length+(7:ℕ).bits.length+6)^2≤(B+18)^2 :=
    Nat.pow_le_pow_left (by
      rw [show (4:ℕ).bits.length=3 from rfl,show (7:ℕ).bits.length=3 from rfl]
      omega) 2
  have hc3' : c3≤(D+1)*(13*D.bits.length+15)+D*(2^32*(B+18)^2) :=
    hc3.trans (Nat.add_le_add_left (Nat.mul_le_mul_left D (Nat.mul_le_mul_left _ hp)) _)
  unfold monomialInitializeCost
  omega

#print axioms monomialInitialize_executes
end Maxwell.Continuum.Calibration.RawCutoff
