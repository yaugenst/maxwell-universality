import Maxwell.Continuum.RationalDataflowArrayNormalizeFrame

/-! One fixed program computes a rational table norm, takes the executed
literal square root, and writes every scaled entry to a disjoint table. -/
namespace Maxwell.Continuum.RationalDataflow.PartArray.Normalize
open Maxwell.Cost Maxwell.Cost.Structured Calibration
open scoped BigOperators
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384

def width (T P W : ℕ) : ℕ := RationalRoot.normalizeScalarWidth P (squaresWidth T W)
def code : Code := .seq (squaresCode 24 1)
  (.seq (RationalRoot.normalizeScalarCode 24)
    (.seq (WordReplace.code 787 201) (mapCode (scaleBody 24) 1)))
def retainedWords : List ℕ := [570,571,572,574,700,788,802]
def costBound (T P W length : ℕ) : ℕ := squaresCost T W length+
  (RationalRoot.normalizeScalarCost 24 P (squaresWidth T W)+
    ((6*length+15*T.bits.length+21)+
      ((T+1)*(13*T.bits.length+15)+T*mapStepCost (scaleBody 24) (2*width T P W+1))))

theorem executes {T : ℕ} (a b : Table T) (n : ℕ→ℕ) (v : ℕ→Parts) (W : ℕ) (hW : 1≤W)
    (naturalWidth : ∀i∈RationalRoot.Stored.ids 24,(n i).bits.length≤W)
    (rawWidth : WidthBank slots W v) (good : Good slots v)
    (entryWidth : ∀i,(a.get i).Width W) (entryValid : ∀i,(a.get i).Valid)
    (countWidth : T.bits.length≤W) (metadata : a.MetadataWidth W)
    (outputMetadata : b.MetadataWidth (2*width T (n 700) W+1))
    (capacity : 2*width T (n 700) W+1≤addressValue b.width)
    (separated : b.Separated) (disjoint : a.SeparatedFrom b)
    (positive : 0<sqrtRationalCenter (∑i,(a.get i).value^2) (n 700))
    (input : List Bool) (tape : ℕ→Bool) (xs : List Bool) (origin : ℤ)
    (length : xs.length≤W) (s : Store) (count : addressValue xs=T)
    (counter : s.val.tapes 201=BitTape.shifted xs origin)
    (savedCount : RationalAccumulator.Word s.val 787 T)
    (bank : NatAssign.Bank (RationalRoot.Stored.ids 24) n s.val)
    (raw : Ready slots v s) (array : a.Ready s) (output : b.OutputReady s) :
    ∃cost t,∃result : Table T,Executes input tape code cost s t ∧ cost≤costBound T (n 700) W xs.length ∧
      result.OutputReady t ∧ result.MetadataWidth (2*width T (n 700) W+1) ∧
      (∀i,(result.get i).Valid) ∧
      (∀i,(result.get i).Width (2*width T (n 700) W+1)) ∧
      (∀i,(result.get i).value=(sqrtRationalCenter (∑j,(a.get j).value^2) (n 700))⁻¹*(a.get i).value) ∧
      (result.width=b.width ∧ result.basePositive=b.basePositive ∧ result.baseNegative=b.baseNegative ∧
        result.baseDenominator=b.baseDenominator ∧ result.clock=b.clock) ∧
      (∀limit,limit≤addressValue b.basePositive→limit≤addressValue b.baseNegative→
        limit≤addressValue b.baseDenominator→∀j,j<limit→t.val.memory j=s.val.memory j) ∧
      (∀i∈retainedWords,t.val.tapes i=s.val.tapes i) := by
  have bound : W≤squaresWidth T W := by unfold squaresWidth sumWidth;nlinarith
  obtain ⟨c0,u,word,e0,h0,ru,au,counter0,len0,wu,gu,value0⟩ := squares_executes a slots 24 1
    (by simp [slots]) (by simp [slots]) (by decide) W hW metadata entryWidth entryValid v rawWidth good
    input tape xs origin length s count counter raw array
  change Ready slots (afterSquares a v) u at ru
  change WidthBank slots (squaresWidth T W) (afterSquares a v) at wu
  change Good slots (afterSquares a v) at gu
  change ((afterSquares a v) 24).value=∑i,(a.get i).value^2 at value0
  let n1:=squareNumbers n (afterSquares a v)
  have precision : n1 700=n 700 := rfl
  have nonnegative : 0≤((afterSquares a v) 24).value := by
    rw [value0]
    exact Finset.sum_nonneg (fun _ _=>sq_nonneg _)
  have normpositive : 0<sqrtRationalCenter ((afterSquares a v) 24).value (n1 700) := by
    rw [value0,precision]
    exact positive
  have bu:=squareNumbers_bank n (afterSquares a v) e0 bank ru
  have nu:=squareNumbers_width n (afterSquares a v) W (squaresWidth T W) bound naturalWidth wu
  obtain ⟨c1,z,x,e1,h1,rz,gz,wz,vx,zero,f1⟩ := RationalRoot.normalizeScalar_executes slots 24
    (by simp [slots]) n1 (afterSquares a v) (squaresWidth T W) nu wu gu nonnegative normpositive
    input tape u bu ru
  rw [precision] at h1 wz vx
  change WidthBank slots (width T (n 700) W) (Function.update (afterSquares a v) 24 x) at wz
  have bw : W≤width T (n 700) W := by
    unfold width RationalRoot.normalizeScalarWidth RationalRoot.outputWidth
    omega
  have wx : x.Width (width T (n 700) W) := by
    simpa only [Function.update_self] using wz 24 (by simp [slots])
  have gx : x.Valid := by simpa only [Function.update_self] using gz 24 (by simp [slots])
  have value : x.value=(sqrtRationalCenter (∑i,(a.get i).value^2) (n 700))⁻¹ := by
    rwa [value0] at vx
  obtain ⟨az,bz⟩ := root_arrays au (squares_output e0 output au) f1 rz.2
  have shared:=shared_of_root rz zero
  have saved : RationalAccumulator.Word z.val 787 T :=
    RationalAccumulator.word_of_eq (f1.tapes 787 (by decide))
      (RationalAccumulator.word_of_eq (squares_keeps e0 787 (by simp [retained])) savedCount)
  have oldCount : BankArray.Word z.val 201 word :=
    ⟨origin,(f1.tapes 201 (by decide)).trans counter0⟩
  obtain ⟨q,e2,counter2,f2⟩ := WordReplace.executes 787 201 (by decide)
    input tape T.bits word z saved oldCount
  have aq:=az.copy_frame (Or.inl rfl) f2
  have bq:=bz.copy_frame (Or.inl rfl) f2 aq.scratch aq.seven
  have sq:=sharedReady_copy_frame shared (Or.inl rfl) f2
  obtain ⟨newOrigin,newCounter⟩:=counter2
  obtain ⟨c3,t,_,e3,h3,_,_,bt,_,_,values,memory⟩ := scale_executes a b slots 24
    (by simp [slots]) (by simp [slots]) (by decide)
    (Function.update (afterSquares a v) 24 x) (width T (n 700) W) (by omega) wz gz
    (fun i=>(entryWidth i).mono bw) entryValid (metadata.mono (by omega)) outputMetadata capacity separated disjoint
    input tape T.bits newOrigin (countWidth.trans (by omega)) q (addressValue_bits T) newCounter sq aq bq
  simp only [Function.update_self] at bt values
  have fit (i : Fin T) : ((a.get i).mul x).Width (addressValue b.width) :=
    (((entryWidth i).mono bw).mul wx).mono (by omega)
  refine ⟨c0+(c1+((6*word.length+15*T.bits.length+21)+c3)),t,
    b.filled (fun i=>(a.get i).mul x) 0,e0.seq (e1.seq (e2.seq e3)),?_,bt,
    ⟨outputMetadata.width,outputMetadata.basePositive,outputMetadata.baseNegative,
      outputMetadata.baseDenominator,outputMetadata.clock⟩,?_,?_,?_,⟨rfl,rfl,rfl,rfl,rfl⟩,?_,?_⟩
  · rw [len0]
    exact Nat.add_le_add h0 (Nat.add_le_add h1 (Nat.add_le_add_left h3 _))
  · intro i
    rw [Table.filled_get b _ fit]
    exact Parts.mul_valid (entryValid i) gx
  · intro i
    rw [Table.filled_get b _ fit]
    simpa only [two_mul] using ((entryWidth i).mono bw).mul wx
  · intro i
    rw [values i,value,mul_comm]
  · intro limit hp hm hd i hi
    rw [memory limit hp hm hd i hi,f2.2.2.1,f1.memory,e0.protectsMemory squares_memory]
  · intro i hi
    have first : (squaresCode 24 1).protectsTape i=true := by
      simp only [retainedWords,List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    have last : (mapCode (scaleBody 24) 1).protectsTape i=true := by
      simp only [retainedWords,List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    have middle : i∉RationalRoot.normalizeScalarChanged 24 := by
      simp only [retainedWords,List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    have countKeep : i≠201 := by
      simp only [retainedWords,List.mem_cons,List.not_mem_nil,or_false] at hi
      omega
    exact (e3.protectsTape i last).trans ((f2.2.2.2.2.2.1 i countKeep).trans
      ((f1.tapes i middle).trans (e0.protectsTape i first)))

#print axioms executes
end Maxwell.Continuum.RationalDataflow.PartArray.Normalize
