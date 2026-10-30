import Maxwell.Continuum.ProfileProducerFrames

/-! A computed coefficient is written to its actual runtime-indexed row;
all three unreduced integer channels are materialized. -/
namespace Maxwell.Continuum.Profile.Runtime
open RationalDataflow Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

def roundedStoreCode : Code := .seq roundedCode (PartArray.writeAtCode 700 9)
def roundedStoreCost (grid D P U W M indexLength oldLength : ℕ) : ℕ :=
  roundedCost grid D P U W indexLength oldLength+2^20*(M+5)^2

theorem rounded_store_executes {n : ℕ} (a : PartArray.Table n) (grid D P U W M : ℕ) (j : Fin n)
    (hg0 : 0<grid) (hg : grid≤U) (hD : D≤U) (hP : P≤U) (hj : j.val≤U) (hW : 1≤W)
    (v : ℕ→Parts) (hw : WidthBank dftRegisters W v) (saved : Parts) (hsaved : saved.Width W)
    (jword oldWord : List Bool) (hjword : addressValue jword=j.val) (hlen : jword.length≤M)
    (hmeta : a.MetadataWidth M) (hfit : roundedRawWidth U≤addressValue a.width) (hsep : a.Separated)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hr : Ready dftRegisters v s) (hp : Phase.Runtime.Clean s.val) (hz : Glue.Clean s.val)
    (hfloor : DyadicFloor.Clean s.val) (hpower : Word s.val 144 (2^P))
    (hm : DFTParameters D P s) (hgrid : Word s.val 664 grid)
    (hindex : BankArray.Word s.val 700 jword) (hc : BankArray.Word s.val 201 oldWord)
    (hstore : StoredParts.Stored 701 saved s.val) (ha : a.OutputReady s) :
    ∃(cost : ℕ) (t : Store) (finalWord : List Bool) (outputSaved : Parts)
      (r : RoundedResult grid D P U j.val t),
      Executes input tape roundedStoreCode cost s t ∧
      (a.set j (r.values 9)).OutputReady t ∧
      BankArray.Word t.val 201 finalWord ∧ finalWord.length=grid.bits.length ∧
      BankArray.Word t.val 700 jword ∧ t.val.tapes 700=s.val.tapes 700 ∧ Word t.val 664 grid ∧
      StoredParts.Stored 701 outputSaved t.val ∧ outputSaved.Width (dftRawWidth U) ∧
      t.val.memory=a.writeMemory j (r.values 9) s.val.memory ∧
      cost≤roundedStoreCost grid D P U W M jword.length oldWord.length := by
  obtain ⟨c0,s0,word0,saved0,e0,result0,count0,len0,store0,ws0,f0,h0⟩ := rounded_executes grid D P U j.val W
    hg0 hg hD hP hj hW v hw saved hsaved jword oldWord hjword input tape s hr hp hz hfloor hpower
    hm hgrid hindex hc hstore
  obtain ⟨r0⟩ := result0
  have index0 : BankArray.Word s0.val 700 jword :=
    BankArray.word_of_eq (f0.tapes 700 (rounded_metadata_outside _ (by decide))) hindex
  have grid0 := word_of_eq (f0.tapes 664 (rounded_metadata_outside _ (by decide))) hgrid
  have out0 := outputReady_rounded_frame ha r0.ready f0
  have hpw : 0<addressValue a.width := by unfold roundedRawWidth at hfit;omega
  obtain ⟨c1,t,e1,h1,rt,outt,mem,f1⟩ := PartArray.writeAt_executes a dftRegisters 700 (by decide) 9
    (by decide) r0.values j hpw (r0.resultWidth.mono hfit) hsep input tape jword hjword s0 r0.ready out0 index0
  let r : RoundedResult grid D P U j.val t := r0.write_frame rt f1
  refine ⟨c0+c1,t,word0,saved0,r,e0.seq e1,outt,
    BankArray.word_of_eq (f1.2.2.2.1 201 (by decide) (by decide)) count0,len0,
    BankArray.word_of_eq (f1.2.2.2.1 700 (by decide) (by decide)) index0,
    (f1.2.2.2.1 700 (by decide) (by decide)).trans (f0.tapes 700 (rounded_metadata_outside _ (by decide))),
    word_of_eq (f1.2.2.2.1 664 (by decide) (by decide)) grid0,stored701_write store0 f1,ws0,?_,?_⟩
  · rw [mem,f0.memory]
    rfl
  · have cost1 : c1≤2^20*(M+5)^2 := h1.trans (a.writeCost_bound M hmeta jword hlen _)
    unfold roundedStoreCost
    omega

#print axioms rounded_store_executes
end Maxwell.Continuum.Profile.Runtime
