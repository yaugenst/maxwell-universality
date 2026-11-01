import Maxwell.Continuum.CalibrationSeedRootProducerData

/-! One fixed real or imaginary polarization producer, including actual
destination arithmetic, cache computation, storage, and scratch restoration. -/
namespace Maxwell.Continuum.Calibration.SeedRoot
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

theorem producer_executes (M D : ℕ) (a : PartArray.Table (2*(2*D+1)^3))
    (b : PartArray.Table (2*aliasArraySize (3*M+D)))
    (row : Fin (ArrayDecodeMachine.aliasRowCount (3*M+D))) (j : Fin 3) (part : Fin 2)
    (n : ℕ→ℕ) (v : ℕ→Parts) (B : ℕ) (hB : 2≤B)
    (hM : n 750=M) (hD : n 751=D) (half : n 752=n 750/2)
    (hrow : n 780=row.val) (dimension : n 785=aliasArraySize (3*M+D))
    (naturalWidth : ∀i∈rowIds,(n i).bits.length≤B)
    (width : WidthBank slots B (resetParts v)) (good : Good slots (resetParts v))
    (metadata : a.MetadataWidth B) (entryWidth : ∀i,(a.get i).Width B)
    (entryValid : ∀i,(a.get i).Valid) (outputMeta : b.MetadataWidth (producerWidth B))
    (positive : 0<addressValue b.width) (fits : producerWidth B≤addressValue b.width)
    (separated : b.Separated) (disjoint : a.SeparatedFrom b)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (natural : NatAssign.Bank rowIds n s.val) (ready : Ready slots (resetParts v) s)
    (cache : a.Ready s) (output : b.OutputReady s) :
    ∃cost t,Executes input tape (producerCode j part) cost s t ∧ cost≤producerCost B ∧
      NatAssign.Bank rowIds (resetNumbers n) t.val ∧
      (∀i∈rowIds,(resetNumbers n i).bits.length≤B) ∧ Ready slots (resetParts v) t ∧ a.Ready t ∧
      (b.set (outputCoordinate M D row j part) (entryParts M D a (coordinates n) j part v)).OutputReady t ∧
      t.val.memory=b.writeMemory (outputCoordinate M D row j part)
        (entryParts M D a (coordinates n) j part v) s.val.memory ∧
      t.val.inputHead=s.val.inputHead ∧ t.val.randomCursor=s.val.randomCursor ∧
      t.val.output=s.val.output ∧ t.val.tapes 4=s.val.tapes 4 ∧
      (∀i,10 ≤ i→i∉producerChanged→t.val.tapes i=s.val.tapes i) ∧
      (entryParts M D a (coordinates n) j part v).Valid ∧
      (entryParts M D a (coordinates n) j part v).Width (producerWidth B) := by
  obtain ⟨c0,u,e0,h0,nu,nwu,ru,au,bu,f0⟩ := destination_executes a b j part n (resetParts v)
    B hB naturalWidth input tape s natural ready cache output
  let nd := destinationValues j part n
  let ix := outputCoordinate M D row j part
  have md : nd 750=M := (fixed_destination_keep j part n 750 (by decide)).trans hM
  have dd : nd 751=D := (fixed_destination_keep j part n 751 (by decide)).trans hD
  have hd : nd 752=nd 750/2 := by
    dsimp only [nd]
    rw [fixed_destination_keep j part n 752 (by decide),fixed_destination_keep j part n 750 (by decide)]
    exact half
  have indexEq : nd 789=ix.val := by
    dsimp only [nd,ix]
    rw [destinationValues_index,dimension,hrow,outputCoordinate_value]
  have hs : ids⊆rowIds := by decide
  obtain ⟨c1,z,w,e1,h1,rz,gz,wz,nz,nwz,keep,az,bz,mem,inp,rnd,out,tapes,four⟩ :=
    emission_executes M D _ a b ix j part nd (resetParts v) (destinationWidth B) md dd hd indexEq
      (fun i hi=>nwu i (hs hi)) (width.mono (destinationWidth_ge B)) good
      (metadata.mono (destinationWidth_ge B)) (fun i=>(entryWidth i).mono (destinationWidth_ge B))
      entryValid outputMeta positive fits separated disjoint input tape u (fun i hi=>nu i (hs hi)) ru au bu
  let q := termsValues M D a (coordinates n) j part parities (resetParts v)
  have rz' : Ready slots q z := by simpa only [nd,destination_coordinates] using rz
  have gz' : Good slots q := by simpa only [nd,destination_coordinates] using gz
  have wz' : WidthBank slots (producerWidth B) q := by
    simpa only [producerWidth,q,nd,destination_coordinates] using wz
  have bz' : (b.set ix (q 27)).OutputReady z := by simpa only [nd,destination_coordinates] using bz
  have mem' : z.val.memory=b.writeMemory ix (q 27) s.val.memory := by
    simpa only [nd,destination_coordinates,f0.memory] using mem
  let nf := NatAssign.overlay ids w nd
  have nfBank : NatAssign.Bank rowIds nf z.val := by
    intro i hi
    by_cases own : i∈ids
    · simpa only [nf,NatAssign.overlay,ite_eq_left own] using nz i own
    · have separate : Disjoint (rowIds\ids) (changed∪{37}) := by decide
      have ho : i∉changed∪{37} := fun hh=>Finset.disjoint_left.mp separate (Finset.mem_sdiff.mpr ⟨hi,own⟩) hh
      have hc : i∉changed := fun hh=>ho (Finset.mem_union_left _ hh)
      have hp : i≠37 := fun hh=>ho (Finset.mem_union_right _ (Finset.mem_singleton.mpr hh))
      simpa only [nf,NatAssign.overlay,ite_eq_right own] using
        RationalAccumulator.word_of_eq (tapes i (rowIds_lower i hi) hc hp) (nu i hi)
  have nfWidth : ∀i∈rowIds,(nf i).bits.length≤producerWidth B := by
    intro i hi
    by_cases own : i∈ids
    · simpa only [producerWidth,nf,NatAssign.overlay,ite_eq_left own] using nwz i own
    · simpa only [nf,NatAssign.overlay,ite_eq_right own] using
        (nwu i hi).trans (producerWidth_ge_destination B)
  have fixedKeep (i : ℕ) (hi : i∈fixedFields) : nf i=n i := by
    have hiid : i∈ids := (by decide : fixedFields⊆ids) hi
    have hir : i∈retained := (by decide : fixedFields⊆retained) hi
    simp only [nf,NatAssign.overlay,ite_eq_left hiid]
    exact (keep i hir).trans (fixed_destination_keep j part n i hi)
  have fixedWidth (i : ℕ) (hi : i∈fixedFields) : (nf i).bits.length≤B := by
    rw [fixedKeep i hi]
    exact naturalWidth i ((by decide : fixedFields⊆rowIds) hi)
  have retainedRaw (i : ℕ) (hi : i∈slots) (hx : i∉([24,25,26,27]:List ℕ)) : (q i).Width B := by
    rw [show q i=resetParts v i from terms_keep M D a (coordinates n) j part parities (resetParts v) i hx]
    exact width i hi
  obtain ⟨c2,t,e2,h2,nt,nwt,rt,_,_,f2,four2⟩ := reset_executes nf q (producerWidth B) B
    (by omega) (producerWidth_ge B) nfWidth wz' gz' fixedWidth retainedRaw input tape z nfBank rz'
  have resetEq : resetParts q=resetParts v := resetParts_terms M D a (coordinates n) j part v
  rw [resetEq] at rt
  have finalBank : NatAssign.Bank rowIds (resetNumbers n) t.val := by
    intro i hi
    have eq : resetNumbers nf i=resetNumbers n i := by
      by_cases hf : i∈fixedFields
      · rw [resetNumbers_keep nf i hf,resetNumbers_keep n i hf,fixedKeep i hf]
      · simp [resetNumbers_value,hi,hf]
    exact eq ▸ nt i hi
  have finalWidth := resetNumbers_width n B (fun i hi=>naturalWidth i ((by decide : fixedFields⊆rowIds) hi))
  have arrays := arrays_after_reset az bz' f2 rt.2
  refine ⟨c0+(c1+c2),t,e0.seq (e1.seq e2),?_,finalBank,finalWidth,rt,arrays.1,arrays.2,
    f2.memory.trans mem',f2.inputHead.trans (inp.trans f0.inputHead),
    f2.randomCursor.trans (rnd.trans f0.randomCursor),f2.output.trans (out.trans f0.output),
    four2.trans (four.trans (f0.tapes 4 (by decide))),?_,gz' 27 (by decide),wz' 27 (by decide)⟩
  · unfold producerCost
    omega
  · intro i hi ho
    have hr : i∉rowWorkspace∪RationalDataflow.workspace slots :=
      fun hh=>ho (Finset.mem_union_left _ hh)
    have hc : i∉changed := fun hh=>ho ((by decide : changed⊆producerChanged) hh)
    have hp : i≠37 := fun hh=>ho (Finset.mem_union_right _ (Finset.mem_singleton.mpr hh))
    have hw : i∉workspace := fun hh=>ho ((by decide : workspace⊆producerChanged) hh)
    exact (f2.tapes i hr).trans ((tapes i hi hc hp).trans (f0.tapes i hw))

#print axioms producer_executes
end Maxwell.Continuum.Calibration.SeedRoot
