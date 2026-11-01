import Maxwell.Continuum.SourceRoutingEdgeSelectData

/-! Select an active incidence by reading the already computed inverse
permutation at its left paired port. No graph endpoint scan is repeated. -/
namespace Maxwell.Cost.RoutingPorts.Complete.GeometryPath
open Structured GeometryArithmetic Maxwell.Logical.Routing
open RationalAccumulator (Word Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 2600000

def edgeSelectBound {q : ℕ} (p : GeometrySort.Plan q) (round backward : ℕ) : ℕ :=
  p.bound round+backward.bits.length+16

theorem edgeSelect_executes {V E : Type*} {half : ℕ} (data : Gluing.Data V E half)
    (p : GeometrySort.Plan (2*half)) (round old backward : ℕ)
    (oldBound : old ≤ (2*half)*(2*half)) (edge : E) (edgeIndex : Fin (half*(2*half)))
    (pair : data.pair edge=finProdFinEquiv.symm edgeIndex)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank ids (GeometrySort.seed p round old) s.val)
    (ready : GeometryArray.Ready s.val) (privateBlank : Blank s.val 1249)
    (metadata : GeometrySort.Metadata p s.val) (edgeWord : Word s.val 1257 edgeIndex.val)
    (baseWord : Word s.val 1260 backward)
    (stored : BitArray.Represents s.val.memory backward p.width
      (IncidenceEncoding.words p.width (GeometryPhase.targets data.target.symm))) :
    ∃steps t,Executes input tape edgeSelectCode steps s t ∧
      steps ≤ 2^126*(edgeSelectBound p round backward+3)^2 ∧
      NatAssign.Bank ids (GeometrySort.seed p round (finProdFinEquiv (Gluing.token data (edge,false))).val) t.val ∧
      GeometryArray.Ready t.val ∧ Blank t.val 1249 ∧ GeometrySort.Metadata p t.val ∧
      t.val.memory=s.val.memory ∧ ArchiveFrame work s.val t.val := by
  let B:=edgeSelectBound p round backward
  let v:=GeometrySort.seed p round old
  let loaded:=Function.update v 1230 edgeIndex.val
  let out:=edgeSelectValues p round old edgeIndex.val
  let index:=finProdFinEquiv (Gluing.pairPort (data.pair edge) false)
  let source:=finProdFinEquiv (Gluing.token data (edge,false))
  have pb : p.bound round ≤ B:=by dsimp [B,edgeSelectBound];omega
  have wide : B ≤ 2^4*(B+1):=by omega
  have ew : edgeIndex.val.bits.length ≤ B :=
    ((Maxwell.Continuum.RationalWords.bits_mono (show edgeIndex.val ≤ (2*half)*(2*half) by
      have h:=edgeIndex.isLt;nlinarith)).trans (p.width_bound round)).trans pb
  have width : ∀j∈ids,(loaded j).bits.length ≤ B := by
    intro j hj
    by_cases same : j=1230
    · subst j;exact ew
    · simpa only [loaded,Function.update_of_ne same] using
        (GeometrySort.seed_width p round old oldBound j hj).trans pb
  have zero : ∀j∈Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,loaded j=0 := by
    intro j hj
    simp only [Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,
      Finset.mem_insert,Finset.mem_singleton] at hj
    rcases hj with rfl|rfl|rfl|rfl <;> rfl
  have literals : edgeSelectProgram.Literals B:=by
    simp [edgeSelectProgram,Control.Literals,Control.prepend,NatAssign.Instruction.literalWidth]
  have admissible : edgeSelectProgram.Admissible loaded:=by
    simp [edgeSelectProgram,Control.Admissible,Control.prepend,loaded,v,GeometrySort.seed,p.positive]
  have outWidth : ∀j∈ids,(out j).bits.length ≤ 2^4*(B+1) := by
    intro j hj
    have h:=edgeSelectProgram.evaluate_width edgeSelect_valid loaded B width literals j hj
    exact (Nat.le_add_right _ _).trans h
  obtain ⟨c₀,a,e₀,h₀,ba,za,pa,f₀⟩:=load_executes 1257 1230 (by decide) (by decide)
    v edgeIndex.val input tape s bank ready privateBlank edgeWord
  obtain ⟨c₁,b,e₁,h₁,bb,zb,pbBlank,f₁⟩:=edgeSelectProgram.executes edgeSelect_valid loaded zero
    admissible B width literals input tape a ba za pa
  have before : BinaryPrecision.Frame work s.val b.val:=(f₀.mono (by decide)).trans f₁
  have bm:=metadata.frame (ArchiveFrame.of_binary before) (by decide)
  have indexValue : out 1232=index.val:=by
    dsimp only [out,index]
    rw [edgeSelect_index,pair]
  have sourceValue : (GeometryPhase.targets data.target.symm).get index=source.val:=
    inverse_incidence data edge false
  have iw : index.val.bits.length ≤ 2^4*(B+1):=
    ((p.index_fit index).trans ((p.width_bound round).trans pb)).trans wide
  have sourceFit : ((GeometryPhase.targets data.target.symm).get index).bits.length ≤ p.width:=by
    rw [sourceValue]
    exact p.index_fit source
  have blankTarget : out 1231=0:=by
    dsimp only [out]
    rw [edgeSelect_other _ _ _ _ _ (by decide) (by decide) (by decide)]
    rfl
  have indexWord : Word b.val 1232 index.val := by
    have hb : Word b.val 1232 (out 1232) := bb 1232 (by decide)
    simpa only [indexValue] using hb
  obtain ⟨c₂,c,e₂,h₂,bc,zc,pc,mc,f₂⟩:=GeometryArithmetic.read 711 1232 1260 718 1231
    (by decide) (by decide) (by decide) (by decide) (by decide)
    p.width backward (2^4*(B+1)) p.clock (GeometryPhase.targets data.target.symm) index
    p.width_positive p.clock_length sourceFit (((p.width_bound round).trans pb).trans wide)
    iw (by dsimp [B,edgeSelectBound];omega) input tape out b bb zb pbBlank blankTarget
    bm.width indexWord
    (RationalAccumulator.word_of_eq (before.tapes 1260 (by decide)) baseWord) bm.clock
    (by rw [before.memory];exact stored)
  have updatedWidth : ∀j∈ids,((Function.update out 1231 ((GeometryPhase.targets data.target.symm).get index)) j).bits.length
      ≤ 2^4*(B+1) := by
    intro j hj
    by_cases same : j=1231
    · subst j
      exact sourceFit.trans (((p.width_bound round).trans pb).trans wide)
    · simpa only [Function.update_of_ne same] using outWidth j hj
  obtain ⟨c₃,t,e₃,h₃,bt,zt,f₃⟩:=stage edgeSelectCleanup
    (by simp [edgeSelectCleanup,NatAssign.Instruction.Valid,ids,controls]) _ (2^4*(B+1)) updatedWidth
    (by simp [edgeSelectCleanup,NatAssign.Instruction.literalWidth]) input tape c bc zc
  have ft : ArchiveFrame work s.val t.val:=
    (ArchiveFrame.of_binary before).trans ((f₂.mono (by decide)).trans ((ArchiveFrame.of_binary f₃).mono (by
      intro j hj
      simp only [work,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hj ⊢
      tauto)))
  refine ⟨c₀+(c₁+(c₂+c₃)),t,e₀.seq (e₁.seq (e₂.seq e₃)),?_,?_,zt,
    RationalAccumulator.blank_of_eq (f₃.tapes 1249 (by decide)) pc,
    metadata.frame ft (by decide),by rw [f₃.memory,mc,before.memory],ft⟩
  · have main:=h₁.trans (controlCost_steps _ 4 _ (by decide))
    change c₁ ≤ 2^122*(B+2)^2 at main
    change c₃ ≤ 3000*8^5*(2^4*(B+1)+2)^2 at h₃
    norm_num [v,GeometrySort.seed] at h₀
    change _ ≤ 2^126*(B+3)^2
    nlinarith only [h₀,main,h₂,h₃,ew]
  · simpa only [sourceValue,out,edgeSelect_cleaned] using bt

#print axioms edgeSelect_executes
end Maxwell.Cost.RoutingPorts.Complete.GeometryPath
