import Maxwell.Continuum.SourceRoutingEdgeData

/-! Actual chronological edge emission from the three stored routing histories.
All terminal coordinates and reverse ports are computed by the fixed program. -/
namespace Maxwell.Cost.RoutingPorts.Complete.GeometryPath
open Structured GeometryPathPhase Maxwell.Logical.Routing
open RationalAccumulator (Word Blank)
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

theorem edge_executes {V E : Type*} {half : ℕ} (data : Gluing.Data V E half)
    (p : Plan (2*half))
    (sep₁ : p.history.following.slab (2*(2*half)+1) ≤ p.base)
    (sep₂ : p.history.following.following.slab (2*(2*half)+1) ≤ p.base)
    (edge : E) (cursor n : ℕ)
    (fits₀ : GeometrySort.Fits p.history.width (PhaseKeys.first data.colors))
    (fits₁ : GeometrySort.Fits p.history.width (PhaseKeys.middle data.colors))
    (fits₂ : GeometrySort.Fits p.history.width (PhaseKeys.last data.colors))
    (room : cursor+3072*(2*half) ≤ n) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank GeometryArithmetic.ids
      (GeometrySort.seed (p.history.layer 0) 1 (finProdFinEquiv (Gluing.token data (edge,false))).val) s.val)
    (ready : GeometryArray.Ready s.val) (privateBlank : Blank s.val 1249)
    (metadata : GeometrySort.Metadata (p.history.layer 0) s.val)
    (output : OutputMetadata p.width p.base p.clock s.val)
    (levelWord : Word s.val 1255 0) (cursorWord : Word s.val 1253 cursor) (counterBlank : Blank s.val 1242)
    (stored₀ : GeometryHistory.Stored p.history (PhaseKeys.first data.colors) (2*(2*half)) s.val.memory)
    (stored₁ : GeometryHistory.Stored p.history.following (PhaseKeys.middle data.colors) (2*(2*half)) s.val.memory)
    (stored₂ : GeometryHistory.Stored p.history.following.following (PhaseKeys.last data.colors) (2*(2*half)) s.val.memory) :
    ∃steps t,Executes input tape edgeCode steps s t ∧ steps ≤ edgeCost p sep₁ sep₂ n ∧
      NatAssign.Bank GeometryArithmetic.ids
        (GeometrySort.seed (p.history.layer 0) 1 (finProdFinEquiv (Gluing.token data (edge,true))).val) t.val ∧
      GeometryArray.Ready t.val ∧ Blank t.val 1249 ∧ GeometrySort.Metadata (p.history.layer 0) t.val ∧
      OutputMetadata p.width p.base p.clock t.val ∧ Word t.val 1255 0 ∧
      Word t.val 1253 (cursor+3*(EdgeEmission.edge data (EdgeEmission.prepare data) edge).length) ∧
      t.val.memory=MemoryWord.writeBits s.val.memory (p.base+cursor*p.width)
        (pointsBits p.width (EdgeEmission.edge data (EdgeEmission.prepare data) edge)) ∧
      Blank t.val 1242 ∧ ArchiveFrame phaseWork s.val t.val ∧
      Tree.Memory.Frame p.base (n*p.width) s.val.memory t.val.memory := by
  let leftBottom := EdgeEmission.bottomPrefix data (edge,false)
  let leftNetwork := EdgeEmission.networkPrefix (EdgeEmission.prepare data) (Gluing.token data (edge,false))
  let top := EdgeEmission.topPrefix data edge
  let endpoint := Schedule.gridPort (Gluing.pairPort (data.pair edge) true) (96*(2*half))
  let rightNetwork := EdgeEmission.networkPrefix (EdgeEmission.prepare data) (Gluing.token data (edge,true))
  let rightBottom := EdgeEmission.bottomPrefix data (edge,true)
  let pointsA := leftBottom
  let pointsB := pointsA++leftNetwork
  let pointsC := pointsB++top
  let pointsD := pointsC++[endpoint]
  let pointsE := pointsD++rightNetwork.reverse
  let pointsF := pointsE++rightBottom.reverse
  let cursorA := cursor+3*pointsA.length
  let cursorB := cursor+3*pointsB.length
  let cursorC := cursor+3*pointsC.length
  let cursorD := cursor+3*pointsD.length
  let cursorE := cursor+3*pointsE.length
  have qp := p.history.positive
  have bL := bottom_words_bound data (edge,false)
  have nL := network_words_bound data (edge,false)
  have nR := network_words_bound data (edge,true)
  have bR := bottom_words_bound data (edge,true)
  have topLength := top_prefix_length data edge
  have histories {memory : ℕ→Bool} (frame : Tree.Memory.Frame p.base (n*p.width) s.val.memory memory) :
      GeometryHistory.Stored p.history (PhaseKeys.first data.colors) (2*(2*half)) memory ∧
      GeometryHistory.Stored p.history.following (PhaseKeys.middle data.colors) (2*(2*half)) memory ∧
      GeometryHistory.Stored p.history.following.following (PhaseKeys.last data.colors) (2*(2*half)) memory :=
    ⟨p.history_frame _ n stored₀ frame,(p.following sep₁).history_frame _ n stored₁ frame,
      ((p.following sep₁).following sep₂).history_frame _ n stored₂ frame⟩
  obtain ⟨cA,a,eA,hA,ba,za,pa,ma,oa,ca,memA,fA,mA⟩ := terminal_executes (p.history.layer 0) 1
    (Gluing.token data (edge,false)) true (bottomChoice false) (bottomChoice_valid false) (by rw [bottomChoice_depth]) false
    cursor p.width p.base n p.clock p.positive p.clock_length p.coordinate_width (by omega)
    input tape s bank ready privateBlank metadata output cursorWord
  have cursorAtA : Word a.val 1253 cursorA := by
    rw [bottom_shape_length data (p.history.layer 0) 1 (edge,false) cursor] at ca
    exact ca
  have writtenA : a.val.memory=MemoryWord.writeBits s.val.memory (p.base+cursor*p.width) (pointsBits p.width pointsA) := by
    rw [bottom_bits data (p.history.layer 0) 1 (edge,false) cursor p.width false] at memA
    simpa only [Bool.false_eq_true,ite_false] using memA
  have savedA := histories mA
  obtain ⟨cB,b,eB,hB,bb,zb,pb,mb,ob,lb,cb,memB,blankB,fB,mB⟩ := network_forward data p sep₁ sep₂ (edge,false)
    cursorA n fits₀ fits₁ fits₂
    (by dsimp only [cursorA,pointsA,leftBottom];omega) input tape a ba za pa ma oa
    (RationalAccumulator.word_of_eq (fA.tapes 1255 (by decide) (by decide)) levelWord) cursorAtA
    (RationalAccumulator.blank_of_eq (fA.tapes 1242 (by decide) (by decide)) counterBlank)
    savedA.1 savedA.2.1 savedA.2.2
  have cursorAtB : Word b.val 1253 cursorB := by
    simpa only [cursorB,cursorA,pointsB,leftNetwork,List.length_append,Nat.mul_add,Nat.add_assoc] using cb
  have writtenB : b.val.memory=MemoryWord.writeBits s.val.memory (p.base+cursor*p.width) (pointsBits p.width pointsB) := by
    rw [memB,writtenA]
    exact write_points_append _ _ _ _ _ _
  obtain ⟨cC,c,eC,hC,bc,zc,pc,mc,oc,cc,memC,fC,mC⟩ := terminal_executes
    (p.history.following.following.layer (2*(2*half))) (2*(2*half)+1) (Gluing.pairPort (data.pair edge) false)
    false (.shape .top) (by trivial) (by decide) false cursorB p.width p.base n p.clock
    p.positive p.clock_length p.coordinate_width
    (by dsimp only [cursorB,pointsB,pointsA,leftBottom,leftNetwork];simp only [List.length_append];omega)
    input tape b bb zb pb mb ob cursorAtB
  have cursorAtC : Word c.val 1253 cursorC := by
    simpa only [ShapeChoice.evaluate,Shape.length,cursorC,cursorB,pointsC,List.length_append,
      top,topLength,Nat.mul_add,Nat.add_assoc] using cc
  have writtenC : c.val.memory=MemoryWord.writeBits s.val.memory (p.base+cursor*p.width) (pointsBits p.width pointsC) := by
    rw [ShapeChoice.evaluate,top_bits] at memC
    rw [memC,writtenB]
    exact write_points_append _ _ _ _ _ _
  obtain ⟨cP,d,eP,hP,bd,zd,pd,fP⟩ := pairSwitch_executes
    (p.history.following.following.layer (2*(2*half))) (2*(2*half)+1) (data.pair edge) input tape c bc zc pc
  have md := mc.frame (ArchiveFrame.of_binary fP) (by decide)
  have od : OutputMetadata p.width p.base p.clock d.val :=
    oc.frame ((ArchiveFrame.of_binary fP).mono Finset.subset_union_right)
  have cursorAtPair := RationalAccumulator.word_of_eq (fP.tapes 1253 (by decide)) cursorAtC
  obtain ⟨cD,e,eD,hD,be,ze,pe,me,oe,ce,memD,fD,mD⟩ := terminal_executes
    (p.history.following.following.layer (2*(2*half))) (2*(2*half)+1) (Gluing.pairPort (data.pair edge) true)
    false (.shape .endpoint) (by trivial) (by decide) false cursorC p.width p.base n p.clock
    p.positive p.clock_length p.coordinate_width
    (by dsimp only [cursorC,pointsC,pointsB,pointsA,leftBottom,leftNetwork,top];simp only [List.length_append,topLength];omega)
    input tape d bd zd pd md od cursorAtPair
  have cursorAtD : Word e.val 1253 cursorD := by
    simpa only [ShapeChoice.evaluate,Shape.length,cursorD,cursorC,pointsD,List.length_append,
      List.length_singleton,Nat.mul_add,Nat.add_assoc] using ce
  have writtenD : e.val.memory=MemoryWord.writeBits s.val.memory (p.base+cursor*p.width) (pointsBits p.width pointsD) := by
    rw [ShapeChoice.evaluate,endpoint_bits] at memD
    rw [memD,fP.memory,writtenC]
    exact write_points_append _ _ _ _ _ _
  have fullFrameD : Tree.Memory.Frame p.base (n*p.width) s.val.memory e.val.memory := by
    rw [fP.memory] at mD
    exact mA.trans (mB.trans (mC.trans mD))
  have frameD : ArchiveFrame terminalWork b.val e.val :=
    fC.trans (((ArchiveFrame.of_binary fP).mono (by decide)).trans fD)
  have savedD := histories fullFrameD
  obtain ⟨cE,f,eE,hE,bf,zf,pf,mf,of_,lf,cf,memE,blankF,fE,mE⟩ := network_reverse data p sep₁ sep₂ (edge,true)
    cursorD n fits₀ fits₁ fits₂
    (by dsimp only [cursorD,pointsD,pointsC,pointsB,pointsA,leftBottom,leftNetwork,top];
        simp only [List.length_append,List.length_singleton,topLength];omega)
    input tape e be ze pe me oe
    (RationalAccumulator.word_of_eq (frameD.tapes 1255 (by decide) (by decide)) lb) cursorAtD
    (RationalAccumulator.blank_of_eq (frameD.tapes 1242 (by decide) (by decide)) blankB)
    savedD.1 savedD.2.1 savedD.2.2
  have cursorAtE : Word f.val 1253 cursorE := by
    simpa only [cursorE,cursorD,pointsE,List.length_append,List.length_reverse,Nat.mul_add,Nat.add_assoc] using cf
  have writtenE : f.val.memory=MemoryWord.writeBits s.val.memory (p.base+cursor*p.width) (pointsBits p.width pointsE) := by
    rw [memE,writtenD]
    exact write_points_append _ _ _ _ _ _
  obtain ⟨cF,t,eF,hF,bt,zt,pt,mt,ot,ct,memF,fF,mF⟩ := terminal_executes (p.history.layer 0) 1
    (Gluing.token data (edge,true)) true (bottomChoice true) (bottomChoice_valid true) (by rw [bottomChoice_depth]) true
    cursorE p.width p.base n p.clock p.positive p.clock_length p.coordinate_width
    (by dsimp only [cursorE,pointsE,pointsD,pointsC,pointsB,pointsA,leftBottom,leftNetwork,top,rightNetwork];
        simp only [List.length_append,List.length_singleton,List.length_reverse,topLength];omega)
    input tape f bf zf pf mf of_ cursorAtE
  have actualPoints : pointsF=EdgeEmission.edge data (EdgeEmission.prepare data) edge := by
    simp only [pointsF,pointsE,pointsD,pointsC,pointsB,pointsA,leftBottom,leftNetwork,top,endpoint,
      rightNetwork,rightBottom,edge_parts,List.append_assoc]
  have cursorAtF : Word t.val 1253 (cursor+3*pointsF.length) := by
    rw [bottom_shape_length data (p.history.layer 0) 1 (edge,true) cursorE] at ct
    simpa only [pointsF,rightBottom,List.length_append,List.length_reverse,cursorE,Nat.mul_add,Nat.add_assoc] using ct
  have writtenF : t.val.memory=MemoryWord.writeBits s.val.memory (p.base+cursor*p.width) (pointsBits p.width pointsF) := by
    rw [bottom_bits,ite_eq_left rfl] at memF
    rw [memF,writtenE]
    exact write_points_append _ _ _ _ _ _
  refine ⟨cA+(cB+(cC+(cP+(cD+(cE+cF))))),t,eA.seq (eB.seq (eC.seq (eP.seq (eD.seq (eE.seq eF))))),
    ?_,bt,zt,pt,mt,ot,RationalAccumulator.word_of_eq (fF.tapes 1255 (by decide) (by decide)) lf,
    by rwa [actualPoints] at cursorAtF,by rwa [actualPoints] at writtenF,
    RationalAccumulator.blank_of_eq (fF.tapes 1242 (by decide) (by decide)) blankF,
    (fA.mono (by decide)).trans (fB.trans ((frameD.mono (by decide)).trans (fE.trans (fF.mono (by decide))))),
    fullFrameD.trans (mE.trans mF)⟩
  dsimp only [edgeCost,terminalCost]
  omega

#print axioms edge_executes
end Maxwell.Cost.RoutingPorts.Complete.GeometryPath
