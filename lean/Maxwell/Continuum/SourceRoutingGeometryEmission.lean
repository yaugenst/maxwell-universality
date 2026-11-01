import Maxwell.Continuum.SourceRoutingEmissionPacked

/-! Fixed complete packed-geometry producer. Loop counts are copied or
computed from the actual source metadata, and every path is traversed once. -/
namespace Maxwell.Cost.RoutingPorts.Complete.GeometryEmission
open Structured GeometryArithmetic GeometryPath Maxwell.Logical.Routing
open Maxwell.Composition Maxwell.Composition.SourceDecorationEnumeration
open RationalAccumulator (Word Blank)
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000

def code : Code := .seq (WordReplace.code 154 1258)
  (.seq (originalLoopCode false) (.seq (WordDifference.code 141 154 1258)
    (.seq (originalLoopCode true) (.seq (WordLiteral.code 1257 0)
      (.seq (WordReplace.code 153 1258) edgeLoopCode)))))

def price {q : ℕ} (p : Plan q) (n v e left : ℕ) : ℕ :=
  (15*left.bits.length+21)+originalLoopCost p n left+
    300*(v.bits.length+left.bits.length+4)+originalLoopCost p n (v-left)+
    (6*v.bits.length+11)+(15*e.bits.length+21)+edgeLoopCost p n e

theorem executes {v e half : ℕ} (data : Gluing.Data (Fin v) (Fin e) half)
    (p : Plan (2*half)) (vertexRoom : v≤half*half) (edgeRoom : e≤half*(2*half))
    (tile : ∀i,data.tile i=finProdFinEquiv.symm (Fin.castLE vertexRoom i))
    (pair : ∀i,data.pair i=finProdFinEquiv.symm (Fin.castLE edgeRoom i))
    (left : ℕ) (leftBound : left≤v)
    (leftPart : ∀i : Fin v, i.val < left → data.part i=false)
    (rightPart : ∀i : Fin v, left ≤ i.val → data.part i=true)
    (saved : SourceEmission.Geometry v e)
    (originals : ∀i,saved.original.get i=Gluing.vertexPoint data i)
    (paths : ∀i,saved.paths.get i=EdgeEmission.edge data (EdgeEmission.prepare data) i)
    (n : ℕ) (fits₀ : GeometrySort.Fits p.path.history.width (PhaseKeys.first data.colors))
    (fits₁ : GeometrySort.Fits p.path.history.width (PhaseKeys.middle data.colors))
    (fits₂ : GeometrySort.Fits p.path.history.width (PhaseKeys.last data.colors))
    (room : packedLength saved+1+3072*(2*half)≤n)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (state : State data p 0 0 s) (counterBlank : Blank s.val 1258)
    (totalWord : Word s.val 141 v) (leftWord : Word s.val 154 left) (edgeWord : Word s.val 153 e) :
    ∃steps t,Executes input tape code steps s t ∧ steps≤price p n v e left ∧
      State data p (packedLength saved) e t ∧ Blank t.val 1258 ∧
      t.val.memory=MemoryWord.writeBits s.val.memory p.path.base
        ((packed saved).flatMap (IncidenceEncoding.word p.path.width)) ∧
      ArchiveFrame work s.val t.val ∧
      Tree.Memory.Frame p.path.base (n*p.path.width) s.val.memory t.val.memory := by
  have positive:=p.path.history.positive
  have originalRoom:=originals_span saved
  obtain ⟨a,e₀,sa,ca,f₀⟩:=state.copy_count 154 left (by decide) input tape leftWord counterBlank
  obtain ⟨c₁,b,e₁,h₁,sb,cb,mb,f₁,m₁⟩:=original_loop data p vertexRoom tile false 0 left
    (by omega) (fun i _ hi=>leftPart i (by omega)) 0 n (by omega) input tape a sa ca
  have fb : ArchiveFrame work s.val b.val:=((ArchiveFrame.of_binary f₀).mono (by decide)).trans f₁
  have sb' : State data p (3*left) left b:=by simpa only [Nat.zero_add] using sb
  obtain ⟨c₂,c,e₂,h₂,sc,cc,f₂⟩:=sb'.difference_count v left leftBound input tape
    (RationalAccumulator.word_of_eq (fb.tapes 141 (by decide) (by decide)) totalWord)
    (RationalAccumulator.word_of_eq (fb.tapes 154 (by decide) (by decide)) leftWord) cb
  obtain ⟨c₃,d,e₃,h₃,sd,cd,md,f₃,m₃⟩:=original_loop data p vertexRoom tile true left (v-left)
    (by omega) (fun i hi _=>rightPart i hi) (3*left) n (by omega) input tape c sc cc
  have fd : ArchiveFrame work s.val d.val:=fb.trans
    (((ArchiveFrame.of_binary f₂).mono (by decide)).trans f₃)
  have sd' : State data p (3*v) v d:=by
    have hc : 3*left+3*(v-left)=3*v:=by omega
    simpa only [hc,Nat.add_sub_of_le leftBound] using sd
  obtain ⟨f,e₄,sf,f₄⟩:=sd'.reset_index input tape
  obtain ⟨g,e₅,sg,cg,f₅⟩:=sf.copy_count 153 e (by decide) input tape
    (RationalAccumulator.word_of_eq ((f₄.tapes 153 (by decide)).trans
      (fd.tapes 153 (by decide) (by decide))) edgeWord)
    (RationalAccumulator.blank_of_eq (f₄.tapes 1258 (by decide)) cd)
  obtain ⟨c₆,t,e₆,h₆,st,ct,mt,f₆,m₆⟩:=edge_loop data p edgeRoom pair saved paths n fits₀ fits₁ fits₂ room input tape g sg cg
  have finalMemory : t.val.memory=MemoryWord.writeBits s.val.memory p.path.base
      ((packed saved).flatMap (IncidenceEncoding.word p.path.width)):=by
    rw [mt,f₅.memory,f₄.memory,md,f₂.memory,mb,f₀.memory]
    simp only [Nat.zero_mul,Nat.add_zero]
    rw [original_write_pair data left leftBound]
    have originalEq : List.ofFn (Gluing.vertexPoint data)=List.ofFn saved.original.get:=
      congrArg List.ofFn (funext originals).symm
    rw [originalEq,packed_write]
  refine ⟨(15*left.bits.length+21)+(c₁+(c₂+(c₃+((6*v.bits.length+11)+((15*e.bits.length+21)+c₆))))),t,
    e₀.seq (e₁.seq (e₂.seq (e₃.seq (e₄.seq (e₅.seq e₆))))),?_,st,ct,finalMemory,
    fd.trans (((ArchiveFrame.of_binary f₄).mono (by decide)).trans
      (((ArchiveFrame.of_binary f₅).mono (by decide)).trans f₆)),?_⟩
  · unfold price
    omega
  · have first : Tree.Memory.Frame p.path.base (n*p.path.width) s.val.memory d.val.memory:=by
      rw [f₀.memory] at m₁
      rw [f₂.memory] at m₃
      exact m₁.trans m₃
    rw [f₅.memory,f₄.memory] at m₆
    exact first.trans m₆

#print axioms executes
end Maxwell.Cost.RoutingPorts.Complete.GeometryEmission
