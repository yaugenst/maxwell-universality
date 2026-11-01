import Maxwell.Continuum.CalibrationSeedRootAllocation
import Maxwell.Continuum.CalibrationSeedRootMeasuredInputs
import Maxwell.Continuum.CalibrationSeedRootTableLoop

/-! Runtime allocation, charged reset, and actual row-counter setup construct
the complete seed-table traversal invariant from ordinary stored inputs. -/
namespace Maxwell.Continuum.Calibration.SeedRoot
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384
attribute [local irreducible] producerWidth Allocation.budget Allocation.heap
  Allocation.table Profile.Runtime.memoryTable

def initialCode : Code := .seq Allocation.code (.seq resetCode (NaturalImport.code 787 801))
def initialCost (n : ℕ→ℕ) (B H : ℕ) : ℕ :=
  Allocation.costBound n B H+resetCost (Allocation.budget n)+(37*Allocation.budget n+39)
def initialChanged : Finset ℕ := Allocation.changed∪(rowWorkspace∪RationalDataflow.workspace slots)∪{801}

theorem initial_executes (M D : ℕ) (a : PartArray.Table (2*(2*D+1)^3))
    (n : ℕ→ℕ) (v : ℕ→Parts) (B H : ℕ) (hB : 10≤B)
    (width : ∀k∈Allocation.allIds,(n k).bits.length≤B) (good : Good slots v)
    (size : n 750=M) (degree : n 751=D) (dimension : n 785=aliasArraySize (3*M+D))
    (side : n 786=aliasSide (3*M+D)) (rows : n 787=ArrayDecodeMachine.aliasRowCount (3*M+D))
    (count : n 788=2*aliasArraySize (3*M+D))
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank Allocation.allIds n s.val) (cache : a.Ready s) (raw : Ready slots v s)
    (four : RationalAccumulator.Blank s.val 4) (h37 : RationalAccumulator.Blank s.val 37)
    (h216 : RationalAccumulator.Blank s.val 216)
    (headers : WordCleanup.Bounded PowerMachine.BufferNorm.Allocation.clearHeaders H s.val) :
    ∃cost t,Executes input tape initialCode cost s t ∧ cost ≤ initialCost n B H ∧
      Nonempty (TableState M D (Allocation.budget n) a v (ArrayDecodeMachine.aliasRowCount (3*M+D)) t) ∧
      RationalAccumulator.Word t.val 801 (ArrayDecodeMachine.aliasRowCount (3*M+D)) ∧
      WidthBank slots (Allocation.budget n) (resetParts v) ∧ Good slots (resetParts v) ∧
      a.MetadataWidth (Allocation.budget n) ∧ (∀i,(a.get i).Width (Allocation.budget n)) ∧
      BinaryPrecision.Frame initialChanged s.val t.val := by
  obtain ⟨c0,u,e0,h0,au,ru,out,hm,nu,_,_,_,_,_,f0⟩ := Allocation.executes a n v B H hB width
    input tape s bank cache raw h37 h216 headers
  let W:=Allocation.budget n
  have big : 2≤W := (by decide : 2≤1000).trans (Allocation.budget_ge n)
  have naturalWidth : ∀i∈rowIds,(n i).bits.length≤W := fun i hi=>
    Allocation.budget_bound n i ((by decide : rowIds⊆Allocation.sourceIds) hi)
  have rawWidth : WidthBank slots W v := Allocation.raw_width n v u nu ru
  have cacheMeta : a.MetadataWidth W := Allocation.cache_metadata a n u nu au
  have entries : ∀i,(a.get i).Width W := a.get_width W cacheMeta u au
  let b : PartArray.Table (2*aliasArraySize (3*M+D)) :=
    Profile.Runtime.memoryTable _ (producerWidth W) (Allocation.heap n) (producerWidth_pos _) s.val.memory
  have transport (q : ℕ) (eq : q=2*aliasArraySize (3*M+D))
      (h : (Profile.Runtime.memoryTable q (producerWidth W) (Allocation.heap n)
          (producerWidth_pos _) s.val.memory).OutputReady u ∧
        (Profile.Runtime.memoryTable q (producerWidth W) (Allocation.heap n)
          (producerWidth_pos _) s.val.memory).MetadataWidth (producerWidth W) ∧
        a.SeparatedFrom (Profile.Runtime.memoryTable q (producerWidth W) (Allocation.heap n)
          (producerWidth_pos _) s.val.memory)) :
      b.OutputReady u ∧ b.MetadataWidth (producerWidth W) ∧ a.SeparatedFrom b := by
    subst q
    exact h
  have hd:=Allocation.cache_disjoint a n u nu au (by rw [degree]) s.val.memory
  obtain ⟨output,metadata,disjoint⟩ := transport (n 788) count
    (by simpa only [Allocation.table] using And.intro out (And.intro hm hd))
  obtain ⟨c1,w,e1,h1,nw,ww,rw,gw,vw,f1,four1⟩ := reset_executes n v W W (by omega) le_rfl
    naturalWidth rawWidth good (fun i hi=>naturalWidth i ((by decide : fixedFields⊆rowIds) hi))
    (fun i hi _=>rawWidth i hi) input tape u
    (fun i hi=>nu i ((by decide : rowIds⊆Allocation.sourceIds) hi)) ru
  have arrays1:=arrays_after_reset au output f1 rw.2
  have counter0 : RationalAccumulator.Word w.val 801 (n 801) :=
    RationalAccumulator.word_of_eq (f1.tapes 801 (by decide)) (nu 801 (by decide))
  have source : RationalAccumulator.Word w.val 787 (n 787) := by
    simpa only [resetNumbers_keep n 787 (by decide)] using nw 787 (by decide)
  obtain ⟨c2,t,e2,h2,counterBank,f2⟩ := NaturalImport.executes {801} 787 801
    (by decide) (by decide) n (n 787).bits input tape w
    (by intro k hk;have he:=Finset.mem_singleton.mp hk;subst k;exact counter0) source
  have counter : RationalAccumulator.Word t.val 801 (ArrayDecodeMachine.aliasRowCount (3*M+D)) := by
    simpa only [Function.update_self,addressValue_bits,rows] using counterBank 801 (by decide)
  have arrays2:=PartArray.arrays_high_word (by decide : 216≤801) arrays1.1 arrays1.2 f2
  have rawT : Ready slots (resetParts v) t := by
    constructor
    · intro i hi
      have ne : i≠801 := by intro he;subst i;exact (by decide : 801∉RationalDataflow.ids slots) hi
      exact RationalAccumulator.word_of_eq (f2.tapes i (by simpa using ne)) (rw.1 i hi)
    · intro i hi
      exact RationalAccumulator.blank_of_eq (f2.tapes i (by simp;omega)) (rw.2 i hi)
  have nt : NatAssign.Bank rowIds (resetNumbers n) t.val := by
    intro i hi
    have ne : i≠801 := by intro he;subst i;exact (by decide : 801∉rowIds) hi
    exact RationalAccumulator.word_of_eq (f2.tapes i (by simpa using ne)) (nw i hi)
  have state : TableState M D W a v (ArrayDecodeMachine.aliasRowCount (3*M+D)) t := {
    table := b
    remaining_le := le_rfl
    numbers := resetNumbers n
    natural := nt
    naturalWidth := ww
    size := (resetNumbers_keep n 750 (by decide)).trans size
    degree := (resetNumbers_keep n 751 (by decide)).trans degree
    dimension := (resetNumbers_keep n 785 (by decide)).trans dimension
    side := (resetNumbers_keep n 786 (by decide)).trans side
    raw := rawT
    four := RationalAccumulator.blank_of_eq
      ((f2.tapes 4 (by decide)).trans (four1.trans (f0.tapes 4 (by decide)))) four
    cache := arrays2.1
    ready := arrays2.2
    metadata := metadata
    positive := by simpa only [b,Profile.Runtime.memoryTable,addressValue_bits] using producerWidth_pos W
    fits := by simp only [b,Profile.Runtime.memoryTable,addressValue_bits,le_refl]
    separated := Profile.Runtime.memoryTable_separated _ _ _ _ _
    disjoint := disjoint
    correct := by intro row hr j p;have hlt:=row.isLt;omega }
  have frame : BinaryPrecision.Frame initialChanged s.val t.val :=
    (f0.mono (Finset.subset_union_left.trans Finset.subset_union_left)).trans
      ((f1.mono (Finset.subset_union_right.trans Finset.subset_union_left)).trans
        (f2.mono Finset.subset_union_right))
  refine ⟨c0+(c1+c2),t,e0.seq (e1.seq e2),?_,⟨state⟩,counter,vw,gw,cacheMeta,entries,frame⟩
  have old:=Allocation.budget_bound n 801 (by decide)
  have src:=naturalWidth 787 (by decide)
  unfold initialCost
  dsimp only [W] at h1 src
  omega

#print axioms initial_executes
end Maxwell.Continuum.Calibration.SeedRoot
