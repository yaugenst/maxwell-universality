import Maxwell.Continuum.CalibrationSeedRootControlFrame

/-! A complete sparse cache contribution: test support, compute the physical
index, clear shared scratch, read the cache, and accumulate the product. -/
namespace Maxwell.Continuum.Calibration.SeedRoot
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

def changed : Finset ℕ := workspace∪RationalDataflow.workspace slots
structure Frame (s t : Store) : Prop where
  memory : t.val.memory=s.val.memory
  inputHead : t.val.inputHead=s.val.inputHead
  randomCursor : t.val.randomCursor=s.val.randomCursor
  output : t.val.output=s.val.output
  tapes : ∀i,10 ≤ i→i∉changed→t.val.tapes i=s.val.tapes i
  four : t.val.tapes 4=s.val.tapes 4

theorem Frame.trans {s t u : Store} (f : Frame s t) (g : Frame t u) : Frame s u :=
  ⟨g.memory.trans f.memory,g.inputHead.trans f.inputHead,g.randomCursor.trans f.randomCursor,
    g.output.trans f.output,fun i hi ho=>(g.tapes i hi ho).trans (f.tapes i hi ho),
    g.four.trans f.four⟩
theorem Frame.natural {s t : Store} (f : BinaryPrecision.Frame workspace s.val t.val) : Frame s t :=
  ⟨f.memory,f.inputHead,f.randomCursor,f.output,fun i _ hi=>f.tapes i
    (fun hm=>hi (Finset.mem_union_left _ hm)),f.tapes 4 (by decide)⟩

def guardedCode (parity : Corner.Parity) (j : Fin 3) (part : Fin 2) : Code :=
  .seq (testCode parity (cachePart part))
    (.branch 35 (NatAssign.code clearComparison)
      (.seq indexCode (.seq (NatAssign.code clearComparison) (readTermCode parity j part))))
def guardedWidth (B : ℕ) : ℕ := max B (indexWidth (testWidth B))
def guardedCost (B : ℕ) : ℕ := testCost B+1+cleanupCost (testWidth B)+
  indexCost (testWidth B)+cleanupCost (indexWidth (testWidth B))+readTermCost (guardedWidth B)
def guardedValues (M D : ℕ) (a : PartArray.Table (2*(2*D+1)^3))
    (u : Fin 3→ℕ) (parity : Corner.Parity) (j : Fin 3) (part : Fin 2) (v : ℕ→Parts) : ℕ→Parts :=
  if h : inside M D parity u then
    (termControl parity j part).evaluate (Function.update v 24
      (a.get ⟨index M D parity u (cachePart part),index_lt M D parity u (cachePart part) h⟩))
  else v

theorem testWidth_le_guardedWidth (B : ℕ) : testWidth B≤guardedWidth B := by
  have h : testWidth B≤ indexWidth (testWidth B) := by
    unfold indexWidth
    change testWidth B≤128*(testWidth B+1)
    omega
  exact h.trans (le_max_right _ _)

theorem guarded_executes (M D : ℕ) (a : PartArray.Table (2*(2*D+1)^3))
    (parity : Corner.Parity) (j : Fin 3) (part : Fin 2) (n : ℕ→ℕ) (v : ℕ→Parts) (B : ℕ)
    (hM : n 750=M) (hD : n 751=D) (half : n 752=n 750/2)
    (naturalWidth : ∀i∈ids,(n i).bits.length≤B)
    (width : WidthBank slots B v) (good : Good slots v)
    (metadata : a.MetadataWidth B) (entryWidth : ∀i,(a.get i).Width B)
    (entryValid : ∀i,(a.get i).Valid)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (natural : NatAssign.Bank ids n s.val) (ready : Ready slots v s) (table : a.Ready s) :
    ∃cost t w,Executes input tape (guardedCode parity j part) cost s t ∧ cost≤guardedCost B ∧
      Ready slots (guardedValues M D a (coordinates n) parity j part v) t ∧
      Good slots (guardedValues M D a (coordinates n) parity j part v) ∧
      WidthBank slots (termWidth (guardedWidth B))
        (guardedValues M D a (coordinates n) parity j part v) ∧
      NatAssign.Bank ids w t.val ∧ (∀i∈ids,(w i).bits.length≤guardedWidth B) ∧
      (∀i∈retained,w i=n i) ∧ a.Ready t ∧ Frame s t := by
  obtain ⟨c0,b,w,e0,h0,bw,zb,ww,keep,flag,f0⟩ := test_executes parity (cachePart part) n B
    naturalWidth half input tape s natural ready.2
  rw [hM,hD] at flag
  have smallKeep (i : ℕ) (hi : i∈retained) : w i=n i := by
    have hm : i∈extra := by have :=retained_bounds i hi;simp [extra];omega
    exact (keep i hm).trans (prepared_keep parity (cachePart part) n i hi)
  have restore {u : Store} (z : ℕ→ℕ) (f : BinaryPrecision.Frame workspace s.val u.val)
      (bank : NatAssign.Bank ids (cleared z) u.val) (scratch : NatAssign.Scratch u.val) :
      Ready slots v u := by
    apply rational_ready_after_control ready f scratch
    intro i hi
    have hm : i∈ids := Finset.mem_union_right _ hi
    have hw := bank i hm
    rw [cleared_zero z i hi] at hw
    exact hw
  have widthGrow : B≤termWidth (guardedWidth B) := by
    have hh := le_max_left B (indexWidth (testWidth B))
    change B≤16*(guardedWidth B+2)
    change B≤guardedWidth B at hh
    omega
  by_cases supported : inside M D parity (coordinates n)
  · have fields := prepared_fields parity (cachePart part) n half
    have ordered : w 756≤w 753 ∧ w 757≤w 754 ∧ w 758≤w 755 := by
      have h0 := (fields.1 0).1
      have h1 := (fields.1 1).1
      have h2 := (fields.1 2).1
      norm_num only [Fin.val_zero,Fin.val_one,Fin.val_two,Nat.reduceAdd] at h0 h1 h2
      have p0 := (supported 0).1
      have p1 := (supported 1).1
      have p2 := (supported 2).1
      rw [keep 756 (by decide),keep 757 (by decide),keep 758 (by decide),
        smallKeep 753 (by decide),smallKeep 754 (by decide),smallKeep 755 (by decide)]
      simpa [hM,h0,h1,h2,coordinates] using And.intro p0 (And.intro p1 p2)
    have zero : w 762=0 ∧ w 763=0 ∧ w 764=0 := by
      rw [keep 762 (by decide),keep 763 (by decide),keep 764 (by decide)]
      exact ⟨(fields.1 0).2.2,(fields.1 1).2.2,(fields.1 2).2.2⟩
    obtain ⟨c1,c,e1,h1,bc,zc,wc,f1⟩ := index_executes w (testWidth B) ww ordered zero input tape b bw zb
    obtain ⟨c2,d,e2,h2,bd,zd,wd,f2⟩ := cleanup_executes (finished w) (indexWidth (testWidth B)) wc
      input tape c bc zc
    have frame := f0.trans (f1.trans f2)
    have rd := restore (finished w) frame bd zd
    have ad := table_ready_after_control table frame zd
    let ix : Fin (2*(2*D+1)^3) := ⟨index M D parity (coordinates n) (cachePart part),
      index_lt M D parity (coordinates n) (cachePart part) supported⟩
    have indexEq : cleared (finished w) 765=ix.val := by
      rw [cleared_keep _ _ (by decide),finished_congr w (prepared parity (cachePart part) n) keep,
        finished_index parity (cachePart part) n half,hM,hD]
    have iw := bd 765 (by decide)
    rw [indexEq] at iw
    have ib : ix.val.bits.length≤guardedWidth B := by
      rw [←indexEq]
      exact (wd 765 (by decide)).trans (le_max_right _ _)
    have base := le_max_left B (indexWidth (testWidth B))
    obtain ⟨c3,t,e3,h3,rt,gt,wt,ta,out,mem,inp,rnd,tapes,four⟩ := readTerm_executes a ix parity j part v
      (guardedWidth B) (width.mono base) good (metadata.mono base) ((entryWidth ix).mono base)
      (entryValid ix) ib input tape d rd ad iw
    have finalBank : NatAssign.Bank ids (cleared (finished w)) t.val := by
      intro i hi
      rcases Finset.mem_union.mp hi with he|hm
      · have hb := Finset.mem_Icc.mp he
        exact RationalAccumulator.word_of_eq
          (tapes i (by omega) (outside_workspace slots i (Or.inr (by omega)))) (bd i hi)
      · have low : i<1000 := by
          simp only [Finset.mem_insert,Finset.mem_singleton] at hm
          omega
        rw [cleared_zero _ i hm]
        have hw := rt.1 i (Finset.mem_union_right _ (Finset.mem_union_right _ hm))
        rwa [dataValues_small _ low] at hw
    refine ⟨c0+(1+(c1+(c2+c3))),t,cleared (finished w),
      e0.seq (Executes.no (by simpa [supported] using flag) (e1.seq (e2.seq e3))),?_,?_,?_,?_,
      finalBank,fun i hi=>(wd i hi).trans (le_max_right _ _),?_,ta,?_⟩
    · unfold guardedCost
      omega
    · simpa [guardedValues,supported,ix] using rt
    · simpa [guardedValues,supported,ix] using gt
    · simpa [guardedValues,supported,ix] using wt
    · intro i hi
      have hh := retained_bounds i hi
      rw [cleared_keep _ i (by simp [RationalMagnitude.ids];omega),finished_keep w i hi]
      exact smallKeep i hi
    · refine ⟨mem.trans frame.memory,inp.trans frame.inputHead,rnd.trans frame.randomCursor,
        out.trans frame.output,?_,four.trans (frame.tapes 4 (by decide))⟩
      intro i hi ho
      have hn : i∉workspace := fun h=>ho (Finset.mem_union_left _ h)
      have hr : i∉RationalDataflow.workspace slots := fun h=>ho (Finset.mem_union_right _ h)
      exact (tapes i hi hr).trans (frame.tapes i hn)
  · obtain ⟨c1,t,e1,h1,bt,zt,wt,f1⟩ := cleanup_executes w (testWidth B) ww input tape b bw zb
    have frame := f0.trans f1
    have rt := restore w frame bt zt
    refine ⟨c0+(1+c1),t,cleared w,
      e0.seq (Executes.yes (by simpa [supported] using flag) e1),?_,?_,?_,?_,bt,
      fun i hi=>(wt i hi).trans (testWidth_le_guardedWidth B),?_,
      table_ready_after_control table frame zt,Frame.natural frame⟩
    · unfold guardedCost
      omega
    · simpa [guardedValues,supported] using rt
    · simpa [guardedValues,supported] using good
    · simpa [guardedValues,supported] using width.mono widthGrow
    · intro i hi
      have hh := retained_bounds i hi
      rw [cleared_keep _ i (by simp [RationalMagnitude.ids];omega)]
      exact smallKeep i hi

#print axioms guarded_executes
end Maxwell.Continuum.Calibration.SeedRoot
