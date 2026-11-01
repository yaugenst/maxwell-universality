import Maxwell.Continuum.WellMediatorEntry
import Maxwell.Continuum.StoredGeometryState
import Maxwell.Continuum.RationalDataflowArrayWritePrefix

/-! Shared runtime invariant for chronological strength-table passes.
Geometry and arithmetic reuse only scratch; the calibrated rational bank,
rounding power, table metadata, and output cursor survive geometry work. -/
namespace Maxwell.Continuum.RationalDataflow.WellStrengthPass
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 5000000
set_option maxRecDepth 16384

structure State {J : ℕ} (a : PartArray.Table J) (P : ℕ) (values : ℕ→Parts)
    (index : ℕ) (s : Store) : Prop where
  rational : Ready WellStrength.bank values s
  clean : DyadicFloor.Clean s.val
  power : Word s.val 144 (2^P)
  table : a.OutputReady s
  outputIndex : Word s.val 999 index


structure Configuration {J : ℕ} (a : PartArray.Table J) (P B M boundary : ℕ) : Prop where
  metadata : a.MetadataWidth M
  fit : P+4096*(256*(B+1))+4179 ≤ addressValue a.width
  separated : a.Separated
  above : ∀b∈[a.basePositive,a.baseNegative,a.baseDenominator],boundary ≤ addressValue b

theorem Configuration.set {J P B M boundary : ℕ} {a : PartArray.Table J}
    (h : Configuration a P B M boundary) (i : Fin J) (part : Parts) :
    Configuration (a.set i part) P B M boundary :=
  ⟨⟨h.metadata.width,h.metadata.basePositive,h.metadata.baseNegative,h.metadata.baseDenominator,h.metadata.clock⟩,
    h.fit,h.separated,h.above⟩

theorem State.geometry_frame {J P i j : ℕ} {a : PartArray.Table J} {values : ℕ→Parts}
    {s t : Store} (h : State a P values i s) {gv : ℕ→ℕ} (hz : GeometryOutput.Ready gv t)
    (hm : t.val.memory=s.val.memory) (hfour : t.val.tapes 4=s.val.tapes 4)
    (keep : ∀k,10 ≤ k→(k<960 ∨ 989<k)→k ≠ 999→t.val.tapes k=s.val.tapes k)
    (index : Word t.val 999 j) : State a P values j t := by
  have rational : Ready WellStrength.bank values t := by
    refine ⟨?_,hz.natural⟩
    intro k hk
    have outside : k<960 ∨ 989<k := by
      have kn : k∉Finset.Icc 960 989 :=
        Finset.disjoint_left.mp (by decide : Disjoint (ids WellStrength.bank) (Finset.Icc 960 989)) hk
      simp only [Finset.mem_Icc,not_and_or] at kn
      omega
    have notIndex : k ≠ 999 := by intro he;subst k;exact (by decide : 999∉ids WellStrength.bank) hk
    exact word_of_eq (keep k (ids_ge_ten _ _ hk) outside notIndex) (h.rational.1 k hk)
  have clean : DyadicFloor.Clean t.val := by
    refine ⟨blank_of_eq hfour h.clean.1,?_⟩
    intro k hk
    have bounds : 10 ≤ k ∧ k<960 := by
      simp only [DyadicFloor.extraIds,NaturalQuotient.workPorts,Finset.mem_union,
        Finset.mem_insert,Finset.mem_singleton] at hk
      omega
    exact blank_of_eq (keep k bounds.1 (Or.inl bounds.2) (by omega)) (h.clean.2 k hk)
  have out : a.OutputReady t := by
    apply h.table.transfer hm _ hz.scratch hz.seven
    intro k hk
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl|rfl|rfl|rfl|rfl|rfl <;> exact keep _ (by decide) (by decide) (by decide)
  exact ⟨rational,clean,word_of_eq (keep 144 (by decide) (by decide) (by decide)) h.power,out,index⟩

theorem geometry_after_write {n J base width B : ℕ} {data : Vector ℕ n} {clock : List Bool}
    {constants gv : ℕ→ℕ} {a : PartArray.Table J} {s t : Store}
    (g : GeometryOutput.Context data base width B clock constants gv s)
    (i : Fin J) (part : Parts) (out : (a.set i part).OutputReady t)
    (hm : t.val.memory=a.writeMemory i part s.val.memory)
    (below : ∀b∈[a.basePositive,a.baseNegative,a.baseDenominator],base+n*width ≤ addressValue b)
    (keep : ∀k,300 ≤ k→k<1000→t.val.tapes k=s.val.tapes k) :
    GeometryOutput.Context data base width B clock constants gv t := by
  have ready : GeometryOutput.Ready gv t := by
    refine ⟨?_,out.scratch,out.seven⟩
    intro k hk
    have bounds : 960 ≤ k ∧ k ≤ 989 := by
      simp only [GeometryOutput.ids,Finset.mem_erase,Finset.mem_Icc] at hk
      omega
    exact word_of_eq (keep k (by omega) (by omega)) (g.ready.bank k hk)
  refine ⟨ready,g.wordWidth,?_,BankArray.word_of_eq (keep 962 (by decide) (by decide)) g.clockWord,g.fixed⟩
  rw [hm]
  exact a.writeMemory_preserves i part g.array (fun b hb=>Or.inl (below b hb))


theorem geometry_external_frame {n base width B : ℕ} {data : Vector ℕ n} {clock : List Bool}
    {constants gv : ℕ→ℕ} {s t : Store}
    (g : GeometryOutput.Context data base width B clock constants gv s)
    (f : BinaryPrecision.Frame {972,973,999} s.val t.val) :
    GeometryOutput.Context data base width B clock constants gv t := by
  have keep (k : ℕ) (hk : k ≠ 972 ∧ k ≠ 973 ∧ k ≠ 999) :=
    f.tapes k (by simpa only [Finset.mem_insert,Finset.mem_singleton,not_or] using hk)
  have scratch : BankArray.Scratch t.val :=
    ⟨blank_of_eq (keep 0 (by decide)) g.ready.scratch.1,
      blank_of_eq (keep 1 (by decide)) g.ready.scratch.2.1,
      blank_of_eq (keep 2 (by decide)) g.ready.scratch.2.2.1,
      blank_of_eq (keep 3 (by decide)) g.ready.scratch.2.2.2.1,
      blank_of_eq (keep 5 (by decide)) g.ready.scratch.2.2.2.2.1,
      blank_of_eq (keep 6 (by decide)) g.ready.scratch.2.2.2.2.2.1,
      blank_of_eq (keep 8 (by decide)) g.ready.scratch.2.2.2.2.2.2.1,
      blank_of_eq (keep 9 (by decide)) g.ready.scratch.2.2.2.2.2.2.2⟩
  refine ⟨⟨?_,scratch,blank_of_eq (keep 7 (by decide)) g.ready.seven⟩,g.wordWidth,?_,
    BankArray.word_of_eq (keep 962 (by decide)) g.clockWord,g.fixed⟩
  · intro k hk
    exact word_of_eq (keep k (by
      simp only [GeometryOutput.ids,Finset.mem_erase,Finset.mem_Icc] at hk;omega)) (g.ready.bank k hk)
  · simpa only [f.memory] using g.array


theorem geometry_index_frame {n base width B : ℕ} {data : Vector ℕ n} {clock : List Bool}
    {constants gv : ℕ→ℕ} {s t : Store}
    (g : GeometryOutput.Context data base width B clock constants gv s)
    (f : BinaryPrecision.Frame {999} s.val t.val) :
    GeometryOutput.Context data base width B clock constants gv t :=
  geometry_external_frame g (f.mono (by decide))

#print axioms State.geometry_frame
#print axioms geometry_after_write
end Maxwell.Continuum.RationalDataflow.WellStrengthPass
