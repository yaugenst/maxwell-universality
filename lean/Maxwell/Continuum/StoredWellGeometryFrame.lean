import Maxwell.Continuum.StoredWellPayload
import Maxwell.Continuum.StoredGeometryMediator
import Maxwell.Continuum.StoredGeometryPathSetup
import Maxwell.Continuum.RationalDataflowReadFootprint

/-! Geometry and payload encoders share only cleared arithmetic scratch.
Their concrete stored data and cursors survive the other stage. -/
namespace Maxwell.Continuum.WellPayload
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
open RationalDataflow RationalDataflow.PartArray
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

theorem State.geometry_frame {J P B j : ℕ} {strengths : Table J} {profile template : List Bool}
    {values : ℕ→Parts} {s t : Store} (h : State strengths P B j profile template values s)
    {v : ℕ→ℕ} (hz : GeometryOutput.Ready v t) (hm : t.val.memory=s.val.memory)
    (keep : ∀k,10 ≤ k → (k<960 ∨ 989<k) → t.val.tapes k=s.val.tapes k) :
    State strengths P B j profile template values t := by
  have rt : RationalDataflow.Ready StoredInteger.slots values t := by
    refine ⟨?_,hz.natural⟩
    intro k hk
    have kk : k<960 ∨ 989<k := by
      have kn : k∉Finset.Icc 960 989 :=
        Finset.disjoint_left.mp (by decide : Disjoint (RationalDataflow.ids StoredInteger.slots)
          (Finset.Icc 960 989)) hk
      simp only [Finset.mem_Icc,not_and_or] at kn
      omega
    exact word_of_eq (keep k (ids_ge_ten StoredInteger.slots k hk) kk) (h.ready.1 k hk)
  have arrt : strengths.Ready t := by
    refine ⟨hz.scratch,hz.seven,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · exact BankArray.word_of_eq (keep 200 (by decide) (by decide)) h.table.width
    · exact BankArray.word_of_eq (keep 202 (by decide) (by decide)) h.table.basePositive
    · exact BankArray.word_of_eq (keep 203 (by decide) (by decide)) h.table.baseNegative
    · exact BankArray.word_of_eq (keep 204 (by decide) (by decide)) h.table.baseDenominator
    · exact BankArray.word_of_eq (keep 205 (by decide) (by decide)) h.table.clock
    · simpa only [hm] using h.table.positive
    · simpa only [hm] using h.table.negative
    · simpa only [hm] using h.table.denominator
  exact ⟨rt,h.width,arrt,word_of_eq (keep 728 (by decide) (by decide)) h.index,
    word_of_eq (keep 727 (by decide) (by decide)) h.one,
    word_of_eq (keep 990 (by decide) (by decide)) h.precision,
    BankArray.word_of_eq (keep 991 (by decide) (by decide)) h.profileWord,
    BankArray.word_of_eq (keep 992 (by decide) (by decide)) h.templateWord⟩

theorem geometry_context_frame {n base width BG J P B j : ℕ} {data : Vector ℕ n} {clock : List Bool}
    {constants v : ℕ→ℕ} {strengths : Table J} {profile template : List Bool}
    {values : ℕ→Parts} {s t : Store}
    (h : GeometryOutput.Context data base width BG clock constants v s)
    (ht : State strengths P B j profile template values t)
    (hm : t.val.memory=s.val.memory)
    (keep : ∀k,10 ≤ k → k∉cellPorts 0 → k≠728 → t.val.tapes k=s.val.tapes k) :
    GeometryOutput.Context data base width BG clock constants v t := by
  have kt (k : ℕ) (hlo : 960 ≤ k) (hhi : k≤989) : t.val.tapes k=s.val.tapes k :=
    keep k (by omega) (by simp only [cellPorts,positivePort,negativePort,denominatorPort,
      Finset.mem_insert,Finset.mem_singleton];omega) (by omega)
  have rt : GeometryOutput.Ready v t := by
    refine ⟨?_,ht.table.scratch,ht.table.seven⟩
    intro k hk
    have hb := hk
    simp only [GeometryOutput.ids,Finset.mem_erase,Finset.mem_Icc] at hb
    exact word_of_eq (kt k (by omega) (by omega)) (h.ready.bank k hk)
  exact ⟨rt,h.wordWidth,by simpa only [hm] using h.array,
    BankArray.word_of_eq (kt 962 (by decide) (by decide)) h.clockWord,h.fixed⟩

theorem terminalStep_memory : GeometryOutput.terminalStepCode.protectsMemory=true := by decide
theorem mediatorStep_memory : GeometryOutput.mediatorStepCode.protectsMemory=true := by decide

theorem pathSetup_memory (trim : ℕ) : (GeometryOutput.pathSetupCode trim).protectsMemory=true := by
  have ht : (GeometryOutput.trimCounterCode 973 trim).protectsMemory=true := by
    induction trim with
    | zero => rfl
    | succ k ih => simpa only [GeometryOutput.trimCounterCode,Code.protectsMemory,
        show (CountedShifted.test 973).protectsMemory=true from by decide,Bool.true_and] using ih
  simp only [GeometryOutput.pathSetupCode,Code.protectsMemory,ht]
  decide

#print axioms State.geometry_frame
#print axioms geometry_context_frame
end Maxwell.Continuum.WellPayload
