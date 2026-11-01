import Maxwell.Continuum.CalibrationRootTableComputed
import Maxwell.Continuum.CalibrationSeedRootMeaning
import Maxwell.Continuum.RationalDataflowArrayPromote

/-! The actual computed root table supplies the seed convolution cache.
Its input descriptor is established by five charged physical header copies. -/
namespace Maxwell.Continuum.Calibration.SeedRoot
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384

theorem cache_promote_executes (grid P B I W H N ell : ℕ) [NeZero grid] (scale : Parts)
    (hgrid : grid=rootSamplingGrid scale.value N ell)
    (hprecision : P=rootSamplingBits scale.value N ell)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (state : RootTable.TableState (2*grid^3) grid P B I W scale 0 s)
    (old : WordCleanup.Bounded PartArray.Promote.headers H s.val) :
    ∃cost t,∃a : PartArray.Table (2*(2*rootDegree scale.value N ell+1)^3),
      Executes input tape PartArray.Promote.code cost s t ∧ cost≤256*(W+H+1) ∧
      a.Ready t ∧ a.OutputReady t ∧ a.MetadataWidth W ∧ (∀i,(a.get i).Valid) ∧
      CacheCorrect (rootDegree scale.value N ell) a
        (fun ν=>rectangleRational (computedRootCoefficient scale.value N ell ν)) ∧
      BinaryPrecision.Frame PartArray.Promote.changed s.val t.val := by
  subst grid
  obtain ⟨cost,t,e,hc,ready,output,frame⟩ := PartArray.Promote.executes state.table W H state.metadata
    input tape s state.ready old
  refine ⟨cost,t,state.table,e,hc,ready,output,state.metadata,?_,?_,frame⟩
  · intro i
    exact (state.computed_correct N ell rfl hprecision i).1
  · intro i
    exact (state.computed_correct N ell rfl hprecision i).2.2

theorem computed_grid (n : ℕ→ℕ) (scale : Parts) (denominator : 0<n 332)
    (value : scale.value=(n 330:ℚ)/n 332) :
    RootParameters.values n 331=rootSamplingGrid scale.value (n 333) (n 334) ∧
    RootParameters.values n 640=rootSamplingBits scale.value (n 333) (n 334) := by
  rw [value]
  exact RootTable.requested_parameters n denominator

#print axioms cache_promote_executes
end Maxwell.Continuum.Calibration.SeedRoot
