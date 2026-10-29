import Maxwell.Certificate.PointWitness.ConventionalCenter
import Maxwell.Spectral.FourLGeometry
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible

/-! The three conventional folded sectors are the three other certified L
centers, with exact primitive reciprocal shifts. -/
namespace Maxwell.Certificate.PointWitness
open Maxwell.Spectral Maxwell.Spectral.PrimitiveYee
open Maxwell.Spectral.PeriodicYee (Momentum)
open FourierBinding FourLGeometry
noncomputable section

theorem other_sector_momentum (b : Folding.Coset) (hb : b ≠ 0) :
    ∃ (a : Fin 4) (n : Translation), a ≠ 0 ∧
      Folding.sectorMomentum pointPrimitiveMomentum b =
        fun j => boundaryMomentum (center a) j+2*Real.pi*(n j : ℝ) := by
  rcases b with ⟨b0,b1⟩
  fin_cases b0 <;> fin_cases b1
  · exact (hb rfl).elim
  · refine ⟨1,0,by decide,?_⟩
    ext j
    fin_cases j <;> simp [Folding.sectorMomentum,Folding.sectorTranslation,
      pointPrimitiveMomentum,timeReversalMomentum,center,point,cartesianMomentum,boundaryMomentum]
    all_goals ring
  · refine ⟨3,![1,1,0],by decide,?_⟩
    ext j
    fin_cases j <;> simp [Folding.sectorMomentum,Folding.sectorTranslation,
      pointPrimitiveMomentum,timeReversalMomentum,center,point,cartesianMomentum,boundaryMomentum]
    all_goals ring
  · refine ⟨2,![0,1,0],by decide,?_⟩
    ext j
    fin_cases j <;> simp [Folding.sectorMomentum,Folding.sectorTranslation,
      pointPrimitiveMomentum,timeReversalMomentum,center,point,cartesianMomentum,boundaryMomentum]
    all_goals ring

theorem other_sector_fiber (b : Folding.Coset) (hb : b ≠ 0) :
    ∃ a : Fin 4, a ≠ 0 ∧
      PrimitiveYee.fiber Concrete.material (Folding.sectorMomentum pointPrimitiveMomentum b) =
        PrimitiveYee.fiber Concrete.material (boundaryMomentum (center a)) := by
  obtain ⟨a,n,ha,hk⟩ := other_sector_momentum b hb
  refine ⟨a,ha,?_⟩
  rw [hk]
  simp only [PrimitiveYee.fiber,ReciprocalCover.curl_integer_periodic]

private theorem eigenvalue_ne_of_invertible {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (T : H →L[ℂ] H) (hT : T.toLinearMap.IsSymmetric) (E : ℝ)
    (h : (T-(E:ℂ) • 1).IsInvertible) (i : Fin (Module.finrank ℂ H)) :
    hT.eigenvalues rfl i ≠ E := by
  intro heq
  let v := hT.eigenvectorBasis rfl i
  have hv : T v = (E:ℂ) • v := by
    have hv := hT.apply_eigenvectorBasis rfl i
    change T v = (hT.eigenvalues rfl i : ℂ) • v at hv
    rwa [heq] at hv
  obtain ⟨e,he⟩ := h
  have hz : e v = e 0 := by
    change e.toContinuousLinearMap v = e.toContinuousLinearMap 0
    rw [he]
    simpa only [sub_apply,smul_apply,
      one_apply_eq_self,map_zero,smul_zero,sub_self] using sub_eq_zero.mpr hv
  have hv0 : v=0 := e.injective hz
  have hn := (hT.eigenvectorBasis rfl).orthonormal.norm_eq_one i
  change ‖v‖=1 at hn
  rw [hv0,norm_zero] at hn
  exact zero_ne_one hn

set_option maxHeartbeats 800000 in
theorem pointOtherSectorExclusion_of_centers
    (hcenter : ∀ a : Fin 4, a ≠ 0 →
      (Matrix.toEuclideanCLM (n := Electric) (𝕜 := ℂ)
        (PrimitiveYee.fiber Concrete.material (boundaryMomentum (center a))) -
          (pointEnergy:ℂ) • 1).IsInvertible) : PointOtherSectorExclusion := by
  intro b hb i
  obtain ⟨a,ha,hfiber⟩ := other_sector_fiber b hb
  have hi : (Matrix.toEuclideanCLM (n := Electric) (𝕜 := ℂ)
      (PrimitiveYee.fiber Concrete.material (Folding.sectorMomentum pointPrimitiveMomentum b))-
        (pointEnergy:ℂ) • 1).IsInvertible := by
    rw [hfiber]
    exact hcenter a ha
  exact eigenvalue_ne_of_invertible _ (SectorSimplicity.primitive_symmetric pointPrimitiveMomentum b)
    pointEnergy hi i

end
end Maxwell.Certificate.PointWitness
