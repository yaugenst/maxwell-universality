import Maxwell.Spectral.FourLGeometry
import Maxwell.Spectral.UniformLocalNeighborhood

/-! The checked uniform neighborhood count applies at each of the four
actual primitive centers, with its Cartesian displacement unchanged. -/
namespace Maxwell.Spectral.FourLGeometry
open PeriodicYee (Momentum)
open PrimitiveYee ReciprocalCover GlobalCover LocalClusterCount
noncomputable section

theorem center_signed (a : Fin 4) :
    ∃ s : Translation, (∀ j, s j=1 ∨ s j= -1) ∧
      center a = fun j => (s j : ℝ)/2 := by
  fin_cases a
  · refine ⟨![1,1,-1],?_,?_⟩
    · intro j; fin_cases j <;> simp
    · ext j; fin_cases j <;> norm_num [center,point,cartesianMomentum]
  · refine ⟨![1,1,1],?_,?_⟩
    · intro j; fin_cases j <;> simp
    · ext j; fin_cases j <;> norm_num [center,point,cartesianMomentum]
  · refine ⟨![1,-1,1],?_,?_⟩
    · intro j; fin_cases j <;> simp
    · ext j; fin_cases j <;> norm_num [center,point,cartesianMomentum]
  · refine ⟨![-1,1,1],?_,?_⟩
    · intro j; fin_cases j <;> simp
    · ext j; fin_cases j <;> norm_num [center,point,cartesianMomentum]

theorem centered_local_ball (a : Fin 4) (q : Momentum)
    (hr : YeeTaylor.radius q ≤ 1/20) :
    ReciprocalLocalBall (centeredMomentum (point a) q) := by
  obtain ⟨s,hs,hc⟩ := center_signed a
  refine ⟨centeredMomentum (point a) q,0,?_,s,hs,?_⟩
  · simp [reciprocalShift]
  · have he (j : Fin 3) : centeredMomentum (point a) q j-(s j : ℝ)/2=q j := by
      have hj := congrFun hc j
      change center a j+q j-(s j : ℝ)/2=q j
      rw [hj]
      ring
    simp_rw [he]
    rw [← YeeTaylor.radius_sq]
    have hn : 0 ≤ YeeTaylor.radius q := norm_nonneg _
    nlinarith

theorem local_positive_count (hn : NegativeCenters)
    (hc : UniformLocalNeighborhood.CenterCertificate) (a : Fin 4)
    (q : Momentum) (hr : YeeTaylor.radius q ≤ 1/20) :
    (Finset.univ.filter fun i =>
      0 < (YeeTaylorRemainder.centeredOperator_symmetric (point a) q).eigenvalues rfl i ∧
      (YeeTaylorRemainder.centeredOperator_symmetric (point a) q).eigenvalues rfl i < 7/256).card ≤ 2 :=
  UniformLocalNeighborhood.centered_positive_count hn hc (point a) q (centered_local_ball a q hr)

end
end Maxwell.Spectral.FourLGeometry
