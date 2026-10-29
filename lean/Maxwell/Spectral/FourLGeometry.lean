import Maxwell.Spectral.GlobalCover
import Maxwell.Spectral.LocalClusterCount

/-! The eight signed L corners reduce to exactly the four certified primitive
TRIM by reciprocal translations. This uses no symmetry of the perturbed material. -/
namespace Maxwell.Spectral.FourLGeometry
open Maxwell.Certificate.FourierBinding
open PeriodicYee (Momentum Direction)
open PrimitiveYee ReciprocalCover GlobalCover LocalClusterCount
noncomputable section

def point (a : Fin 4) : Translation :=
  ![![1,1,0],![1,1,1],![1,0,1],![-1,0,0]] a

def center (a : Fin 4) : Momentum := cartesianMomentum (fun j => (point a j : ℝ)/2)

theorem signed_center (s : Translation) (hs : ∀ j, s j=1 ∨ s j= -1) :
    ∃ (a : Fin 4) (n : Translation), (fun j => (s j : ℝ)/2) = center a+reciprocalShift n := by
  rcases hs 0 with h0 | h0 <;> rcases hs 1 with h1 | h1 <;> rcases hs 2 with h2 | h2
  · refine ⟨1,0,?_⟩
    ext j
    fin_cases j <;> norm_num [center, point, cartesianMomentum, reciprocalShift, h0,h1,h2]
  · refine ⟨0,0,?_⟩
    ext j
    fin_cases j <;> norm_num [center, point, cartesianMomentum, reciprocalShift, h0,h1,h2]
  · refine ⟨2,0,?_⟩
    ext j
    fin_cases j <;> norm_num [center, point, cartesianMomentum, reciprocalShift, h0,h1,h2]
  · refine ⟨3,![1,0,0],?_⟩
    ext j
    fin_cases j <;> norm_num [center, point, cartesianMomentum, reciprocalShift, h0,h1,h2]
  · refine ⟨3,0,?_⟩
    ext j
    fin_cases j <;> norm_num [center, point, cartesianMomentum, reciprocalShift, h0,h1,h2]
  · refine ⟨2,![-1,0,-1],?_⟩
    ext j
    fin_cases j <;> norm_num [center, point, cartesianMomentum, reciprocalShift, h0,h1,h2]
  · refine ⟨0,![-1,-1,0],?_⟩
    ext j
    fin_cases j <;> norm_num [center, point, cartesianMomentum, reciprocalShift, h0,h1,h2]
  · refine ⟨1,![-1,-1,-1],?_⟩
    ext j
    fin_cases j <;> norm_num [center, point, cartesianMomentum, reciprocalShift, h0,h1,h2]

theorem signed_local_decomposition (v : Momentum) (hv : SignedLocalBall v) :
    ∃ (a : Fin 4) (n : Translation) (q : Momentum),
      v = centeredMomentum (point a) q+reciprocalShift n ∧ YeeTaylor.radius q ≤ 1/20 := by
  obtain ⟨s,hs,hbound⟩ := hv
  obtain ⟨a,n,hn⟩ := signed_center s hs
  let q : Momentum := fun j => v j-(s j : ℝ)/2
  refine ⟨a,n,q,?_,?_⟩
  · have he := congrFun hn
    ext j
    have hj := he j
    change (s j : ℝ)/2 = center a j+reciprocalShift n j at hj
    change v j = center a j+q j+reciprocalShift n j
    dsimp [q]
    linarith
  · have hsq : YeeTaylor.radius q^2 ≤ 1/400 := by
      rw [YeeTaylor.radius_sq]
      exact hbound
    have hq : 0 ≤ YeeTaylor.radius q := norm_nonneg _
    nlinarith

theorem reciprocal_local_decomposition (c : Momentum) (hc : ReciprocalLocalBall c) :
    ∃ (a : Fin 4) (n : Translation) (q : Momentum),
      c = centeredMomentum (point a) q+reciprocalShift n ∧ YeeTaylor.radius q ≤ 1/20 := by
  obtain ⟨v,n,rfl,hv⟩ := hc
  obtain ⟨a,m,q,hv,hq⟩ := signed_local_decomposition v hv
  refine ⟨a,m+n,q,?_,hq⟩
  rw [hv, reciprocalShift_add, add_assoc]

end
end Maxwell.Spectral.FourLGeometry
