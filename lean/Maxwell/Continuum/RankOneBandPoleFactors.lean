import Maxwell.Continuum.RankOneBandInverseAnalytic
import Maxwell.Continuum.RankOneBandDivision

/-! Actual analytic scalar division at the simple band root and the
holomorphic finite-rank factor of the inverse's pole. -/

noncomputable section
namespace Maxwell.Continuum.RankOneBand.Data

set_option backward.isDefEq.respectTransparency false

open Set Metric Filter
open scoped NNReal Topology ContDiff

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {K : H →L[ℂ] H} {u : H} {ell : ℝ} (D : Data K u ell)
variable {V : E → ℂ → H →L[ℂ] H} {U : Set E} (P : PerturbationData V U ell)

def poleDivisor (p : E) (e : ℂ) : ℂ :=
  dslope (fun z => scalarResidual K u ell (V p z) z) (D.bandRoot P p) e

def poleNumerator (p : E) (e : ℂ) : H →L[ℂ] H :=
  (D.poleDivisor P p e)⁻¹ • rankOneNumerator K u ell (V p e) e

def poleResidue (p : E) : H →L[ℂ] H := D.poleNumerator P p (D.bandRoot P p)

def separatedResolvent (p : E) (e : ℂ) : H →L[ℂ] H :=
  dslope (D.poleNumerator P p) (D.bandRoot P p) e - highSolve K u ell (V p e) e

omit [NormedAddCommGroup E] [NormedSpace ℂ E] in
theorem scalarResidual_bandRoot (p : E) (hp : p ∈ U) :
    scalarResidual K u ell (V p (D.bandRoot P p)) (D.bandRoot P p) = 0 := by
  rw [scalarResidual, D.bandRoot_fixed P p hp, sub_self]

omit [NormedAddCommGroup E] [NormedSpace ℂ E] in
theorem scalarResidual_factor (p : E) (hp : p ∈ U) (e : ℂ) :
    (e - D.bandRoot P p) * D.poleDivisor P p e = scalarResidual K u ell (V p e) e :=
  sub_smul_dslope_of_zero (f := fun z => scalarResidual K u ell (V p z) z)
    (D.scalarResidual_bandRoot P p hp) e

variable (hV : AnalyticOnNhd ℂ (Function.uncurry V) (U ×ˢ closedBall (ell : ℂ) (1 / 100)))
include hV

include D P in
theorem analyticAt_family_scalarResidual (p : E) (hp : p ∈ U) (e : ℂ)
    (he : e ∈ closedBall (ell : ℂ) (1 / 100)) :
    AnalyticAt ℂ (fun z => scalarResidual K u ell (V p z) z) e := by
  have ha : AnalyticAt ℂ (V p) e := (hV (p, e) ⟨hp, he⟩).comp₂ analyticAt_const analyticAt_id
  exact D.analyticAt_scalarResidual (V p) id e ha analyticAt_id (P.small p hp e he)
    (by simpa only [mem_closedBall, dist_eq_norm, id_eq] using he)

theorem scalarResidual_deriv_ne_zero (p : E) (hp : p ∈ U) :
    deriv (fun z => scalarResidual K u ell (V p z) z) (D.bandRoot P p) ≠ 0 := by
  have h := (D.contractionData P).residual_deriv_ne_zero
    (D.analyticOnNhd_scalarMap P hV) p hp (D.bandRoot P p) (D.bandRoot_mem P p hp)
  have heq : (fun z => scalarResidual K u ell (V p z) z) =
      fun z => -(z - scalarMap K u ell V p z) := by
    funext z
    simp only [scalarResidual, scalarMap, neg_sub]
  rw [heq]
  change deriv (-(fun z => z - scalarMap K u ell V p z)) (D.bandRoot P p) ≠ 0
  rw [deriv.neg]
  exact neg_ne_zero.mpr h

theorem poleDivisor_ne_zero (p : E) (hp : p ∈ U) (e : ℂ)
    (he : e ∈ closedBall (ell : ℂ) (1 / 100)) : D.poleDivisor P p e ≠ 0 := by
  by_cases hh : e = D.bandRoot P p
  · subst e
    simpa only [poleDivisor, dslope_same] using D.scalarResidual_deriv_ne_zero P hV p hp
  · intro hz
    have h := D.scalarResidual_factor P p hp e
    rw [hz, mul_zero] at h
    exact D.scalarResidual_ne_zero P p hp e he hh h.symm

theorem analyticAt_poleDivisor (p : E) (hp : p ∈ U) (e : ℂ)
    (he : e ∈ closedBall (ell : ℂ) (1 / 100)) : AnalyticAt ℂ (D.poleDivisor P p) e :=
  RankOneBand.analyticAt_dslope
    (D.analyticAt_family_scalarResidual P hV p hp _ (D.bandRoot_mem P p hp))
    (D.analyticAt_family_scalarResidual P hV p hp e he)

theorem analyticAt_poleNumerator (p : E) (hp : p ∈ U) (e : ℂ)
    (he : e ∈ closedBall (ell : ℂ) (1 / 100)) : AnalyticAt ℂ (D.poleNumerator P p) e := by
  have ha : AnalyticAt ℂ (V p) e := (hV (p, e) ⟨hp, he⟩).comp₂ analyticAt_const analyticAt_id
  have hn := D.analyticAt_rankOneNumerator (V p) id e ha analyticAt_id (P.small p hp e he)
    (by simpa only [mem_closedBall, dist_eq_norm, id_eq] using he)
  have hd := (D.analyticAt_poleDivisor P hV p hp e he).inv (D.poleDivisor_ne_zero P hV p hp e he)
  exact (hd.contDiffAt.smul hn.contDiffAt).analyticAt

theorem analyticAt_separatedResolvent (p : E) (hp : p ∈ U) (e : ℂ)
    (he : e ∈ closedBall (ell : ℂ) (1 / 100)) : AnalyticAt ℂ (D.separatedResolvent P p) e := by
  have hnum := RankOneBand.analyticAt_dslope
    (D.analyticAt_poleNumerator P hV p hp _ (D.bandRoot_mem P p hp))
    (D.analyticAt_poleNumerator P hV p hp e he)
  have ha : AnalyticAt ℂ (V p) e := (hV (p, e) ⟨hp, he⟩).comp₂ analyticAt_const analyticAt_id
  exact hnum.sub (D.analyticAt_highSolve (V p) id e ha analyticAt_id
    (P.small p hp e he) (by simpa only [mem_closedBall, dist_eq_norm, id_eq] using he))

#print axioms scalarResidual_factor
#print axioms analyticAt_poleNumerator
#print axioms analyticAt_separatedResolvent

end Maxwell.Continuum.RankOneBand.Data
