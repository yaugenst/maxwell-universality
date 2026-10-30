import Maxwell.Continuum.SourceDecorationEnumeration
import Maxwell.Continuum.ContinuumGeometryWords

/-! Exact continuum center arithmetic on the chronological well stream.
The coordinate multiplier, length, spacing and buffer are ordinary stored
integer/natural inputs; the semantic theorem identifies their selected values. -/
namespace Maxwell.Composition.SourceDecorationEnumeration
open Maxwell.Logical Maxwell.Logical.Routing Maxwell.Spectral.Lattice
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192

def centerPoint (B : Fin 3→ℤ) (L d t : ℕ) (x : Site) : Site :=
  fun k => 2*((((L+L*t+8+1)/2:ℕ):ℤ)+(L:ℤ)*(d:ℤ)*(B k*x k))

def centers {v e : ℕ} (B : Fin 3→ℤ) (L d t : ℕ)
    (saved : SourceEmission.Geometry v e) : List Site :=
  (sites saved).map (centerPoint B L d t)

theorem centers_length {v e : ℕ} (B : Fin 3→ℤ) (L d t : ℕ)
    (saved : SourceEmission.Geometry v e) : (centers B L d t saved).length=siteCount saved := by
  rw [centers,List.length_map,sites_length]

theorem centerPoint_injective (B : Fin 3→ℤ) {L d t : ℕ} (hL : 0<L) (hd : 0<d)
    (hB : ∀k,B k≠0) : Function.Injective (centerPoint B L d t) := by
  intro x y h
  funext k
  have hk := congrFun h k
  dsimp only [centerPoint] at hk
  have hL' : (L:ℤ)≠0 := by exact_mod_cast Nat.ne_of_gt hL
  have hd' : (d:ℤ)≠0 := by exact_mod_cast Nat.ne_of_gt hd
  exact mul_left_cancel₀ (hB k)
    (mul_left_cancel₀ (mul_ne_zero hL' hd')
      (add_left_cancel (mul_left_cancel₀ (by decide : (2:ℤ)≠0) hk)))

noncomputable section
open Maxwell.Continuum Maxwell.Continuum.RealizationParameters
open Maxwell.Continuum.PeriodicBand
variable (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0<S.nnz)

theorem centerPoint_site (v : SourceDecoration.Vertex S (precision p S hm)) :
    centerPoint placementDiagonal (length p S hm) (spacing p S hm) (bufferSteps p S hm)
      (SourceDecoration.site S (precision p S hm) v)=integerCenter p S hm v := by
  funext k
  simp only [centerPoint,integerCenter,Parameters.sourceCell,EffectiveMass.placementCell,
    Parameters.translationCell,Parameters.margin,placementMatrix,Matrix.mulVec_diagonal]

theorem Represents.centers_eq {saved} (h : Represents S (precision p S hm) saved) :
    centers placementDiagonal (length p S hm) (spacing p S hm) (bufferSteps p S hm) saved=
      (vertexList S (precision p S hm)).map (integerCenter p S hm) := by
  rw [centers,h.sites_eq,List.map_map]
  apply List.map_congr_left
  intro v _
  exact centerPoint_site p S hm v

theorem Represents.centers_nodup {saved} (h : Represents S (precision p S hm) saved) :
    (centers placementDiagonal (length p S hm) (spacing p S hm) (bufferSteps p S hm) saved).Nodup := by
  exact h.sites_nodup.map (centerPoint_injective placementDiagonal (length_pos p S hm)
    (spacing_pos p S hm) (fun k => by fin_cases k <;> norm_num [placementDiagonal]))

theorem Represents.mem_centers_iff {saved} (h : Represents S (precision p S hm) saved) (x : Site) :
    x∈centers placementDiagonal (length p S hm) (spacing p S hm) (bufferSteps p S hm) saved ↔
      ∃v,integerCenter p S hm v=x := by
  rw [h.centers_eq,List.mem_map]
  exact ⟨fun ⟨v,_,hx⟩ => ⟨v,hx⟩,
    fun ⟨v,hx⟩ => ⟨v,vertexList_complete S (precision p S hm) v,hx⟩⟩

#print axioms Represents.centers_eq
#print axioms Represents.centers_nodup
#print axioms Represents.mem_centers_iff
end
end Maxwell.Composition.SourceDecorationEnumeration
