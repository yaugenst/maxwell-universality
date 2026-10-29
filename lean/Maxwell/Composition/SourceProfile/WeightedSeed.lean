import Maxwell.Composition.SourceProfile.Geometry
import Maxwell.Composition.SourceSeedWords

/-! The actual quarter weights admit one fixed integer repack: multiply
signed qhat channels by 12/count and use denominator 3*qhatDen. -/
noncomputable section
namespace Maxwell.Composition.SourceProfile
open Maxwell.Defect Maxwell.Defect.FiniteStencil
open Maxwell.Spectral Maxwell.Spectral.Lattice
open SourceSeedWords
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 1000000

def factor (P : PhysicalPlatform) (k : PhysicalSource.Local P) : ℕ :=
  12/incidentCount P k

theorem incidentCount_le_four (P : PhysicalPlatform) (k : PhysicalSource.Local P) :
    incidentCount P k≤4 := by
  have h := (ScalarDefect.coordinateWeight_bounds P.defect k).2
  rw [weight_eq] at h
  have h' : (incidentCount P k:ℚ)≤4 := by linarith
  exact_mod_cast h'

theorem incidentCount_dvd_twelve (P : PhysicalPlatform) (k : PhysicalSource.Local P) :
    incidentCount P k ∣ 12 := by
  have hp := incidentCount_pos P k
  have hl := incidentCount_le_four P k
  have h : incidentCount P k=1 ∨ incidentCount P k=2 ∨
      incidentCount P k=3 ∨ incidentCount P k=4 := by omega
  rcases h with h|h|h|h <;> rw [h] <;> decide

theorem factor_le (P : PhysicalPlatform) (k : PhysicalSource.Local P) : factor P k≤12 :=
  Nat.div_le_self _ _

theorem factor_value (P : PhysicalPlatform) (k : PhysicalSource.Local P) :
    (factor P k:ℚ)/3=(ScalarDefect.coordinateWeight P.defect k)⁻¹ := by
  have h := Nat.mul_div_cancel' (incidentCount_dvd_twelve P k)
  have hc : (incidentCount P k:ℚ)≠0 := by exact_mod_cast Nat.ne_of_gt (incidentCount_pos P k)
  have hh : (incidentCount P k:ℚ)*(factor P k:ℚ)=12 := by exact_mod_cast h
  rw [weight_eq]
  field_simp
  nlinarith only [hh]

/-- Sparse repacking sums only over the fixed prototype edges. Every
coefficient is generated from the actual supplied signed qhat channels. -/
def weightedChannel (P : PhysicalPlatform) (a : PhysicalSource.Local P→ℕ) (i : Index P) : ℕ :=
  ∑ k, if radixEdge (radius P) i=ScalarDefect.edgeEmbedding P.defect k then factor P k*a k else 0

theorem weightedChannel_value (P : PhysicalPlatform) (positive negative : PhysicalSource.Local P→ℕ)
    (denominator : ℕ) (hden : 0<denominator) (q : PhysicalSource.Local P→ℚ)
    (hq : ∀ k,((positive k:ℚ)-negative k)/denominator=q k) (i : Index P) :
    ((weightedChannel P positive i:ℚ)-weightedChannel P negative i)/(3*denominator)=
      coefficients (radixCubeEmbedding (radius P)) (seed P q) i := by
  simp only [weightedChannel,Nat.cast_sum,Nat.cast_ite,Nat.cast_mul,Nat.cast_zero,
    ←Finset.sum_sub_distrib,Finset.sum_div]
  change (∑ k, ((if radixEdge (radius P) i=ScalarDefect.edgeEmbedding P.defect k then
      (factor P k:ℚ)*positive k else 0)-(if radixEdge (radius P) i=ScalarDefect.edgeEmbedding P.defect k then
      (factor P k:ℚ)*negative k else 0))/(3*denominator)) = _
  simp only [coefficients,seed,evaluate,List.map_ofFn,List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro k _
  change _ = if radixEdge (radius P) i=ScalarDefect.edgeEmbedding P.defect k then
    (ScalarDefect.coordinateWeight P.defect k)⁻¹*q k else 0
  split_ifs
  · rw [←factor_value,←hq k]
    ring
  · simp

/-- The single fixed-cube matrix action has the exact full local profile
semantics; the cube contains every intermediate stencil coordinate. -/
theorem dense_profile (P : PhysicalPlatform) (σ : ℚ) (q : PhysicalSource.Local P→ℚ) :
    coefficients (radixCubeEmbedding (radius P)) (profile P σ q) =
      stencilMatrix (radixCubeEmbedding (radius P)) (mass P.background) σ *ᵥ
        coefficients (radixCubeEmbedding (radius P)) (seed P q) := by
  apply coefficients_step _ (mass P.background) 25 (by norm_num)
    (fun e => by rw [mass_cast]; exact P.background.edge_bound e) σ (seed P q)
  intro t ht
  exact radixCubeEmbedding_covers (radius P) t.1
    (fun j => (seed_supported P q t ht j).trans (by unfold radius; exact_mod_cast (show
      SourceDefectLayout.radius P.defect+1≤SourceDefectLayout.radius P.defect+3 by omega)))

end Maxwell.Composition.SourceProfile
