import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Abel

/-! Exact block elimination for a bounded negative block of any dimension. -/

namespace Maxwell.Continuum.BlockSchur

variable {G T : Type*}
variable [NormedAddCommGroup G] [NormedSpace ℂ G]
variable [NormedAddCommGroup T] [NormedSpace ℂ T]

theorem projected_negative (P : T →L[ℂ] G) (c m x : T) (b e : G) (ell : ℂ)
    (hc : P c = 0) (hm : P m = b + e) :
    P (c - m - ell • x) = -(b + ell • P x) - e := by
  rw [map_sub, map_sub, map_smul, hc, hm]
  abel

theorem projected_transverse (P : T →L[ℂ] G) (c m x : T) (v f d : G) (ell : ℂ)
    (hc : P c = v) (hm : P m = f + d) :
    P (c - m - ell • x) = (v - d - ell • P x) - f := by
  rw [map_sub, map_sub, map_smul, hc, hm]
  abel

theorem negativeBlock_elimination
    (B R : G →L[ℂ] G) (E : T →L[ℂ] G) (F : G →L[ℂ] T)
    (hBR : ∀ x, B (R x) = x) (hRB : ∀ x, R (B x) = x)
    (g : G) (t v : T) (fG : G) (fT : T) :
    (-B g - E t = fG ∧ v - F g = fT) ↔
      (g = -R (fG + E t) ∧ v + F (R (E t)) = fT - F (R fG)) := by
  constructor
  · rintro ⟨hg, ht⟩
    have hB : B g = -(fG + E t) := by rw [← hg]; abel
    have hr := congrArg R hB
    simp only [hRB, map_neg] at hr
    refine ⟨hr, ?_⟩
    apply eq_sub_iff_add_eq.mpr
    calc
      v + F (R (E t)) + F (R fG) = v - F g := by
        rw [hr, map_neg, map_add, map_add]
        abel
      _ = fT := ht
  · rintro ⟨hg, ht⟩
    constructor
    · rw [hg, map_neg, hBR]
      abel
    · calc
        v - F g = v + F (R (E t)) + F (R fG) := by
          rw [hg, map_neg, map_add, map_add]
          abel
        _ = fT := eq_sub_iff_add_eq.mp ht

end Maxwell.Continuum.BlockSchur
