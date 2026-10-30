import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-! Exact finite periodic sampling for Banach-valued absolutely
convergent Fourier series. Every congruent integer frequency is retained
in the alias sum; no band-limit premise is imposed. -/

noncomputable section

namespace Maxwell.Continuum.PeriodicSampling

open scoped BigOperators
open AddChar

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable (N : ℕ) [NeZero N]

def phase (n : ℤ) (x : ℝ) : ℂ :=
  Complex.exp (2*(Real.pi : ℂ)*Complex.I*(n : ℂ)*(x : ℂ))

theorem phase_norm (n : ℤ) (x : ℝ) : ‖phase n x‖ = 1 := by
  simp [phase,Complex.norm_exp,Complex.mul_re,Complex.mul_im]

def synthesis (c : ℤ → E) (x : ℝ) : E := ∑' n, phase n x • c n

theorem synthesis_summable (c : ℤ → E) (hc : Summable (fun n => ‖c n‖)) (x : ℝ) :
    Summable (fun n => phase n x • c n) := by
  apply Summable.of_norm_bounded hc
  intro n
  rw [norm_smul,phase_norm,one_mul]

def gridSynthesis (c : ℤ → E) (j : ZMod N) : E :=
  ∑' n : ℤ, ZMod.stdAddChar ((n : ZMod N)*j) • c n

def coefficient (f : ZMod N → E) (k : ZMod N) : E :=
  (N : ℂ)⁻¹ • ∑ j, ZMod.stdAddChar (-(j*k)) • f j

theorem phase_grid (n : ℤ) (j : ZMod N) :
    phase n ((j.val : ℝ)/N) = ZMod.stdAddChar ((n : ZMod N)*j) := by
  have hc : ((n*(j.val : ℤ) : ℤ) : ZMod N) = (n : ZMod N)*j := by
    push_cast
    rw [ZMod.natCast_zmod_val]
  rw [← hc,ZMod.stdAddChar_coe,phase]
  congr 1
  push_cast
  ring

omit [CompleteSpace E] in
theorem synthesis_grid (c : ℤ → E) (j : ZMod N) :
    synthesis c ((j.val : ℝ)/N) = gridSynthesis N c j := by
  apply tsum_congr
  intro n
  rw [phase_grid]

theorem character_sum (a : ZMod N) :
    ∑ j : ZMod N, ZMod.stdAddChar (a*j) = if a = 0 then (N : ℂ) else 0 := by
  classical
  by_cases ha : a = 0
  · simp only [ha,zero_mul,map_zero_eq_one,Finset.sum_const,Finset.card_univ,ZMod.card,
      nsmul_eq_mul,mul_one,↓reduceIte]
  · rw [ite_eq_right ha]
    exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar N ha)

theorem weighted_grid_summable (c : ℤ → E) (hc : Summable (fun n => ‖c n‖))
    (j k : ZMod N) : Summable (fun n : ℤ =>
      ZMod.stdAddChar (-(j*k)) • (ZMod.stdAddChar ((n : ZMod N)*j) • c n)) := by
  apply Summable.of_norm_bounded hc
  intro n
  simp only [norm_smul,ZMod.stdAddChar_apply,Circle.norm_coe,one_mul]
  exact le_rfl

theorem coefficient_gridSynthesis (c : ℤ → E) (hc : Summable (fun n => ‖c n‖))
    (k : ZMod N) :
    coefficient N (gridSynthesis N c) k = ∑' n : ℤ, if (n : ZMod N) = k then c n else 0 := by
  classical
  unfold coefficient gridSynthesis
  simp_rw [← tsum_const_smul'']
  rw [← Summable.tsum_finsetSum (fun j (_ : j ∈ (Finset.univ : Finset (ZMod N))) =>
    weighted_grid_summable N c hc j k)]
  rw [← tsum_const_smul'']
  apply tsum_congr
  intro n
  simp only [smul_smul,← map_add_eq_mul]
  have harg (j : ZMod N) : -(j*k)+(n : ZMod N)*j = ((n : ZMod N)-k)*j := by ring
  simp_rw [harg]
  rw [← Finset.sum_smul,character_sum]
  by_cases hn : (n : ZMod N) = k
  · simp only [hn,sub_self,↓reduceIte,smul_smul]
    rw [inv_mul_cancel₀ (NeZero.ne (N : ℂ)),one_smul]
  · have hs : (n : ZMod N)-k ≠ 0 := sub_ne_zero.mpr hn
    simp only [hs,hn,↓reduceIte,zero_smul,smul_zero]

/-- Literal equispaced samples of the continuous Fourier synthesis. -/
theorem coefficient_samples (c : ℤ → E) (hc : Summable (fun n => ‖c n‖))
    (k : ℤ) : coefficient N (fun j => synthesis c ((j.val : ℝ)/N)) (k : ZMod N) =
      ∑' n : ℤ, if (n : ZMod N) = (k : ZMod N) then c n else 0 := by
  simp_rw [synthesis_grid]
  exact coefficient_gridSynthesis N c hc _

#print axioms coefficient_samples

end Maxwell.Continuum.PeriodicSampling
