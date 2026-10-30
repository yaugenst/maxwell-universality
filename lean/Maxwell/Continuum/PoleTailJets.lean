import Maxwell.Continuum.PoleChartCutoff
import Maxwell.Continuum.PoleOscillatoryIntegral
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! Actual real derivatives of the cutoff simple-pole tail. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048

namespace Maxwell.Continuum.OscillatoryPole

open Complex Real MeasureTheory Set Filter PeriodicBand
open scoped Topology ContDiff

def complexCutoff (a u : ℝ) : ℂ := scaledPsi a u
def cutoffComplement (a u : ℝ) : ℂ := 1 - complexCutoff a u
def poleTail (a : ℝ) (p : ℂ) (u : ℝ) : ℂ := cutoffComplement a u * poleSimple p u
def poleJet (p : ℂ) (n : ℕ) (u : ℝ) : ℂ :=
  (-1 : ℂ)^n * (n.factorial : ℂ) / ((u : ℂ)-p)^(n+1)

theorem complexCutoff_contDiff (a : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (complexCutoff a) :=
  Complex.ofRealCLM.contDiff.comp (scaledPsi_contDiff a)

theorem complexCutoff_iteratedDeriv (a : ℝ) (n : ℕ) (u : ℝ) :
    iteratedDeriv n (complexCutoff a) u = (iteratedDeriv n (scaledPsi a) u : ℝ) := by
  have he := Complex.ofRealCLM.iteratedFDeriv_comp_left (x := u)
    ((scaledPsi_contDiff a).contDiffAt.of_le (show (n : ℕ∞ω) ≤ (⊤ : ℕ∞) by simp)) le_rfl
  unfold iteratedDeriv
  exact congrArg (fun f => f (fun _ => (1 : ℝ))) he

theorem cutoffComplement_contDiff (a : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (cutoffComplement a) :=
  contDiff_const.sub (complexCutoff_contDiff a)

theorem poleSimple_contDiff {p : ℂ} (hp : 0 < p.im) : ContDiff ℝ (⊤ : ℕ∞) (poleSimple p) := by
  change ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => 1 / ((u : ℂ)-p))
  simpa only [one_div, Complex.ofRealCLM_apply] using
    (Complex.ofRealCLM.contDiff.sub (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : ℝ => p))).fun_inv
      (real_sub_pole_ne_zero hp)

theorem poleTail_contDiff (a : ℝ) {p : ℂ} (hp : 0 < p.im) :
    ContDiff ℝ (⊤ : ℕ∞) (poleTail a p) :=
  (cutoffComplement_contDiff a).mul (poleSimple_contDiff hp)

theorem poleJet_hasDerivAt {p : ℂ} (hp : 0 < p.im) (n : ℕ) (u : ℝ) :
    HasDerivAt (poleJet p n) (poleJet p (n+1) u) u := by
  have hd := (hasDerivAt_const u ((-1 : ℂ)^n * (n.factorial : ℂ))).div
    ((((hasDerivAt_id u).ofReal_comp).sub_const p).pow (n+1))
    (pow_ne_zero _ (real_sub_pole_ne_zero hp u))
  convert hd using 1
  · rfl
  · simp only [poleJet, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
      id_eq, Complex.ofReal_one, mul_one, zero_mul, zero_sub, Pi.pow_apply,
      Nat.add_sub_cancel]
    rw [pow_succ (-1 : ℂ)]
    field_simp [real_sub_pole_ne_zero hp u]
    ring

theorem poleSimple_iteratedDeriv {p : ℂ} (hp : 0 < p.im) (n : ℕ) :
    iteratedDeriv n (poleSimple p) = poleJet p n := by
  induction n with
  | zero => ext u; simp [poleSimple, poleJet]
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext u
    exact (poleJet_hasDerivAt hp n u).deriv

theorem poleJet_norm (p : ℂ) (n : ℕ) (u : ℝ) :
    ‖poleJet p n u‖ = (n.factorial : ℝ) / ‖(u : ℂ)-p‖^(n+1) := by
  simp only [poleJet, norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
    Complex.norm_natCast, one_mul]

theorem poleTail_iteratedDeriv {p : ℂ} (hp : 0 < p.im) (a : ℝ) (n : ℕ) (u : ℝ) :
    iteratedDeriv n (poleTail a p) u = ∑ k ∈ Finset.range (n+1),
      (n.choose k : ℂ) * iteratedDeriv k (cutoffComplement a) u * poleJet p (n-k) u := by
  unfold poleTail
  rw [iteratedDeriv_fun_mul ((cutoffComplement_contDiff a).contDiffAt.of_le (by simp))
    ((poleSimple_contDiff hp).contDiffAt.of_le (by simp))]
  simp only [poleSimple_iteratedDeriv hp]

theorem cutoffComplement_iteratedDeriv_pos (a : ℝ) {n : ℕ} (hn : 0 < n) (u : ℝ) :
    iteratedDeriv n (cutoffComplement a) u = -((iteratedDeriv n (scaledPsi a) u : ℝ) : ℂ) := by
  unfold cutoffComplement
  rw [iteratedDeriv_const_sub hn, iteratedDeriv_neg, complexCutoff_iteratedDeriv]

theorem poleTail_eq_zero_near {a : ℝ} (ha : 0 < a) (p : ℂ) {u : ℝ} (hu : |u| < a) :
    poleTail a p =ᶠ[𝓝 u] 0 := by
  filter_upwards [(isOpen_lt continuous_abs continuous_const).mem_nhds hu] with v hv
  simp only [poleTail, cutoffComplement, complexCutoff,
    scaledPsi_eq_one ha hv.le, Complex.ofReal_one, sub_self, zero_mul, Pi.zero_apply]

theorem poleTail_iteratedDeriv_zero {a : ℝ} (ha : 0 < a) (p : ℂ) {u : ℝ}
    (hu : |u| < a) (n : ℕ) : iteratedDeriv n (poleTail a p) u = 0 := by
  rw [(poleTail_eq_zero_near ha p hu).iteratedDeriv_eq n]
  simp

#print axioms poleTail_iteratedDeriv
#print axioms poleTail_iteratedDeriv_zero

end Maxwell.Continuum.OscillatoryPole
