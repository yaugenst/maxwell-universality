import Maxwell.Defect.RobustGap
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Sequences

/-! Completeness of residual and quadratic-gap certificates for convergent
finite approximations of an actual isolated eigenpair. -/
namespace Maxwell.Defect
open InnerProductSpace Filter Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Rational target values and vectors are sufficient: any convergent
approximations eventually pass every strictly feasible residual and gap
budget around an actual isolated eigenpair. -/
theorem residual_quadratic_certificate_eventually
    (S : E →L[ℝ] E) (u : E) (μ γ g ε : ℝ)
    (T : ℕ → E →L[ℝ] E) (v : ℕ → E) (target : ℕ → ℝ)
    (hu : ‖u‖ = 1) (hSu : S u = μ • u) (hγ : 0 < γ)
    (hg : 0 ≤ g) (hgγ : g ≤ γ / 2) (hε : 0 < ε)
    (hgap : ∀ x : E, inner ℝ u x = 0 → γ * ‖x‖ ≤ ‖S x - μ • x‖)
    (hT : ∀ n, (T n).toLinearMap.IsSymmetric)
    (hv : ∀ᶠ n in atTop, ‖v n‖ = 1)
    (hTlim : Tendsto T atTop (𝓝 S)) (hvlim : Tendsto v atTop (𝓝 u))
    (hμlim : Tendsto target atTop (𝓝 μ)) :
    ∀ᶠ n in atTop, ‖v n‖ = 1 ∧ ‖T n (v n) - target n • v n‖ < ε ∧
      ∀ x : E, g ^ 2 * ‖x‖ ^ 2 ≤
        ‖residualReference (T n) (v n) (target n) x - target n • x‖ ^ 2 +
          2 * g ^ 2 * |inner ℝ (v n) x| ^ 2 := by
  have happ : Tendsto (fun n => T n (v n)) atTop (𝓝 (S u)) :=
    isBoundedBilinearMap_apply.continuous.tendsto _ |>.comp (hTlim.prodMk_nhds hvlim)
  have hres : Tendsto (fun n => ‖T n (v n) - target n • v n‖) atTop (𝓝 0) := by
    simpa only [hSu, sub_self, norm_zero] using (happ.sub (hμlim.smul hvlim)).norm
  have hop : Tendsto (fun n => ‖S - T n‖) atTop (𝓝 0) := by
    simpa using ((tendsto_const_nhds (x := S)).sub hTlim).norm
  have hdir : Tendsto (fun n => ‖u - v n‖) atTop (𝓝 0) := by
    simpa using ((tendsto_const_nhds (x := u)).sub hvlim).norm
  have htar : Tendsto (fun n => |μ - target n|) atTop (𝓝 0) := by
    simpa using ((tendsto_const_nhds (x := μ)).sub hμlim).abs
  have href : Tendsto
      (fun n => ‖S - T n‖ + 2 * ‖T n (v n) - target n • v n‖) atTop (𝓝 0) := by
    simpa using hop.add (hres.const_mul 2)
  have hevent := (hres.eventually_lt_const hε).and
    ((hdir.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 4)).and
      ((htar.eventually_lt_const (by positivity : 0 < γ / 8)).and
        (href.eventually_lt_const (by positivity : 0 < γ / 8))))
  filter_upwards [hv, hevent] with n hvn hn
  rcases hn with ⟨hresn, hdirn, htarn, hrefn⟩
  refine ⟨hvn, hresn, ?_⟩
  let A := residualReference (T n) (v n) (target n)
  have hSA : ‖S - A‖ ≤ γ / 8 := by
    calc
      _ ≤ ‖S - T n‖ + ‖T n - A‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ ‖S - T n‖ + 2 * ‖T n (v n) - target n • v n‖ :=
        add_le_add_right (residualReference_norm (T n) (hT n) (v n) (target n) hvn) _
      _ ≤ γ / 8 := hrefn.le
  have hgapn := complementary_gap_perturbation S A u (v n) μ (target n) γ
    (γ / 8) (γ / 8) (1 / 4) hu hSu hγ.le hgap hSA htarn.le hdirn.le
  apply quadratic_certificate_of_complementary_gap A (v n) (target n) g (γ / 2)
    hvn (residualReference_selected (T n) (v n) (target n) hvn) hg hgγ
  intro x hx
  have hh := hgapn x hx
  convert hh using 1
  ring

/-- An actual real scalar has a convergent sequence of rational proposals. -/
theorem exists_rational_target_sequence (μ : ℝ) :
    ∃ target : ℕ → ℚ, Tendsto (fun n => (target n : ℝ)) atTop (𝓝 μ) := by
  obtain ⟨f, hf, hlim⟩ := mem_closure_iff_seq_limit.mp (Rat.denseRange_cast μ)
  choose target htarget using hf
  refine ⟨target, ?_⟩
  convert hlim using 1
  funext n
  exact htarget n

/-- Rational coordinate vectors approximate every finite real vector. -/
theorem exists_rational_vector_sequence {ι : Type*} [Fintype ι]
    (u : EuclideanSpace ℝ ι) :
    ∃ v : ℕ → ι → ℚ,
      Tendsto (fun n => WithLp.toLp 2 (fun i => (v n i : ℝ))) atTop (𝓝 u) := by
  have hd : DenseRange (fun v : ι → ℚ => fun i => (v i : ℝ)) :=
    DenseRange.piMap (fun _ => Rat.denseRange_cast)
  obtain ⟨f, hf, hlim⟩ := mem_closure_iff_seq_limit.mp (hd (WithLp.ofLp u))
  choose v hv using hf
  refine ⟨v, ?_⟩
  have hh := (PiLp.continuous_toLp 2 (fun _ : ι => ℝ)).tendsto (WithLp.ofLp u) |>.comp hlim
  convert hh using 1
  funext n
  exact congrArg (WithLp.toLp 2) (hv n)

/-- Normalization of rational proposals preserves convergence to a unit
vector; proposals are eventually nonzero and therefore exactly unit length. -/
theorem exists_rational_unit_sequence {ι : Type*} [Fintype ι]
    (u : EuclideanSpace ℝ ι) (hu : ‖u‖ = 1) :
    ∃ v : ℕ → ι → ℚ,
      (∀ᶠ n in atTop, v n ≠ 0) ∧
      Tendsto (fun n => ‖WithLp.toLp 2 (fun i => (v n i : ℝ))‖⁻¹ •
        WithLp.toLp 2 (fun i => (v n i : ℝ))) atTop (𝓝 u) := by
  obtain ⟨v, hv⟩ := exists_rational_vector_sequence u
  have hn : Tendsto (fun n => ‖WithLp.toLp 2 (fun i => (v n i : ℝ))‖) atTop (𝓝 1) := by
    simpa only [hu] using hv.norm
  have hevent : ∀ᶠ n in atTop, v n ≠ 0 := by
    filter_upwards [hn.eventually_const_lt (by norm_num : (0 : ℝ) < 1)] with n hn
    intro hzero
    have hvzero : WithLp.toLp 2 (fun i => (v n i : ℝ)) =
        (0 : EuclideanSpace ℝ ι) := by ext i; simp [hzero]
    rw [hvzero, norm_zero] at hn
    exact (lt_irrefl 0) hn
  refine ⟨v, hevent, ?_⟩
  have hh := (hn.inv₀ (by norm_num : (1 : ℝ) ≠ 0)).smul hv
  simpa only [inv_one, one_smul] using hh

end Maxwell.Defect
