import Maxwell.Cost.SelectedParameters.BufferPredicate
import Maxwell.Cost.SelectedParameters.BufferBounds

/-! Exact executable buffer selection. The fixed finite program starts at
zero, recomputes the integer stopping test, and returns its first successful
index on tape570. Termination and the cost bound use the proved logarithmic
witness only as mathematical evidence. -/
namespace Maxwell.Cost.SelectedParameters.Buffer
open Structured RationalAccumulator
set_option maxHeartbeats 1500000

def rate (d : Data) : ℚ := (d.a:ℚ)/d.b
def volume (d : Data) : ℚ := (d.e:ℚ)/d.f

structure Conditions (d : Data) (J g τ ζ : ℚ) : Prop where
  a_pos : 0 < d.a
  a_lt_b : d.a < d.b
  v_pos : 0 < d.v
  f_pos : 0 < d.f
  J_nonneg : 0 ≤ J
  g_pos : 0 < g
  τ_pos : 0 < τ
  τ_le_one : τ ≤ 1
  ζ_pos : 0 < ζ
  ζ_le_one : ζ ≤ 1
  coefficient : (d.u:ℚ)/d.v = 128*J/(g*τ*ζ^2)

theorem Conditions.b_pos {d : Data} {J g τ ζ : ℚ} (h : Conditions d J g τ ζ) : 0 < d.b :=
  h.a_pos.trans h.a_lt_b

theorem Conditions.rate_pos {d : Data} {J g τ ζ : ℚ} (h : Conditions d J g τ ζ) : 0 < rate d :=
  div_pos (by exact_mod_cast h.a_pos) (by exact_mod_cast h.b_pos)

theorem Conditions.rate_lt_one {d : Data} {J g τ ζ : ℚ} (h : Conditions d J g τ ζ) : rate d < 1 :=
  (div_lt_one (by exact_mod_cast h.b_pos)).mpr (by exact_mod_cast h.a_lt_b)

theorem Conditions.volume_nonneg {d : Data} {J g τ ζ : ℚ} (h : Conditions d J g τ ζ) : 0 ≤ volume d :=
  div_nonneg (Nat.cast_nonneg _) (by exact_mod_cast h.f_pos.le)

noncomputable def choice (d : Data) (J g τ ζ : ℚ) (h : Conditions d J g τ ζ) : ℕ :=
  Realization.Buffer.rationalChoice (rate d) J g (volume d) τ ζ d.m d.s
    h.rate_pos h.rate_lt_one h.J_nonneg h.g_pos h.volume_nonneg h.τ_pos h.τ_le_one h.ζ_pos h.ζ_le_one

theorem Conditions.exists_test {d : Data} {J g τ ζ : ℚ} (h : Conditions d J g τ ζ) : ∃ n, Test d n := by
  refine ⟨choice d J g τ ζ h,?_⟩
  apply (test_iff_rationalTest d J g τ ζ _ h.b_pos h.v_pos h.f_pos h.g_pos h.τ_pos h.ζ_pos h.coefficient).mpr
  exact Realization.Buffer.rationalChoice_spec (rate d) J g (volume d) τ ζ d.m d.s
    h.rate_pos h.rate_lt_one h.J_nonneg h.g_pos h.volume_nonneg h.τ_pos h.τ_le_one h.ζ_pos h.ζ_le_one

theorem find_eq_choice (d : Data) (J g τ ζ : ℚ) (h : Conditions d J g τ ζ) (hexists : ∃ n, Test d n) :
    Nat.find hexists = choice d J g τ ζ h := by
  unfold choice Realization.Buffer.rationalChoice
  apply Nat.find_congr'
  intro n
  exact test_iff_rationalTest d J g τ ζ n h.b_pos h.v_pos h.f_pos h.g_pos h.τ_pos h.ζ_pos h.coefficient

noncomputable def logarithmicBound (d : Data) (J g τ ζ : ℚ) : ℝ :=
  2+(2/(-Real.log (rate d:ℝ)))*
    (Real.log (Realization.Buffer.fixedConstant (-Real.log (rate d:ℝ)) J g (volume d))+
      2*Real.log ((d.m:ℝ)+1)+6*Real.log ((d.s:ℝ)+1)+Real.log (1/(τ:ℝ))+2*Real.log (1/(ζ:ℝ)))

theorem choice_logarithmic (d : Data) (J g τ ζ : ℚ) (h : Conditions d J g τ ζ) :
    (choice d J g τ ζ h:ℝ) ≤ logarithmicBound d J g τ ζ :=
  Realization.Buffer.rationalChoice_logarithmic_bound (rate d) J g (volume d) τ ζ d.m d.s
    h.rate_pos h.rate_lt_one h.J_nonneg h.g_pos h.volume_nonneg h.τ_pos h.τ_le_one h.ζ_pos h.ζ_le_one

/-- All variable geometric scales occur only in the logarithmic index bound;
the remaining width contribution is quadratic. -/
theorem costBound_logarithmic (d : Data) (J g τ ζ : ℚ) (h : Conditions d J g τ ζ) (B : ℕ) :
    (costBound (choice d J g τ ζ h) B:ℝ) ≤
      (3000*8^32+(3000*8^31+16002)*23^2 : ℝ)*
        (logarithmicBound d J g τ ζ+1)^3*((B:ℝ)+3)^2 := by
  have hp := costBound_polynomial (choice d J g τ ζ h) B
  have hc : (costBound (choice d J g τ ζ h) B:ℝ) ≤
      (3000*8^32+(3000*8^31+16002)*23^2 : ℝ)*
        ((choice d J g τ ζ h:ℝ)+1)^3*((B:ℝ)+3)^2 := by exact_mod_cast hp
  refine hc.trans ?_
  gcongr
  exact choice_logarithmic d J g τ ζ h

/-- Runtime input words determine the exact least buffer index. Every tape
outside the fixed workspace, including all eight inputs, is preserved. -/
theorem rational_executes (v : ℕ → ℕ) (B : ℕ) (hwidth : ∀ i ∈ ids, (v i).bits.length ≤ B)
    (J g τ ζ : ℚ) (h : Conditions (initialData v) J g τ ζ)
    (input : List Bool) (randomTape : ℕ → Bool) (s : Store)
    (hbank : NatAssign.Bank ids v s.val) (hscratch : NatAssign.Scratch s.val) :
    ∃ cost t, Executes input randomTape code cost s t ∧
      cost ≤ costBound (choice (initialData v) J g τ ζ h) B ∧
      Ready (initialData v) (choice (initialData v) J g τ ζ h) t ∧
      Word t.val 570 (choice (initialData v) J g τ ζ h) ∧ BinaryPrecision.Frame workspace s.val t.val := by
  obtain ⟨cost,t,he,hcost,ht,hf⟩ := executes v B hwidth h.exists_test input randomTape s hbank hscratch
  rw [find_eq_choice (initialData v) J g τ ζ h h.exists_test] at hcost ht
  refine ⟨cost,t,he,hcost,ht,?_,hf⟩
  simpa [values] using ht.bank 570 (by simp [ids,base])

end Maxwell.Cost.SelectedParameters.Buffer
