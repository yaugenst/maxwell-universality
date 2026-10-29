import Maxwell.Logical.Circuit

namespace Maxwell.Logical.Circuit

inductive CopyOnly {n : ℕ} : {d : ℕ} → Circuit n d → Prop where
  | input : CopyOnly (.input : Circuit n n)
  | copy {d : ℕ} {c : Circuit n d} (h : CopyOnly c) (parent : Fin d) :
      CopyOnly (c.copyGate parent)

/-- Every copy path uses each residual coordinate at most once. This
uniform bound charges the actual sum of all residual magnitudes. -/
theorem CopyOnly.evaluate_bound {n d : ℕ} {c : Circuit n d} (hc : c.CopyOnly)
    (input : Fin n → ℝ) (error : Fin d → ℝ) (X : ℝ)
    (hX : ∀ i, |input i| ≤ X) (i : Fin d) :
    |c.evaluate input error i| ≤ X + ∑ j, |error j| := by
  induction hc with
  | input =>
      change |input i + error i| ≤ _
      exact (abs_add_le _ _).trans (add_le_add (hX i)
        (Finset.single_le_sum (fun j _ => abs_nonneg (error j)) (Finset.mem_univ i)))
  | @copy d c hc parent ih =>
      have hs : ∑ j : Fin (d + 1), |error j| =
          (∑ j : Fin d, |error j.castSucc|) + |error (Fin.last d)| := by
        exact Fin.sum_univ_castSucc _
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [copyGate_last]
        exact (abs_add_le _ _).trans (by
          rw [hs, ← add_assoc]
          exact add_le_add (ih (fun j => error j.castSucc) parent) (le_refl _))
      · change |(c.append _).evaluate input error j.castSucc| ≤ _
        rw [evaluate_append_castSucc]
        have h := ih (fun k => error k.castSucc) j
        rw [hs]
        linarith [abs_nonneg (error (Fin.last d))]

theorem CopyOnly.unit_error_bound {n d : ℕ} {c : Circuit n d} (hc : c.CopyOnly)
    (i j : Fin d) : |c.evaluate 0 (Pi.single j 1) i| ≤ 1 := by
  have h := hc.evaluate_bound 0 (Pi.single j 1) 0 (by intro k; simp) i
  simpa only [Pi.single_apply, apply_ite abs, abs_one, abs_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, zero_add] using h

theorem CopyOnly.arbitrary_residual {n d : ℕ} {c : Circuit n d} (hc : c.CopyOnly)
    (input : Fin n → ℝ) (state : Fin d → ℝ) (i : Fin d) :
    |state i - c.evaluate input 0 i| ≤ ∑ j, |c.residual input state j| := by
  have hs := congrFun (c.residual_error_superposition input state) i
  have h := hc.evaluate_bound 0 (c.residual input state) 0 (by intro k; simp) i
  simp only [Pi.add_apply] at hs
  rw [hs]
  simpa only [add_sub_cancel_left, zero_add] using h

end Maxwell.Logical.Circuit
